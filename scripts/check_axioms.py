#!/usr/bin/env python3
"""Run `#print axioms` on every anchor and fail unless each one uses only the standard axioms.

Usage:  python3 scripts/check_axioms.py            (runs `lake env lean RhStatementAudit/Axioms.lean`)
        python3 scripts/check_axioms.py LOGFILE    (parses a saved output instead)
"""
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
AXIOMS_FILE = ROOT / "RhStatementAudit" / "Axioms.lean"
PERMITTED = {"propext", "Classical.choice", "Quot.sound"}


def main() -> int:
    if len(sys.argv) > 1:
        out = Path(sys.argv[1]).read_text(encoding="utf-8", errors="replace")
    else:
        proc = subprocess.run(
            ["lake", "env", "lean", str(AXIOMS_FILE.relative_to(ROOT))],
            cwd=ROOT, capture_output=True, text=True, encoding="utf-8", errors="replace",
        )
        out = proc.stdout + proc.stderr
        if proc.returncode != 0:
            print(out)
            print(f"FAIL: lean exited with code {proc.returncode}")
            return 1

    expected = [
        m.group(1)
        for m in re.finditer(r"^#print axioms (\S+)", AXIOMS_FILE.read_text(encoding="utf-8"), re.M)
    ]
    seen = {}
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out):
        seen[m.group(1)] = {a.strip() for a in m.group(2).split(",") if a.strip()}
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", out):
        seen[m.group(1)] = set()

    ok = True
    for name in expected:
        full = next((k for k in seen if k == name or k.endswith("." + name)), None)
        if full is None:
            print(f"FAIL  {name}: no `#print axioms` output found")
            ok = False
            continue
        extra = seen[full] - PERMITTED
        status = "ok  " if not extra else "FAIL"
        print(f"{status}  {full}: {sorted(seen[full])}")
        if extra:
            ok = False
    if "sorry" in out.lower() and "sorryAx" in out:
        print("FAIL: sorryAx detected")
        ok = False
    print(f"\n{len(expected)} declarations checked; permitted axioms = {sorted(PERMITTED)}")
    print("RESULT:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
