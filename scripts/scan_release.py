#!/usr/bin/env python3
"""Static red-flag scan of the Alpöge release source tree (read-only; never builds it).

Usage: python3 -I scripts/scan_release.py PATH/TO/release/lean

If PATH is inside a git checkout, sources are read from the git object store at HEAD
(`git cat-file --batch`), which is fast and immune to working-tree edits / CRLF conversion;
otherwise the file system is walked.

HARD flags (exit 1):
  * a declaration whose name is *exactly* a constant of the statement, at root or with `_root_.`
    (RiemannHypothesis, riemannZeta, HurwitzZeta.hurwitzZetaEven, HurwitzZeta.completedHurwitzZetaEven,
    Gammaℝ, DirichletCharacter.LFunction), or any declaration inside `namespace DirichletCharacter` /
    `namespace HurwitzZeta` named like one of them;
  * `debug.skipKernelTC` / `debug.skipKernelTypeCheck`;
  * `axiom` declarations (the release is supposed to use none);
  * `export` of a statement constant;
  * Statements.lean / Challenge.lean importing anything other than `Mathlib`;
  * lakefile requiring a non-upstream git source.
SOFT flags (reported): declarations in *other* namespaces whose last component equals a statement
  constant (e.g. `Foo.LFunction`), `export` (other), `unsafe`, `implemented_by`, `extern`,
  `run_cmd`/`run_elab`/`run_meta`, `elab`/`macro_rules`.
Heuristic only: the authoritative check is comparator / con-leche's transitive comparison.
"""
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path

CONSTS = ["RiemannHypothesis", "riemannZeta", "hurwitzZetaEven", "completedHurwitzZetaEven",
          "Gammaℝ", "LFunction"]
EXACT = {"RiemannHypothesis", "riemannZeta", "HurwitzZeta.hurwitzZetaEven",
         "HurwitzZeta.completedHurwitzZetaEven", "Gammaℝ", "DirichletCharacter.LFunction"}
END = r"(?=[\s:({\[]|$)"   # explicit end-of-name (\b misbehaves after ℝ)
DECL = re.compile(
    r"^[ \t]*(?:@\[[^\]\n]*\][ \t\n]*)*(?:(?:private|protected|noncomputable|unsafe|partial|nonrec)\s+)*"
    r"(?:def|abbrev|theorem|lemma|opaque|axiom|instance|structure|class|inductive)\s+"
    r"(_root_\.)?((?:[\w'ℝ]+\.)*(" + "|".join(map(re.escape, CONSTS)) + r"))" + END, re.M)
NAMESPACE = re.compile(r"^\s*namespace\s+(\S+)", re.M)
SKIPKERNEL = re.compile(r"debug\.skipKernelT(?:C|ypeCheck)")
AXIOM = re.compile(r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*(?:(?:private|protected)\s+)?axiom\s+(\S+)", re.M)
EXPORT = re.compile(r"^[ \t]*export\s+(.*)$", re.M)
SOFT = {
    "unsafe": re.compile(r"(?<![\w.])unsafe(?![\w'])"),
    "implemented_by": re.compile(r"implemented_by"),
    "extern": re.compile(r"@\[extern"),
    "run_cmd/run_elab": re.compile(r"^\s*(?:run_cmd|run_elab|run_meta)\b", re.M),
    "elab/macro_rules": re.compile(r"^\s*(?:elab|macro_rules|elab_rules)\b", re.M),
}


def iter_sources(root: Path):
    """Yield (relative path, text) for every .lean file under root/src."""
    top = subprocess.run(["git", "-C", str(root), "rev-parse", "--show-toplevel"],
                         capture_output=True, text=True)
    if top.returncode == 0:
        prefix = subprocess.run(["git", "-C", str(root), "rev-parse", "--show-prefix"],
                                capture_output=True, text=True).stdout.strip()
        ls = subprocess.run(["git", "-C", str(root), "ls-tree", "-r", "-z", "--full-name", "HEAD",
                             "src"], capture_output=True, check=True).stdout
        entries = []
        for rec in ls.split(b"\0"):
            if not rec:
                continue
            meta, path = rec.split(b"\t", 1)
            _, typ, sha = meta.split()
            p = path.decode("utf-8")
            if typ == b"blob" and p.endswith(".lean"):
                entries.append((p[len(prefix):], sha))
        print(f"source: git object store at HEAD of {top.stdout.strip()}")
        proc = subprocess.Popen(["git", "-C", str(root), "cat-file", "--batch"],
                                stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        import threading

        def feed():
            for _, sha in entries:
                proc.stdin.write(sha + b"\n")
            proc.stdin.close()
        threading.Thread(target=feed, daemon=True).start()
        for rel, _ in entries:
            header = proc.stdout.readline().split()
            size = int(header[2])
            data = proc.stdout.read(size)
            proc.stdout.read(1)
            yield rel, data.decode("utf-8", errors="replace")
        proc.wait()
    else:
        print("source: file system walk")
        for f in sorted((root / "src").rglob("*.lean")):
            yield str(f.relative_to(root)).replace("\\", "/"), f.read_text(encoding="utf-8", errors="replace")


def namespace_at(text: str, pos: int) -> str:
    """Crude: the last `namespace X` opened before pos (ignores `end`); good enough for flagging."""
    ns = [m.group(1) for m in NAMESPACE.finditer(text, 0, pos)]
    return ns[-1] if ns else ""


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__)
        return 2
    root = Path(sys.argv[1]).resolve()
    hard, soft, soft_ex = [], Counter(), defaultdict(list)
    n = 0
    for rel, t in iter_sources(root):
        n += 1
        for m in DECL.finditer(t):
            name, last = m.group(2), m.group(3)
            ns = namespace_at(t, m.start())
            full = name if m.group(1) else (f"{ns}.{name}" if ns else name)
            if m.group(1) or full in EXACT or name in EXACT or ns.split(".")[0] in ("DirichletCharacter", "HurwitzZeta"):
                hard.append(f"declaration `{full}` in {rel}")
            else:
                soft["homonym (other namespace)"] += 1
                soft_ex["homonym (other namespace)"].append(f"{full} @ {rel}")
        if SKIPKERNEL.search(t):
            hard.append(f"kernel type-check skipping option in {rel}")
        for m in AXIOM.finditer(t):
            hard.append(f"axiom `{m.group(1)}` in {rel}")
        for m in EXPORT.finditer(t):
            if any(c in m.group(1) for c in CONSTS):
                hard.append(f"export of a statement constant in {rel}: {m.group(0).strip()}")
            else:
                soft["export (other)"] += 1
                soft_ex["export (other)"].append(rel)
        for k, rx in SOFT.items():
            c = len(rx.findall(t))
            if c:
                soft[k] += c
                soft_ex[k].append(rel)
        if rel in ("src/Statements.lean", "src/Challenge.lean"):
            imports = re.findall(r"^import\s+(\S+)", t, re.M)
            if imports != ["Mathlib"]:
                hard.append(f"{rel} imports {imports} (expected only Mathlib)")
            else:
                print(f"ok    {rel} imports only Mathlib")
    print(f"scanned {n} .lean files")

    lf = root / "lakefile.toml"
    if lf.exists():
        gits = re.findall(r'git\s*=\s*"([^"]+)"', lf.read_text(encoding="utf-8"))
        bad = [g for g in gits if g.rstrip("/").removesuffix(".git")
               != "https://github.com/leanprover-community/mathlib4"]
        if bad:
            hard.append(f"lakefile requires non-upstream git sources: {bad}")
        else:
            print(f"ok    lakefile git requirements: {gits}")

    print("\nSOFT flags (informational):")
    for k in ["homonym (other namespace)", "export (other)", *SOFT]:
        ex = soft_ex.get(k, [])
        print(f"  {k:26s} {soft[k]:5d}" + (f"   e.g. {ex[:3]}" if ex else ""))
    print("\nHARD flags:")
    for h in hard:
        print("  FAIL ", h)
    if not hard:
        print("  none")
    print("\nRESULT:", "PASS" if not hard else f"FAIL ({len(hard)})")
    return 0 if not hard else 1


if __name__ == "__main__":
    sys.exit(main())
