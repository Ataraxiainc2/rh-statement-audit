#!/usr/bin/env python3
"""Check that this project is pinned to exactly the environment of the Alpöge release and that
the Mathlib checkout is upstream and untouched.

Checks
  1. lean-toolchain == leanprover/lean4:v4.33.1
  2. lake-manifest.json: every package (name, url, rev) identical to the release manifest
     (reference/alpoge-lake-manifest.json, SHA-256 checked against the release archive).
  3. Mathlib URL is the upstream leanprover-community/mathlib4 (no fork).
  4. reference/*.lean and the release manifest have the SHA-256 recorded in the release
     archive's per-file manifest (tamnd/riemann-lean manifests/files.sha256).
  5. If .lake/packages/mathlib exists: HEAD == pinned rev and `git status --porcelain` is empty
     (no local edits to Mathlib sources), and the source text of `RiemannHypothesis` is the
     expected one.
  6. --online: the pinned Mathlib commit is the upstream tag `v4.33.1`, and relative to upstream
     `master` it adds only a toolchain bump (only `lean-toolchain` changes). NOTE: it is *not* an
     ancestor of master (GitHub reports `diverged`); that is normal for Mathlib's version tags.
"""
import hashlib
import json
import os
import subprocess
import sys
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TOOLCHAIN = "leanprover/lean4:v4.33.1"
MATHLIB_URL = "https://github.com/leanprover-community/mathlib4"
MATHLIB_REV = "0df444a360eaa60ab8c11dca51a86af692955474"

# SHA-256 values from the release archive (alpo.ge lean.tar.gz, 2026-11-20), as listed in
# https://github.com/tamnd/riemann-lean/blob/main/manifests/files.sha256
RELEASE_SHA256 = {
    "reference/alpoge-lake-manifest.json": "fee57ee9ed399d0a638ca955e5ad40a37a36eeb9b6dfd9f5964114fa7bbe4774",
    "reference/Statements.lean": "79ef7ca776e42abe1f46caee13ea09bd19f1e2d0b1620d8d5d200258f33b47bf",
    "reference/Main.lean": "017645ca448f2fd1f6fd5c4c2cb2c6e96e472725be13f6e180ca6e1574360939",
}

EXPECTED_RH_DEF = (
    "def RiemannHypothesis : Prop :=\n"
    "  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2"
)

MATHLIB_TAG = "v4.33.1"

failures = []


def gh_api(path: str) -> dict:
    url = f"https://api.github.com/repos/leanprover-community/mathlib4/{path}"
    req = urllib.request.Request(url, headers={"Accept": "application/vnd.github+json",
                                               "User-Agent": "rh-statement-audit"})
    tok = os.environ.get("GITHUB_TOKEN")
    if tok:
        req.add_header("Authorization", f"Bearer {tok}")
    with urllib.request.urlopen(req, timeout=60) as r:
        return json.load(r)


def check(cond: bool, msg: str) -> None:
    print(("ok    " if cond else "FAIL  ") + msg)
    if not cond:
        failures.append(msg)


def sha256(p: Path) -> str:
    # normalise CRLF so that a Windows checkout gives the same hash as the release archive
    return hashlib.sha256(p.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def pkgs(manifest: dict) -> dict:
    return {p["name"]: (p.get("url"), p.get("rev")) for p in manifest["packages"]}


def main() -> int:
    online = "--online" in sys.argv

    tc = (ROOT / "lean-toolchain").read_text().strip()
    check(tc == TOOLCHAIN, f"lean-toolchain = {tc!r} (expected {TOOLCHAIN!r})")

    for rel, h in RELEASE_SHA256.items():
        got = sha256(ROOT / rel)
        check(got == h, f"sha256({rel}) = {got[:16]}… matches release archive")

    ours = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    ref = json.loads((ROOT / "reference/alpoge-lake-manifest.json").read_text(encoding="utf-8"))
    po, pr = pkgs(ours), pkgs(ref)
    check(set(po) == set(pr), f"same package set as release: {sorted(po)}")
    for name in sorted(set(po) & set(pr)):
        check(po[name] == pr[name], f"package {name}: {po[name][1][:12]} == release")
    check(po.get("mathlib") == (MATHLIB_URL, MATHLIB_REV),
          f"mathlib = upstream {MATHLIB_URL} @ {MATHLIB_REV[:12]}")

    ml = ROOT / ".lake" / "packages" / "mathlib"
    if ml.exists():
        head = subprocess.run(["git", "-C", str(ml), "rev-parse", "HEAD"],
                              capture_output=True, text=True).stdout.strip()
        check(head == MATHLIB_REV, f".lake/packages/mathlib HEAD = {head[:12]}")
        dirty = subprocess.run(["git", "-C", str(ml), "status", "--porcelain", "--untracked-files=no"],
                               capture_output=True, text=True).stdout.strip()
        check(dirty == "", "no local modifications in .lake/packages/mathlib")
        src = (ml / "Mathlib/NumberTheory/LSeries/RiemannZeta.lean").read_text(encoding="utf-8")
        check(EXPECTED_RH_DEF in src.replace("\r\n", "\n"),
              "Mathlib source of `RiemannHypothesis` is the expected text")
    else:
        print("skip  .lake/packages/mathlib not present (run `lake exe cache get` first)")

    if online:
        # The pinned commit is Mathlib's official tag `v4.33.1`: one "bump toolchain" commit on
        # top of a master commit. So we check: (a) the upstream tag `v4.33.1` points at it, and
        # (b) relative to upstream master it adds only commits that touch `lean-toolchain`.
        try:
            ref = gh_api(f"git/ref/tags/{MATHLIB_TAG}")
            obj = ref["object"]
            if obj["type"] == "tag":  # annotated tag: dereference
                obj = gh_api(f"git/tags/{obj['sha']}")["object"]
            check(obj["sha"] == MATHLIB_REV,
                  f"upstream tag {MATHLIB_TAG} points at the pinned commit")
            cmp = gh_api(f"compare/master...{MATHLIB_REV}")
            files = sorted({f["filename"] for f in cmp.get("files", [])})
            check(cmp["status"] in ("behind", "identical")
                  or (cmp["status"] == "diverged" and files == ["lean-toolchain"]),
                  f"vs upstream master: status={cmp['status']}, ahead_by={cmp['ahead_by']}, "
                  f"files changed off-master={files} (only lean-toolchain allowed)")
            print(f"      merge-base with master: {cmp['merge_base_commit']['sha']}")
        except Exception as e:  # noqa: BLE001
            check(False, f"GitHub API failed: {e}")

    print("\nRESULT:", "PASS" if not failures else f"FAIL ({len(failures)} failures)")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
