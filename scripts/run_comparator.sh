#!/usr/bin/env bash
# Run leanprover/comparator against the Alpöge release with a Challenge file that WE control.
#
# UNTESTED in this repository (requires Linux x86-64, landrun, lean4export, ~100 GB RAM, ~200 GB disk,
# and many hours). Kept as a reproducible recipe. Usage: scripts/run_comparator.sh PATH/TO/release/lean
#
# Trust model (see comparator README, assumption 1): the Challenge's imports and the lakefile must be
# trusted. We therefore (a) refuse to run unless the release lakefile/manifest pin upstream Mathlib at
# the tag v4.33.1 commit, and (b) write our own Challenge.lean (copied from reference/Challenge.lean,
# which imports only Mathlib) instead of using any file shipped with the solution.
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
REL="$(cd "$1" && pwd)"

python3 - "$REL" <<'PY'
import json, sys
m = json.load(open(f"{sys.argv[1]}/lake-manifest.json"))
ml = [p for p in m["packages"] if p["name"] == "mathlib"][0]
assert ml["url"] == "https://github.com/leanprover-community/mathlib4", ml["url"]
assert ml["rev"] == "0df444a360eaa60ab8c11dca51a86af692955474", ml["rev"]
print("ok: release pins upstream Mathlib v4.33.1")
PY
grep -qx 'leanprover/lean4:v4.33.1' "$REL/lean-toolchain"

# Our Challenge (identical to the one used by the Lean FRO / Deicyde setup; imports only Mathlib).
cp "$HERE/reference/Challenge.lean" "$REL/src/Challenge.lean"
cp "$HERE/reference/comparator.json" "$REL/comparator.json"
if ! grep -q 'name = "Challenge"' "$REL/lakefile.toml"; then
  printf '\n[[lean_lib]]\nname = "Challenge"\nroots = ["Challenge"]\n' >> "$REL/lakefile.toml"
fi

# Tools: comparator standalone (Lean < v4.35 has no `lake comparator`), lean4export, landrun, nanoda.
: "${COMPARATOR:?set COMPARATOR to the comparator binary built for Lean v4.33.x}"
: "${COMPARATOR_LEAN4EXPORT:?set to lean4export compatible with v4.33.1}"
: "${COMPARATOR_LANDRUN:?set to landrun (main)}"

cd "$REL"
lake exe cache get   # trusted Mathlib cache (see README for the from-source alternative)
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" \
  -E COMPARATOR_LEAN4EXPORT -E COMPARATOR_LANDRUN --working-directory "$REL" -- \
  bash -c "lake env '$COMPARATOR' comparator.json" | tee comparator.log
grep -q "Your solution is okay" comparator.log
