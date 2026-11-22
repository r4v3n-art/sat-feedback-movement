#!/usr/bin/env bash
# Run from any directory. The exported declarations are the exact audit list in Main.
set -euo pipefail
cd "$(dirname "$0")/.."
tmp=$(mktemp -d)
trap 'rm -f "$tmp/proofs.ndjson" "$tmp/axioms.log"; rmdir "$tmp"' EXIT
lake build
lake env lean SatWalk/Main.lean | tee "$tmp/axioms.log"
names=()
while read -r name; do names+=("$name"); done < <(sed -n 's/^#print axioms //p' SatWalk/Main.lean)
python3 - "$tmp/axioms.log" "${names[@]}" <<'PY'
import re
import sys
from pathlib import Path

log = Path(sys.argv[1]).read_text()
names = set(sys.argv[2:])
headlines = {"SatWalk.theorem_" + suffix for suffix in (
    "upper_bound", "lower_bound", "memoryless_separation")}
allowed = {"propext", "Classical.choice", "Quot.sound"}
if not headlines <= names:
    sys.exit("Incomplete headline audit list")
for name in sorted(names):
    match = re.search(r"'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", log)
    if match is None:
        sys.exit(f"Missing axiom report for {name}")
    extra = set(match[1].split(", ")) - allowed
    if extra:
        sys.exit(f"Unexpected axioms for {name}: {sorted(extra)}")
PY
if [[ ${1:-} == --axioms-only ]]; then
  exit 0
fi
lake env leanexport SatWalk.Main -- "${names[@]}" > "$tmp/proofs.ndjson"
options=(--paranoid "--from-export=$tmp/proofs.ndjson")
if [[ $(uname -s) == Darwin ]]; then
  options+=(--inadvisably-no-sandbox)
fi
lake check "${options[@]}"
