#!/usr/bin/env bash
# Regenerate comparator/Challenge/**, the verbatim copy of the declarations the
# statement of BoCa.Fig16.LogRel.Typed.adequacy reaches (comparator/README.md).
# Needs `lake build Paper` first; reads only this repository.
#
#   tools/challenge/run.sh [output dir]     # default: comparator
set -euo pipefail
cd "$(dirname "$0")/../.."
out="${1:-comparator}"
closure="$(mktemp)"
trap 'rm -f "$closure"' EXIT
lake env lean --run tools/challenge/Closure.lean > "$closure"
rm -rf "$out/Challenge"
python3 tools/challenge/extract.py . "$closure" "$out"
