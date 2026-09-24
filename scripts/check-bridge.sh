#!/usr/bin/env bash
# Every declaration here against its source.  Dumps both environments with
# scripts/DumpDecls.lean and compares them with scripts/check-bridge.py.
#
#   BORROW_LANG_SRC=/path/to/borrow_lang ./scripts/check-bridge.sh
#
# The source repository must be built (`lake build BoCa` there); nothing is
# written inside it.
set -euo pipefail
cd "$(dirname "$0")/.."
SRC="${BORROW_LANG_SRC:-$(cd .. && pwd)/borrow_lang}"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
BRIDGE_IMPORTS=Paper,Support BRIDGE_PREFIXES=Paper,Support BRIDGE_OUT="$TMP/new.tsv" \
  lake env lean --run scripts/DumpDecls.lean
(cd "$SRC" && BRIDGE_IMPORTS=BoCa BRIDGE_PREFIXES=BoCa. BRIDGE_OUT="$TMP/old.tsv" \
  lake env lean --run "$OLDPWD/scripts/DumpDecls.lean")
python3 scripts/check-bridge.py "$TMP/new.tsv" "$TMP/old.tsv"
