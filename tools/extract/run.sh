#!/usr/bin/env bash
# Regenerate Paper/ and Support/ from the source repository, then build.
#
#   BORROW_LANG_SRC=/path/to/borrow_lang tools/extract/run.sh [--dump]
#
# --dump re-reads the source environment (needs `lake build BoCa` there; nothing
# is written inside it).  Everything the scripts produce besides Paper/, Support/,
# Bridge/ and the two root files stays in this directory and is not committed.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
export BORROW_LANG_SRC="${BORROW_LANG_SRC:-$(cd "$ROOT/.." && pwd)/borrow_lang}"
cd "$HERE"
if [[ "${1:-}" == "--dump" || ! -f dump.tsv ]]; then
  (cd "$BORROW_LANG_SRC" && EXTRACT_DUMP="$HERE/dump.tsv" lake env lean "$HERE/Dump.lean")
fi
python3 roots.py > /dev/null
python3 closure.py > /dev/null
rm -rf "$ROOT/Paper" "$ROOT/Support"
python3 stage2.py | grep -E "PROB|CLASH|^files|^bridge|^index" || true
python3 plan.py > plan.out
python3 skeleton.py > /dev/null
cd "$ROOT"
(for f in $(find Paper -name "*.lean" | sort); do echo "import $(echo "${f%.lean}" | tr / .)"; done) > Paper.lean
(for f in $(find Support -name "*.lean" | sort); do echo "import $(echo "${f%.lean}" | tr / .)"; done) > Support.lean
lake build
