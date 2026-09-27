#!/usr/bin/env bash
# `Extensions/Purity`: build the library, then check every declaration's axioms.
# The forbidden-keyword scan of `Extensions/` is part of `scripts/check-hygiene.sh`.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build Purity
lake env lean --run scripts/CheckAxiomsPurity.lean
