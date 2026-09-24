#!/usr/bin/env bash
# No `sorry`, `axiom`, `native_decide`, `implemented_by`, `opaque`, `partial`,
# `unsafe` in the library, outside comments; then every declaration's axioms.
# `comparator/` is scanned too, with one permitted exception: the single `sorry`
# that is the body of the challenge statement in `comparator/Challenge.lean`
# (comparator's convention; comparator/README.md).  Needs nothing outside this
# repository, so CI runs it.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 - <<'PY'
import re, pathlib, sys
BAD = re.compile(r"\b(sorry|axiom|native_decide|implemented_by|opaque|partial|unsafe)\b")
hits = 0
CHALLENGE = pathlib.Path("comparator/Challenge.lean")
challenge_sorries = 0
files = sorted(pathlib.Path(".").glob("[PS]*/**/*.lean")) + [pathlib.Path("Paper.lean"), pathlib.Path("Support.lean")]
files += sorted(pathlib.Path("comparator").glob("**/*.lean"))
for p in files:
    src = p.read_text(encoding="utf-8")
    # strip comments: nested block comments and line comments
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i): depth += 1; i += 2; continue
        if depth and src.startswith("-/", i): depth -= 1; i += 2; continue
        if not depth and src.startswith("--", i):
            j = src.find("\n", i); i = len(src) if j < 0 else j; continue
        if not depth: out.append(src[i])
        i += 1
    code = "".join(out)
    for m in BAD.finditer(code):
        if p == CHALLENGE and m.group(0) == "sorry":
            challenge_sorries += 1; continue
        line = code[:m.start()].count("\n") + 1
        print(f"{p}:{line}: {m.group(0)}"); hits += 1
if challenge_sorries != 1:
    print(f"{CHALLENGE}: expected exactly one `sorry` (the challenge statement), found {challenge_sorries}")
    hits += 1
print(f"{hits} forbidden keyword(s) outside comments.")
sys.exit(1 if hits else 0)
PY
lake env lean --run scripts/CheckAxioms.lean
