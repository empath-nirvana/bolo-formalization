#!/usr/bin/env python3
"""Check every declaration of this repository against its source.

`Bridge/Names.csv` pairs each declaration here with the source declaration it
was moved from.  Given the two dumps `scripts/DumpDecls.lean` writes (one of
this repository, one of the source), this checks, for every constant defined
in `Paper.*` or `Support.*`:

  * that it has a source counterpart under the mapped name;
  * that the two have the same kind and the same type, and for a definition the
    same value, as raw expressions, once the module-specific prefix of private
    names (`_private.<Module>.0.`) is erased on both sides.

Usage:  check-bridge.py NEW.tsv OLD.tsv   (exit 1 on any mismatch)
"""
import csv, re, sys, pathlib, hashlib
PRIV = re.compile(r"_private\.[\w.]+?\.\d+\.")
# A hygienic binder name records the module and a counter; binder names do not
# affect what an expression means, so each is erased to `_h`.
HYG = re.compile(r"[^\s(){}\[\]:,]*_@\.[^\s(){}\[\]:,]*_hyg\.\d+")
def norm(s): return HYG.sub("_h", PRIV.sub("", s))
# Auxiliary declarations Lean generates (matchers, structural-recursion
# functionals, abstracted proofs, notation macros) are named by position or by
# module, and Lean shares one matcher between declarations with the same match
# shape.  They are not compared by name: a reference to one (with or without a
# universe instantiation `.{u}`) is replaced by a digest of its own type, which is
# what identifies it.
AUXREF = re.compile(r"[^\s(){}\[\]:,]+\.(?:match_\d+|_sparseCasesOn_\d+|proof_\d+|_proof_\d+)(?![\w])(?!\.[^{])")
AUXDECL = re.compile(r"(\.(match_\d+(_\d+)?|_sparseCasesOn_\d+|proof_\d+|_proof_\d+|_f|_sunfold|_unsafe_rec|splitter|eq_\d+|eq_def|below|brecOn|binductionOn)$)|_aux_|^_h$")
def load(p):
    raw = {}
    for line in open(p, encoding="utf-8"):
        n, k, t, v = line.rstrip("\n").split("\t", 3)
        raw[norm(n)] = (k, norm(t), norm(v))
    dig = {n: "AUX#" + hashlib.sha1(t.encode()).hexdigest()[:12]
           for n, (k, t, v) in raw.items() if AUXREF.fullmatch(n)}
    sub = lambda s: AUXREF.sub(lambda m: dig.get(m.group(0), m.group(0)), s)
    return {n: (k, sub(t), sub(v)) for n, (k, t, v) in raw.items() if not AUXDECL.search(n)}
new, old = load(sys.argv[1]), load(sys.argv[2])
root = pathlib.Path(__file__).resolve().parent.parent
rename = {}
with open(root / "Bridge" / "Names.csv", encoding="utf-8") as f:
    for row in csv.DictReader(f):
        rename[norm(row["name"])] = norm(row["source_name"])
bad = 0; checked = 0
for n, (k, t, v) in sorted(new.items()):
    src = rename.get(n, n)
    if src not in old:
        print("NO SOURCE      ", n); bad += 1; continue
    ok, ot, ov = old[src]
    checked += 1
    if k != ok: print("KIND DIFFERS   ", n, k, ok); bad += 1
    elif t != ot: print("TYPE DIFFERS   ", n); bad += 1
    elif k == "def" and v != ov: print("VALUE DIFFERS  ", n); bad += 1
print(f"{checked} declarations compared with their source; {bad} mismatches.")
sys.exit(1 if bad else 0)
