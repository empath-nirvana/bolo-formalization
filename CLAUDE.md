# Standing instructions

This repository mechanises Wagner, Gierczak, Marshall, Li & Ahmed, *From Linearity
to Borrowing* (PACMPL 9:OOPSLA2:415, 2025), laid out as the paper is. `[CONF]` is
`3764117.pdf`; `[TR]` is `3764117-supplement.pdf`, which holds the complete
definitions and proofs. Both are in the source repository, `borrow_lang`.

The Lean here is moved from `borrow_lang` (branch `mathlib-natdual`, commit
`970a9d0`), not re-proved. The task is to transcribe what is printed. It is not to
find a proof of the same theorem.

## Layout

- `Paper/` — the paper, section by section, in `[TR]`'s order: `S1_Syntax` …
  `S5_Model` (`Definitions.lean`), `S6_1_StandardLemmas` … `S6_8_FundamentalProperty`
  (`Lemmas.lean`; §6.2 also has `Definitions.lean` for Definitions 6.1–6.3),
  `Remarks.lean` files for the theorem-valued rows of §§4–5, and `CONF/` for
  `[CONF]`'s own numbered results. Each item carries its printed form, page, tag
  (`[as printed]`, `[encoding]`, `[repair]`, `[about ours]`) and adjudication.
- `Support/` — what the paper never prints, by topic (`Syntax/`, `Lifetimes/`,
  `Statics/`, `Dynamics/`, `Model/`, `LogicalRelation/`, `TypedWorld/`). Every file
  there is `[about ours]`.
- `Paper/LiteralReadings/` — measurements of printed definitions read literally,
  where the library uses a repaired reading. Nothing else depends on them.
- `Bridge/` — the correspondence with the source at `970a9d0`: `Names.csv` maps each
  declaration here to its source declaration; `Plan.csv` places every declaration
  of the dependency closure.
- `tools/extract/` — the generator. `tools/extract/run.sh` regenerates every Lean
  file from the source and builds. **The Lean files are its output: change the
  generator (`cfg.json`, `banners.py`, the per-result text files), not the Lean.**
- `PLAN.md` — the stages, the placement decisions and why.

Citations of `docs/…` and `BoCa/…` in comments are to `borrow_lang` at `970a9d0`;
its row numbers are those of its `docs/paper-inventory.md` and
`docs/definition-inventory.md`. `borrow_lang` is read-only from here: nothing is
built, edited or written inside it.

## 1. Follow the printed proof. Never take a shorter route.

**A printed proof is not stand-alone.** It is where a technique gets built, and
later proofs reach for that technique. Proving a lemma some easier way leaves the
technique unbuilt, and the next lemma that needs it has nothing to reach for.

If a shorter route exists, that is not a reason to take it. Follow the page,
step by step, and build what each step names — even when the lemma would close
without it.

If you do take a shorter route, you must (a) say so in the docstring, and (b)
record which printed technique was therefore **not** built. `[as printed]` scores
the *statement*; it says nothing about the proof, and a row can read `[as printed]`
while the technique its proof should have left behind is missing.

## 2. The paper is not wrong.

Never report that a printed lemma is false, unsound, un-derivable, or a gap —
not in prose, a declaration name, a docstring, or a commit message. "X cannot be
derived" and "X is un-derivable" are the same claim through a negative. Say
"cannot reconcile", name the exact printed step, and go looking for our mistake.

Novelty is not evidence: "this blocker is a different shape" says nothing about
its cause.

## 3. Before inventing a route, check the objects are transcribed.

When a printed step will not follow, the first question is whether we have
transcribed everything that step names. Reconstruction is invention.

`[TR]` numbers Definitions and Lemmas in **two sequences** — "6.2" is both Lemma
6.2 and Definition 6.2. A row present for a number is not evidence the object is
present. Check the definition inventory as well as the paper inventory.

## 4. Add hypotheses; never edit printed statements or definitions.

If a printed proof uses a fact its statement does not carry, add that fact as a
named hypothesis, quote the sentence it comes from, and leave the conclusion
exactly as printed. Prove any added hypothesis non-vacuous and pin its scope.
Never a hypothesis that assumes the lemma.

## 5. A blocker is a claim, and gets checked like one.

Everything proved here is machine-checked. A claim that *stops* work needs more
evidence than a lemma, not none. Report an obstruction only as a named
`def … : Prop` that elaborates, or a configuration built in Lean with every
hypothesis discharged. Otherwise say "I have not derived X and have not verified
that any obstruction is real", and keep going.

Every report lists: unspent printed hypotheses; unused uniqueness/functionality
results; and **which printed lemmas in the run-up are untranscribed**.

## 6. Do not split cases the paper does not split.

A printed case split is part of the proof. A split we introduce is an
invention, and every case it opens is an obligation the paper never incurs.
When a case analysis is not on the page, the question is not "how do I discharge
this case" but "why am I in it".

The same goes for enumerating cell kinds, operator clauses or walk shapes to see
which combinations survive. That is searching, not transcribing. If the printed
step is one sentence and the mechanisation is a case tree, the case tree is
probably ours.

## 7. Hygiene

- No `axiom`, `sorry`, `native_decide`, `implemented_by`, `opaque`, `partial`,
  `unsafe`.
- Every result `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]`.
- Every step ends with `lake build` clean, `scripts/check-bridge.sh` reporting 0
  mismatches (each declaration elaborates to its source's type, and for a
  definition its value), and `scripts/check-hygiene.sh` passing (the keyword scan
  and the axiom check over every constant).
- A declaration keeps its source name; a new name is an alias (`TR.lemma_6_N`)
  and `Bridge/Names.csv` records what it aliases.
- Comments explain code, not history: no counts, no changelog, no puffery.
