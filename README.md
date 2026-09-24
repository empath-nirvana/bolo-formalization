# From Linearity to Borrowing — the mechanisation, laid out as the paper is

This repository is a Lean 4 mechanisation of Wagner, Gierczak, Marshall, Li and
Ahmed, *From Linearity to Borrowing* (PACMPL 9:OOPSLA2:415, 2025).  `[CONF]` is the
conference paper and `[TR]` its supplement, which prints the complete definitions
and proofs.  The files follow `[TR]` section by section: each printed definition
and each numbered result sits in the file for its section, in printed order as far
as Lean's definition-before-use allows, under a comment that quotes what is
printed.

The Lean is moved, not re-proved, from the source repository `borrow_lang` (branch
`mathlib-natdual`, commit `970a9d0`): every declaration keeps its name, statement
and proof, and `scripts/check-bridge.sh` checks that each one elaborates to the same
type (and, for a definition, the same value) as its source.  New names are aliases
only.

## Headline results

* **`[TR]` Lemma 6.151 / `[CONF]` Lemma 3.1, the Fundamental Property** —
  `Fig16.LogRel.Typed.fundamentalProperty` (aliases `TR.lemma_6_151`,
  `TR.«Fundamental Property»`, `CONF.lemma_3_1`), in
  `Paper/S6_8_FundamentalProperty/Lemmas.lean`: if `Δ; Γ ⊢ e : T` as `[TR]` p. 2
  reads it (`DerivesWf`, under the presuppositions `⊨ Δ` and `Δ ⊢ Γ` that p. 2 boxes)
  then `Δ; Γ ⊨ e : T` at the repaired judgment `SemX`, with no other hypothesis.
  The proof is the printed one: induction on the derivation, each node closed by
  its compatibility lemma (6.152–6.176).
* **Adequacy, from a typing derivation alone** — `Fig16.LogRel.Typed.adequacy`,
  in `Paper/CONF/Results.lean`: `DerivesWf ∅ [] e 1 → (∅, e) →* (∅, ())`, i.e.
  termination and memory reclamation for every closed program typed at `1`.  It
  composes `[CONF]` Corollary 3.3 at `SemX` (`Fig16.LogRel.Typed.corollary33`) with
  6.151.  `[CONF]` Theorem 3.2 and Corollary 3.3 are also stated and proved at the
  literal judgment over both machines (`Adequacy.theorem32`, `…Printed`,
  `Adequacy.corollary33`, `…Printed`).  Neither document prints a proof of 3.2 or
  3.3; these proofs are the source's.

Every declaration's `#print axioms` is within `[propext, Classical.choice,
Quot.sound]`; the tree has no `sorry`, `axiom`, `native_decide`, `implemented_by`,
`opaque`, `partial` or `unsafe`.

## Which printed definitions are repaired

Two layers, both recorded where the definition is printed.

1. **The library's reading of `[TR]` §§1–5.**  57 rows of the definition inventory
   carry the tag `[repair]`: the Lean departs from the print on purpose, and the
   row's comment in its section file gives the adjudication and the sentences of
   the paper that ground it.  `Paper/INDEX.md` (*Repaired definitions*) lists them
   with their files.  Among them: typing rules the library reads differently from
   the display (rows 2.10–2.18), the terms of the axiom table taken from
   `[CONF]` Figs. 3b, 14 and 15 (rows 2.39–2.47, 3.24–3.28), the two evaluation
   frames `K; e` and `injᵢ K` that `[TR]` p. 2's rules need and p. 3 does not print
   (rows 3.30, 3.31; the printed machine is kept as `TR3`, and each `wp` rule is
   re-proved over it), the lifetime index of `ℓ ↦ Imm α P̂` (row 5.30), the
   comprehensions of the walks `ex` and `ag` read as families (rows 5.20, 5.21),
   and Definition 6.3's `⊟` (row 5.66).
2. **The typed world.**  At our literal reading of the logical relation of `[TR]`
   p. 4, the library proves 6.151 only from an added hypothesis, and a configuration
   of our carrier refuses that reading without it; at the repair of rows 4.4–4.14
   and 5.33 it is proved with none (source `docs/boca-rules.md` §12.69–§12.72): an `Imm` payload
   read at its observable view, borrow payloads stratified by a record list, the
   `Imm` clause carrying the type the world recorded at the cell, `⊸`/`∀` Kripke
   over the record list, and `wp` ranging over the typed worlds `TW` the printed
   proofs' operations produce (`wpTS`).  The adjudication is in
   `Paper/S4_LogicalRelation/Definitions.lean` (its banner and rows 4.4–4.14) and
   `Paper/S5_Model/Definitions.lean` (row 5.33); the declarations are in
   `Support/TypedWorld/`.  Both readings are kept: every result of §6.3–§6.8 whose
   source also proves it at the typed world names that version in its record, and
   the literal Fundamental Property — the same statement at `Sem`, proved from the
   hypothesis `WithloadEscrow` — sits beside the headline, marked, with the
   configuration that refuses it without that hypothesis in
   `Paper/LiteralReadings/S6_8_FundamentalProperty.lean`.

## How it is organised

```
Paper/                     what the paper prints, in its order
  S1_Syntax … S5_Model/    [TR] §§1–5: Definitions.lean (one row per printed item),
                           Remarks.lean (theorems about them whose proofs use §6)
  S6_1_StandardLemmas/ … S6_8_FundamentalProperty/
                           [TR] §6.1–§6.8: Lemmas.lean, one record per numbered result
  S6_2_NonStandardLemmas/Definitions.lean   Definitions 6.1–6.3
  CONF/Results.lean        [CONF] 3.1–3.3
  LiteralReadings/         measurements of printed items read literally; nothing depends on them
  INDEX.md                 every numbered result and definition row → file and declaration
Support/                   [about ours]: what the paper leaves implicit, by topic
  Syntax, Lifetimes, Statics, Dynamics, Model, LogicalRelation, TypedWorld
Bridge/Names.csv           each declaration here → its source declaration
Bridge/Plan.csv            each unit of the dependency closure → its file
scripts/                   the checks
comparator/                the comparator challenge: the statement of adequacy over its trust base
.github/workflows/         CI and the comparator judge
tools/extract/             the generator: the Lean files are its output
```

A **record** for a numbered result gives its number, page and the source
inventory's status, the printed statement quoted, the printed proof transcribed
compactly in its own order, the declaration with the source's tag (`[as printed]`,
`[variant: …]`, `[restricted: …]`), the declarations the record cites, the
typed-world version, the literal readings, and the inventory's note.  After it come
the aliases: `TR.lemma_6_N` and, where `[TR]` names the rule, `TR.«name»`
(`TR.«Imm Frame»`, `TR.«↺⋆»`, `TR.«wp-bind»`); `[CONF]`'s results are
`CONF.lemma_3_1`, `CONF.theorem_3_2`, `CONF.corollary_3_3`.  A result an earlier
section's printed proof cites is declared in that earlier file, under a heading
naming the citation; its record and aliases stay in its own section.

One numbered result has no declaration: **`[TR]` Lemma 6.40** is untranscribed on
the printed carrier (its record says why).  `PLAN.md` gives the placement decisions
and the stages.

## Building and checking

The toolchain and Mathlib are the source's.  With the source checked out beside
this repository, `.lake/packages` can be a symlink to its packages (otherwise
`lake exe cache get` fetches Mathlib at the pinned revision, as CI does):

```
ln -s ../../borrow_lang/.lake/packages .lake/packages
lake build
```

The checks (`check-bridge.sh` needs the source built, `lake build BoCa` in
`borrow_lang`, and writes nothing inside it; `check-hygiene.sh` needs only this
repository):

```
scripts/check-bridge.sh     # every declaration against its source: kind, type, value
scripts/check-hygiene.sh    # forbidden keywords, and #print axioms of every constant
```

To regenerate every Lean file, `Bridge/`, `Paper/INDEX.md` and build:

```
BORROW_LANG_SRC=/path/to/borrow_lang tools/extract/run.sh [--dump]
```

The placement decisions are in `tools/extract/cfg.json`, the section banners in
`tools/extract/banners.py`, and the records of §6 and `[CONF]` §3 in
`tools/extract/results/*.txt`; change those, not the Lean.

## Verification

Two GitHub workflows, and one check that stays local.

* **CI** (`.github/workflows/ci.yml`, on every push and pull request): builds
  `Paper`, `Support` and `Challenge` with Mathlib's build cache; runs
  `scripts/check-hygiene.sh` (the keyword scan, and every declaration's axioms
  against `[propext, Classical.choice, Quot.sound]`); and runs the axiom audit,
  `scripts/AxiomCheck.lean`, whose output — `#print axioms` of
  `Fig16.LogRel.Typed.fundamentalProperty`, `Typed.adequacy`, `Typed.theorem32`,
  `Typed.corollary33`, the `CONF.*` results and every `TR.lemma_*` alias,
  enumerated from the environment — must equal `scripts/axioms.expected`.  A pass
  certifies that the library builds from a clean checkout, has no forbidden
  keyword, and that no result's axioms changed.
* **Comparator judge** (`.github/workflows/comparator.yml`, on pushes to `main`
  touching the Lean, and on demand): runs
  [leanprover/comparator](https://github.com/leanprover/comparator) with the
  nanoda kernel on `comparator/config.json`.  The judged theorem is
  `Fig16.LogRel.Typed.adequacy`, stated in `comparator/Challenge.lean` over a
  verbatim copy of what its statement reaches — the syntax, `DerivesWf` and the
  machine, `[TR]` §§1–3 — without importing `Paper` or `Support`.  A pass
  certifies that `Paper` proves exactly that statement from the three standard
  axioms, re-checked by the Lean kernel and by the independent nanoda kernel,
  without trusting our build; the model (`[TR]` §§4–6) and its repairs are not in
  the trust base.  `comparator/README.md` says what is trusted and why.
* **The bridge** (`scripts/check-bridge.sh`) is local only: it elaborates every
  declaration against the source repository `borrow_lang` at `970a9d0`, which CI
  does not have.
