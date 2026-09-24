# Plan: a paper-shaped repository for *From Linearity to Borrowing*

This repository re-organises the Lean mechanisation in `borrow_lang` (branch
`mathlib-natdual`, commit `970a9d0`) by the sections of `[TR]`
(`3764117-supplement.pdf`), carrying only what the paper's results depend on.
Declarations are **moved, not re-proved**: each keeps its source name, its
statement and its proof, and `scripts/check-bridge.sh` checks that it
elaborates to the same type (and, for a definition, the same value) as its
source.

Toolchain and Mathlib are the source's: `lean-toolchain` is copied,
`lakefile.toml` pins the same Mathlib `rev`, and `.lake/packages` is a symlink to
`borrow_lang/.lake/packages` (not committed; recreate it with
`ln -s ../../borrow_lang/.lake/packages .lake/packages` after cloning).

## Layout

```
Paper/                                 what the paper prints, in its order
  S1_Syntax/Definitions.lean           [TR] §1, p. 1
  S2_Statics/Definitions.lean          [TR] §2, pp. 2–3
  S3_Dynamics/Definitions.lean         [TR] §3, pp. 3–4
  S4_LogicalRelation/Definitions.lean  [TR] §4, p. 4   (the literal reading; each row records its repair)
  S4_LogicalRelation/Remarks.lean      theorems about §4's definitions whose proofs use §6
  S5_Model/Definitions.lean            [TR] §5, pp. 4–6
  S5_Model/Remarks.lean                theorems about §5's definitions whose proofs use §6
  S6_1_StandardLemmas/Lemmas.lean      [TR] §6.1, Lemmas 6.1–6.15 (Stage 2b)
  S6_2_NonStandardLemmas/Definitions.lean   Definitions 6.1, 6.2, 6.3
  S6_2_NonStandardLemmas/Remarks.lean  theorems about Definition 6.2's ∼
  S6_2_NonStandardLemmas/Lemmas.lean   [TR] §6.2, Lemmas 6.16–6.63 (Stage 2b)
  S6_3_FrameAndAntiFrame/Lemmas.lean   [TR] §6.3 ─┐ skeletons:
  S6_4_StandardEntailments/Lemmas.lean [TR] §6.4  │ banner + the list of results
  S6_5_NonStandardEntailments/…        [TR] §6.5  │ and the declaration planned
  S6_6_ReborrowingEntailments/…        [TR] §6.6  │ for each
  S6_7_WeakestPreconditionRules/…      [TR] §6.7  │
  S6_8_FundamentalProperty/Lemmas.lean [TR] §6.8 ─┘
  CONF/Results.lean                    [CONF] 3.1–3.3 (skeleton)
  LiteralReadings/                     measurements of printed definitions read literally
Support/                               [about ours]: what makes the paper tree go, by topic
  Syntax/Terms                         value inversion, shifting, substitution, derived-form names
  Lifetimes/Terms, Substitution, Interpretation
                                       lifetime terms and contexts; substitution into types; δ-extension
  Statics/Contexts                     contexts as slot lists, and their splitting
  Dynamics/Machine, Interpreter        the machines' `→*`; an executable interpreter no result uses
  Model/Prelude, Notation, Cells       arithmetic, casts, bijections, ι; the notation of p. 6; cell facts
  Model/Lifetimes, CellFacts, Composition, Singletons, Walks, Algebra, WalkSplitting,
        Flattening, Compatibility      the carrier's algebra: what §6.1's results need
  Model/AlgebraInstances, RelaxedWalks, FlatteningCells, Subtraction, Update, UpdateFrame,
        Propositions, Outlives, Ancestors, Reborrow, ReborrowFrame, Restriction,
        ReborrowLowering, Surgery, ClosingSentence
                                       what §6.2's results need beyond §6.1's
  LogicalRelation/ClosingSubstitutions, ClosedJudgment, Facts
                                       γ(e) and free lifetime variables; ⊨ at ∅; ⌜p⌝ ⋆ P
  TypedWorld/Records, World, Relation  the typed world: records; TW and wpTS (row 5.33's repair);
                                       the repaired relation vX, gDenX, SemX (rows 4.4–4.14's repairs)
Bridge/Names.csv                       every declaration here → its source declaration
Bridge/Plan.csv                        every declaration of the closure → its target file (both stages)
scripts/                               bridge, axiom and hygiene checks
tools/extract/                         the generator that produced Paper/, Support/ and Bridge/
```

`tools/extract/run.sh` regenerates every Lean file here from the source
repository and builds; the Lean files are its output and are not edited by
hand.  `tools/extract/cfg.json` holds the placement decisions below, and
`tools/extract/banners.py` the section banners, and `tools/extract/results/S6_*.txt`
the numbered results' records (statement, transcribed proof, declarations and
aliases).  `tools/extract/stage2.py` is the driver; `gen.py` holds the selection,
layering and emission it shares.

Each `Definitions.lean` opens with a banner transcribing its section's display
from `[TR]`, then gives the printed items as rows of the source's
`docs/definition-inventory.md`, in printed order as far as definition-before-use
allows.  Each row carries: its number, the printed form, the page, a tag
(`[as printed]`, `[encoding]`, `[repair]`, `[about ours]`) and the inventory's
note — which for a `[repair]` row is the adjudication with the paper's sentences
that ground it.  The source docstring follows, then the Lean.

## How the content was selected

1. `scripts`-style dump of the source environment (`lake env lean` over `BoCa`):
   every constant, its module, source range, and the constants its type **and
   proof** use.
2. Roots: every Lean name cited in a row of `docs/paper-inventory.md` or
   `docs/definition-inventory.md` (the "Lean" column for the latter), minus the
   legacy carriers.
3. Closure over the dependency graph, at the level of source *units* (a
   declaration with its constructors, fields and auxiliaries; a `mutual`
   block), plus three dependencies the proof terms do not record: notation a
   unit's text uses, lemmas a tactic names (`simp [h]`, `rw [h]`, `unfold h`),
   and `@[simp]` lemmas about carried objects (a `rfl` simp lemma leaves no
   trace in the term that uses it).

The closure is **2,129 units, 33,321 lines of declarations**; no declaration of
the legacy carriers is in it.

| stage | units | declaration lines |
|---|---|---|
| 1 (this commit): [TR] §§1–5 definitions and what they need | 455 | 3,119 |
| 2: §6, [CONF] §3, the remaining literal readings, their support | 1,674 | 30,202 |

`Bridge/Plan.csv` lists every unit with its source location, stage and target.
The Stage 2 targets there are **tentative**: they come from the inventory rows
(the first cited declaration of a `6.x` row is taken as the result itself), and
Stage 2 re-derives placement by the same layering that places Stage 1.

### Left behind

| source module(s) | why |
|---|---|
| `Resource`, `Model`, `BoLo`, `Flatten`, `LogRel`, `Compat`, `Surgery`, `Ledger` | the old unstratified carrier `ResI` and everything stated over it; no cited result depends on them |
| `*Tests`, `TestCore`, `Programs` | test suites and example programs |
| `Wp` except the machine | the old carrier's `wp` and its rules; the machine (`BoLo.Kont`, `Head`, `Step1`, `Steps`, `Heap`) is carried because `Fig16.BoLo.wp` runs it |
| `Surplus` | not reached by any cited result |
| unreached declarations of the carried modules (e.g. `Fig16` 237 units, `Fig16LogRel` 129, `Reborrow` 49, `Derives` 24, `TR3` 25) | examples, superseded variants and helpers no cited result uses |
| `vercheck/`, `BorrowLang/`, `FutureWork/`, the checker | out of scope |

`tools/extract/plan.py` prints the per-module counts of what is left behind.

## Stage 1 — what is here, and what builds

`lake build` builds `Paper` and `Support` with no errors and no `sorry`.

| file | units |
|---|---|
| `Paper/S1_Syntax/Definitions.lean` | 31 |
| `Paper/S2_Statics/Definitions.lean` | 34 |
| `Paper/S3_Dynamics/Definitions.lean` | 22 |
| `Paper/S4_LogicalRelation/Definitions.lean` | 24 |
| `Paper/S5_Model/Definitions.lean` | 200 |
| `Paper/S6_2_NonStandardLemmas/Definitions.lean` | 10 |
| `Paper/LiteralReadings/S4_LogicalRelation.lean` | 3 |
| `Support/…` (16 files) | 131 |

Checks, all passing:

* `scripts/check-bridge.sh` — 1,573 declarations compared with their source; 0
  mismatches (kind, type, and value for definitions; auxiliary declarations are
  compared through the declarations that use them).
* `scripts/check-hygiene.sh` — no `sorry`/`axiom`/`native_decide`/`implemented_by`/
  `opaque`/`partial`/`unsafe` outside comments; `#print axioms` of all 1,987
  constants ⊆ `[propext, Classical.choice, Quot.sound]`.

## Design decisions that depart from the brief, and why

1. **§2 imports §3.**  The axiom table of p. 3 names `swap`, `copy`, `forget`,
   `withbor`, `withload`, `withswap`; `[TR]` defines them as terms on p. 4, in
   §3.  They stay in §3's file, and §3's file needs nothing from §2.
2. **Definitions 6.1–6.3 are in `S6_2_NonStandardLemmas/Definitions.lean`**, where
   `[TR]` prints them (pp. 9, 13, 17), not in §5 where the inventory lists them
   (rows 5.61, 5.65, 5.66).  Nothing in §§1–5 uses them.
3. **The typed world is in `Support/TypedWorld/`, imported after §4.**  Its
   worlds (`Typed.TW`) are defined through value shapes (`Typed.vShape`), which
   read lifetimes through §4's `atLife` (row 4.15), so it cannot precede §4; and
   nothing in the paper files uses it, so it can follow.  §4's file holds the
   literal reading, and each of its `[repair]` rows (4.4, 4.5, 4.8, 4.9, 4.11,
   4.13, 4.14) records the adjudication and the repair in its comment; §5's file
   holds the printed `wp` and row 5.33's record.  Each declaration of the repair
   opens with a pointer back to its row (`cfg.json`'s `support_modules`).
4. **`[about ours]` declarations inside `Definitions.lean`.**  When a
   declaration the paper does not print is both defined through a printed row
   and needed by a later printed row of the same section (the finite map, the
   lifetime set `℘⁺(Life)`, the stratum embeddings, the cell constructors'
   equations), no file order puts it in `Support/`.  Such declarations are kept
   inline, each run marked `[about ours]`, and so are the `@[simp]` equations
   of a printed object, which go with it: 94 units in §5, 31 in the other four
   files.
5. **Theorem-valued inventory rows.**  Rows whose Lean is a theorem about a
   definition (the clause equations `vDen_unit` … `vDen_unk`, `Cell_eq`,
   `compS_immOf`, `SPropS.toU_range`, `noOwn_compS`, `Sim.refl`,
   `supported_iff`) are in `Definitions.lean` where they cost nothing further.
   Eight cost more — their proofs reach §6 machinery — and move in Stage 2, to a
   `Remarks.lean` after §6: `BigComp.perm` (5.56), `vDen_mut_supported` and
   `vDen_mut_of_supported` (4.16), `MutImmGap.inRel_same` (4.17, literal),
   `sem_iff` (4.18), `wp_eq_wpU` (5.62), `Sim.trans` and `upd_iff_sim` (5.65).
   Row 5.67 ([CONF]'s prose characterisation of `✓`, whose theorems include
   Lemma 6.36 itself) moves with §6.
6. **Names are unchanged in Stage 1** (`BoCa.Fig16.ResU.Comp`, …), so the bridge
   is by name.  Two private lemmas, `BoCa.Fig16.cast_left`/`cast_right`, are
   public here because their users landed in another file.  Numbered names
   (`TR.lemma_6_60`, with the paper's own name as a second alias) are for §6's
   results, in Stage 2.
7. **`Support/` files are named by topic and layered by what they need.**
   `cfg.json`'s `topic_rules` (source module and declaration-name pattern) and
   `topic` (source module) give each unsupported declaration a topic; a topic
   whose declarations sit on both sides of a paper file is split in two, and
   `support_names` names each part (the generator refuses an unnamed part).
8. **The executable interpreter** (`BoCa.Mem`, `step`, `run`; rows 3.10, 3.37)
   is in `Support/Dynamics/Interpreter.lean`: the paper gives a relation, and no
   result uses the interpreter.
9. **Every file is wrapped in `noncomputable section`**, which marks nothing
   that compiles; and a file whose declarations come from a source module that
   imported Mathlib imports Mathlib.
10. **Citations in comments** (`docs/boca-rules.md` §12.67, `BoCa/Fig16.lean` §3,
    …) are to the source repository at `970a9d0`; its `docs/` is not copied.
    Sentences of inventory notes that record history (deletions, migrations,
    earlier scorings) are dropped.

## Stage 2

Stage 1's placement is pinned: `stage2.py` recomputes it with stage 1's file
order and keeps it, so the §§1–5 files do not move.  New support is layered by
the latest paper file it can follow (`assign(…, latest=True)`), so a `Support/`
file sits just before the first paper file that needs it.

1. **Remaining definitions' remarks — done (2a).**  The eight deferred theorem
   rows and row 5.67's theorems: `Paper/S4_LogicalRelation/Remarks.lean`
   (4.16's two directions, 4.18's `sem_iff`), `Paper/S5_Model/Remarks.lean`
   (5.62's `wp_eq_wpU`, and the records of 5.56 and 5.67),
   `Paper/S6_2_NonStandardLemmas/Remarks.lean` (Definition 6.2's `Sim.trans`
   and `upd_iff_sim`, which 6.39 and 6.59 use), and 4.17's literal
   `MutImmGap.inRel_same` into `Paper/LiteralReadings/S4_LogicalRelation.lean`,
   which now comes last.  A row's theorem that an earlier paper file needs is
   declared there under a heading saying so, and its row's record says where:
   `BigComp.perm` (5.56), `CellU.compatR_iff` and `CompatS.disjoint_of_immFree`
   (5.67) are declared in §6.1's file, `AgW.nonimm_beneath_imm` and
   `flat_eq_ag_at` (5.67) in §6.2's.
2. **§6.1–§6.2 — done (2b).**  Lemmas 6.1–6.63, 63 records, 62 moved
   declarations, 63 aliases `TR.lemma_6_N` (6.58 has two, `_left`/`_right`; 6.40
   has none).  Each record: number, page, the inventory's status, the printed
   statement quoted (symbols the text extraction garbles restored: `⦇ρ⦈`, `⟦ρ⟧`,
   `◐`, `▸◁`, subscripts), the printed proof transcribed compactly in its own
   order, the declaration(s) with the source docstring's tag, and the inventory
   note (sentences about the old carrier dropped).  §§6.1–6.2 print no names,
   so there is no second alias.  Specific rows:
   * 6.10 and 6.35 are one declaration (`Valid.split`), the same statement
     printed twice; 6.35's record says so and aliases it.
   * 6.40 has no declaration here: the source inventory scores it `variant`
     and cites only the old carrier's `BoLo.valid_own_congr`.
   * 6.47 and 6.49 carry both readings of `↭` (`Upd.refl`/`UpdV.refl`,
     `UpdV.trans`/`Upd.trans`); the alias is to the inventory's first-named.
   * 6.63's inventory row cites the old carrier's `Resource.Res.lt_down`; the
     printed carrier's statement is `Fig16.Life.down_sqsubset`, used here.

   **Forward citations.**  `[TR]`'s proofs of 6.7, 6.10 and 6.15 (§6.1) cite
   6.18, 6.20 and 6.36 (§6.2), and Lean needs 6.30 and 6.31 with them; §6.2's
   proofs cite §6.1 throughout.  So the two files cannot each hold their own
   declarations in one import order.  The rule applied (`stage2.py`,
   "ahead of its subsection"): a result whose declaration an earlier paper file
   needs is declared in that file under a heading naming the printed citation,
   and its record and alias stay in its own subsection's file.  Five results
   (6.18, 6.20, 6.30, 6.31, 6.36) and three definition-row theorems are declared
   in §6.1's file this way.  Within a file, a result a printed-earlier result
   needs moves up to just before it (6.42 before 6.17, 6.41 before 6.21, 6.32
   and 6.33 before 6.26, 6.63 before 6.27).

   **`[about ours]` inside the lemma files.**  71 unprinted declarations sit
   between results because they need a result above and a result below needs
   them (44 in §6.1's file, 26 in §6.2's, 1 in LiteralReadings); each run is
   headed with the result it serves.  Everything else unprinted is in
   `Support/Model/*` (532 units over both stages' support).

   Checks at the end of 2b: `lake build` clean; `check-bridge.sh` 2,205
   declarations compared (the 63 aliases against the declarations they name),
   0 mismatches; `check-hygiene.sh` 0 forbidden keywords, 2,674 constants within
   `[propext, Classical.choice, Quot.sound]`.

3. **§6.3–§6.6 — done (2c).**  Theorems and Lemmas 6.64–6.134, 71 records in four
   files, 145 aliases.  The record format is 2b's, with three additions (the
   syntax of `tools/extract/results/*.txt`: `@@` header, `>` statement, proof, `~`
   remark, and `+ beside|tw|lit NAME`):
   * **The printed name as a second alias.**  §§6.3–6.6 name almost every rule, and
     the name is `TR.«name»` beside `TR.lemma_6_N` (`TR.refl`, `TR.«Imm Frame»`,
     `TR.«↺⋆»`, `TR.«И-mono»`).  Names are transcribed from the rendered page,
     small capitals as lower case and without the typesetting space (`[]-mono`,
     `!l`, `Иf`).  6.72 (`∧l`) and 6.73 (`∨r`) are schematic in `i ∈ {1, 2}` and are
     two declarations each, aliased `TR.lemma_6_72_1`/`TR.«∧l₁»` and so on.  6.130 and
     6.134 print no name.
   * **Cited declarations.**  `+ beside` puts a declaration the record cites next to
     the result (the dereliction instance of 6.84, the stronger wildcard readings of
     6.95 and 6.119, 6.115's equal-index case, 6.130's scope lemmas, 6.131's
     all-types induction); the record lists them under *Also here*.
   * **Typed-world versions.**  `+ tw` names the source's version of the result at
     `wpTS`/`𝒱X`/`vShape` (6.64–6.66, 6.113's stratified `I-mono`, 6.131, 6.132).
     They stay in `Support/TypedWorld/`, with a heading pointing back to the record,
     and the record names them under *Typed-world version*.  Pulling them in brings
     most of the typed world with them (≈ 6,500 lines); `Support/TypedWorld/` is split
     by source module — `Images`, `Invariant`, `Wp`, `RelationFacts`, `FrameRules`,
     `ReborrowShapes` (and in 2e `Reborrow`, `Compatibility`) — after stage 1's
     `Records`, `World`, `Relation`.
   * **Literal readings.**  `+ lit` sends a measurement of a printed statement read
     literally to `Paper/LiteralReadings/S6_N_…` (6.84's and 6.88's and 6.102's
     premises checked, 6.115's printed index `α ⊔ β` measured, 6.130's hypothesis
     shown not free, 6.131's `Ref`-chain residual as a `def … : Prop`).

   Lemma 6.112 (`Иf`) is declared in §6.3's file, ahead of its subsection: the
   printed proofs of 6.64 and 6.65 open with it.  New support files:
   `Support/Model/FrameSurgery` (the swaps §6.3 spends at both ends of the run),
   `Support/Model/Entailments`, `Support/Model/Strata`, `Support/Model/Empty`.  The
   generator changes: a support unit no paper file needs is layered after the last
   paper file, and a record's file imports the file declaring its aliased
   declaration.  `scripts/check-bridge.py` now treats `simp`'s instantiated lemmas
   (`…._simp_N_M`, numbered per environment) as auxiliaries, and digests an
   auxiliary's type after replacing the auxiliaries it names, to a fixpoint (Lean
   shares one abstracted proof between declarations of a module, so the source's
   `inner._proof_1` is this repository's `mutInv._proof_1`).

   Checks at the end of 2c: `lake build` clean; `check-bridge.sh` 2,831
   declarations compared, 0 mismatches; `check-hygiene.sh` 0 forbidden keywords,
   3,496 constants within `[propext, Classical.choice, Quot.sound]`.

4. **§6.7 — done (2d).**  Lemmas 6.135–6.150, 16 records, 34 aliases (6.139 is
   schematic in `i`, as 6.72).  Beside each rule is its re-proof over `[TR]` §3's
   printed machine, `TR3.wp_…` (6.150 has none; `TR3.wp` itself is in
   `Support/Dynamics/PrintedWp`), and the shared steps `wp_head` (6.137–6.140) and
   `wp_frame_noOwn` (6.148, 6.149).  The typed-world versions `wpTS_…` and
   `wpTS_reborrow` are named in the records and sit in `Support/TypedWorld/Wp` and
   `Support/TypedWorld/Reborrow`.  `Paper/LiteralReadings/S6_7_…` holds the printed
   machine's stuck forms and `TR3.wp` at them (under 6.135), and 6.150's `DefectB`
   configuration with `defectB_not_rebEscrow`; the whole of `BoCa/DefectB.lean`
   that those need moves into that file (`cfg.json`'s `literal_patterns`), except
   the two facts about `∅` the typed world uses (`Support/Model/Empty`).  Likewise
   `RebExample`, the resource 6.130's literal reading is measured at, moves into
   `Paper/LiteralReadings/S6_6_…`.  New support: `Support/Model/ReborrowRule`
   (`RebEscrow` and the pieces 6.150 names), `SubtractionKeep`, `UpdateSymmetry`.
   The generator names the layer after the last paper file `@After:END`, so adding a
   literal-readings file does not rename it.

   Checks at the end of 2d: `lake build` clean; `check-bridge.sh` 3,073
   declarations compared, 0 mismatches; `check-hygiene.sh` 0 forbidden keywords,
   3,824 constants within `[propext, Classical.choice, Quot.sound]`.

Still to come:

5. **§6.8 and [CONF] §3** (6.151–6.176, 3.1–3.3): the compatibility lemmas, the
   typed world (`Support/TypedWorld/*`, ≈ 8,800 lines), the Fundamental Property
   at `SemX`, adequacy; `ViewWitness` and `DefectB`'s refutations into
   `LiteralReadings`.

For each result: the printed statement and a compact transcription of the
printed proof in the comment, the moved declaration, a numbered alias, the
library's tag, and the lists `CLAUDE.md` asks for (unspent printed hypotheses,
unused uniqueness results, untranscribed run-up lemmas) carried over from the
source docstrings.  Each stage ends with `lake build`, `check-bridge.sh` and
`check-hygiene.sh` passing.
