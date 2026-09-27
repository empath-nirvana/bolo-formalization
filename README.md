# *From Linearity to Borrowing* in Lean 4

This repository is a Lean 4 mechanisation of Wagner, Gierczak, Marshall, Li and
Ahmed, *From Linearity to Borrowing* (PACMPL 9:OOPSLA2:415, 2025).  Throughout,
`[CONF]` is the conference paper and `[TR]` its supplement, which prints the complete
definitions and proofs.

The files follow `[TR]` section by section.  Each printed definition and each
numbered result sits in the file for its section, in printed order as far as Lean's
definition-before-use allows, under a comment that quotes what is printed and gives
its page.  `Paper/INDEX.md` lists every numbered result and every printed definition
with its file and Lean declaration.

## Headline results

**The Fundamental Property** (`[TR]` Lemma 6.151, `[CONF]` Lemma 3.1) —
`Fig16.LogRel.Typed.fundamentalProperty`, in
`Paper/S6_8_FundamentalProperty/Lemmas.lean` (aliases `TR.lemma_6_151`,
`TR.«Fundamental Property»`, `CONF.lemma_3_1`):

```lean
def FundamentalProperty : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty),
    DerivesWf Δ Γ e T → Δ.Ok → Ctx.ScopedB Δ Γ → SemX Δ Γ e T
```

`DerivesWf` is `[TR]` p. 2's typing rules, with the scoping half of p. 2's
well-formedness judgment `Δ ⊢ T` (`Ty.scopedB`, which also admits `Unk`) consulted at
binders and eliminated types, and `∀I` carrying the Barendregt premise that its
binder is free in no live type of `Γ` (C14).  The two further hypotheses are
`⊧ Δ`, carried as `Δ.Ok` (sufficient, `LifeCtx.sat_of_ok`), and `Δ ⊢ Γ`, carried as
`Ctx.ScopedB`.  p. 2's typing box prints no presupposition; p. 2 prints
`Presumes ⊧ Δ` only on the boxes of `Δ ⊢ T` and `Δ ⊢ T ⊐ @a`
(`docs/adjudications.md` §C.26).  The conclusion `SemX` is `[TR]` p. 4's
`Δ; Γ ⊨ e : T` at the repaired definitions described below; it is a different
relation from the literal `Sem`, and the result is a statement about `SemX`.  The
proof is the printed one: induction on the derivation, each case closed by the
typed-world version (`*_compatX`, `Support/TypedWorld/Compatibility.lean`) of its
compatibility lemma, `[TR]` Lemmas 6.152–6.176.

**Adequacy, from a typing derivation alone** — `Fig16.LogRel.Typed.adequacy`, in
`Paper/CONF/Results.lean`:

```lean
theorem adequacy (e : Expr) (hD : DerivesWf LifeCtx.empty ([] : Ctx Ty) e Ty.unit) :
    BoCa.BoLo.Steps Adequacy.emptyMem e Adequacy.emptyMem (.val .unit)
```

Every closed program that `DerivesWf` types at `1` has a run, from the empty
memory, to `()` and the empty memory: some run terminates and frees everything it
allocates.  (`alloc` chooses its fresh location, so `BoLo.Steps` is a statement about
some run; this is the form of `[CONF]` Corollary 3.3.)  At the
empty contexts `Δ.Ok` and `Ctx.ScopedB` hold, so this is `[CONF]` Corollary 3.3 at
`SemX` (`Fig16.LogRel.Typed.corollary33`, from Theorem 3.2,
`Fig16.LogRel.Typed.theorem32`) composed with the Fundamental Property.  Neither
document prints a proof of Theorem 3.2 or Corollary 3.3; the proofs here are ours
(`docs/adjudications.md` §A.1).

**Adequacy under every allocation policy** — `Fig16.LogRel.Typed.adequacyPol`, in the same
file:

```lean
theorem adequacyPol (pol : BoCa.BoLo.Policy) (e : Expr)
    (hD : DerivesWf LifeCtx.empty ([] : Ctx Ty) e Ty.unit) :
    BoCa.BoLo.PolRun pol Adequacy.emptyMem e Adequacy.emptyMem (.val .unit)
```

A policy fixes where `alloc` allocates, as any function of the memory that picks a location
every finite memory misses.  The typed world and 6.151 are proved for `wp` with its run drawn
from any class of runs closed under the operations `wp`'s rules build runs with
(`Fig16.LogRel.Typed.wpTSR`, `Fig16.LogRel.Typed.fundamentalR`); `wpTS`, `SemX` and every
statement above are the instance at every run, and `adequacy` is `adequacyPol` at the
least-free policy with the policy forgotten (`docs/adjudications.md` §12.74).  The classes are indexed:
`Fig16.LogRel.Typed.freshRel` is the runs whose allocations avoid a given finite list and every
location in reach, and `Fig16.LogRel.Typed.adequacyFresh` is adequacy for them.

**The trust base of `adequacy` is `[TR]` §§1–3.**  The statement mentions the
syntax (§1), the typing judgment `DerivesWf` (§2) and the machine `BoLo.Steps`
(§3), and nothing else.  The model — resources, the logic, `wp`, the logical
relation and the typed world of `[TR]` §§4–6, with every repair made there — is
used by the proof and does not occur in the statement.  Those §§1–3 declarations are
copied verbatim into `comparator/Challenge/`.  Two things there differ from the
print and are part of what is trusted: the typing rules and axiom terms as the
library reads them, and the two evaluation frames `K; e` and `injᵢ K` that
`BoLo.Steps` adds (see below).

Every declaration's `#print axioms` is within `[propext, Classical.choice,
Quot.sound]`.  `Paper/` and `Support/` contain no `sorry`, `axiom`, `native_decide`,
`implemented_by`, `opaque`, `partial` or `unsafe`.

## Examples

`Paper/Examples/` shows that the typing judgment `adequacy` takes as hypothesis types
real programs, and that adequacy is a statement about their runs.

* `Derivations.lean` — every rule of `[TR]` p. 2 and every line of the axiom table
  of p. 3, derived at a concrete instance in `DerivesWf`.
* `Programs.lean` — closed programs, each derived at `DerivesWf ∅ [] e 1`, with its
  adequacy instance `BoLo.Steps ∅ e ∅ ()` obtained from
  `Fig16.LogRel.Typed.adequacy` (`BoCa.Programs.*_runs`), and a kernel-checked run
  of the executable interpreter of `Support/Dynamics/Interpreter.lean` ending at
  `()` with no cell left (`BoCa.Programs.*_eval`, by `decide`).  Together they use
  every borrowing construct: `withbor` in all three forms, `withload` (at a
  function payload too, where the loader sees `Unk`), `withswap`, `copy`,
  `forget` at `Imm`, `Mut` and `Unk`, `swap`, the `[a]` modality, `∀I` and `∀E`.
  Among them are `[CONF]`'s own examples — Fig. 2c (`fig2c`), the aliasing program
  of p. 415:9 (`aliasLoad`), the nested `withswap` of p. 415:10 (`swapTwo`) and
  `greet` of Fig. 10b (`greetProg`) — each closed off by allocating the
  references it borrows.  `allocFree_steps` gives one run step by step on
  `BoLo.Steps`.  The interpreter allocates deterministically and is not
  proved to agree with `BoLo.Steps` (`docs/adjudications.md` D8); the adequacy
  instances are the theorems.
* `Model.lean` — `[TR]` Lemmas 6.7 and 6.20 at two resources that share an
  `imm` location, and inhabitants of hypotheses that rows of §6.2 bind or add.

## Building and checking

You need [elan](https://github.com/leanprover/elan) (the Lean toolchain manager),
`git`, `curl` and `python3`.  The toolchain is pinned in `lean-toolchain`
(`leanprover/lean4:v4.33.1`) and Mathlib in `lake-manifest.json`; elan and Lake
fetch both.

```sh
# 1. elan, if you do not have it
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
source "$HOME/.elan/env"

# 2. the repository, and Mathlib's prebuilt cache at the pinned revision
git clone https://github.com/empath-nirvana/bolo-formalization.git
cd bolo-formalization
lake exe cache get

# 3. build the library (Paper, Support) and the comparator challenge
lake build
lake build Challenge

# 4. hygiene: forbidden keywords, and every declaration's axioms
scripts/check-hygiene.sh

# 5. the axiom audit of the headline results and every TR.lemma_* alias
lake env lean scripts/AxiomCheck.lean > axioms.out
diff axioms.out scripts/axioms.expected

# 6. the comparator challenge is exactly what the library's statement reaches
tools/challenge/run.sh /tmp/challenge-check
diff -r /tmp/challenge-check/Challenge comparator/Challenge
```

Step 3 compiles the development itself (not Mathlib); it takes some minutes.
`scripts/check-hygiene.sh` scans every Lean file of `Paper/`, `Support/` and
`comparator/` outside comments for the forbidden
keywords (allowing exactly the one `sorry` that is the body of the challenge
statement in `comparator/Challenge.lean`, which is comparator's convention) and then
walks every constant of `Paper` and `Support` and fails unless its axioms are among
the three standard ones.  Step 5's output lists `#print axioms` for
`Fig16.LogRel.Typed.fundamentalProperty`, `adequacy`, `theorem32`, `corollary33`, the
`CONF.*` results and every `TR.lemma_*` alias, enumerated from the environment; the
`diff` must be empty.  Step 6 regenerates the challenge's copy of the trust base from
this build and must produce no difference.

**The comparator judge.**  [leanprover/comparator](https://github.com/leanprover/comparator)
checks, without trusting this build, that `Paper` proves exactly the statement in
`comparator/Challenge.lean` over declarations identical, constant for constant, to
those in `comparator/Challenge/`, using only the three standard axioms; it replays the
exported proof in the Lean kernel and in the independent nanoda kernel.  A pass
certifies the end-to-end statement above.  `comparator/README.md` gives the commands
(it needs comparator, lean4export and nanoda built locally) and says what is trusted.

Both checks also run on GitHub: `.github/workflows/ci.yml` (build, hygiene, axiom
audit) on every push, and `.github/workflows/comparator.yml` (the judge) on pushes to
`main` that touch the Lean.

## Layout

```
Paper/                        what the paper prints, in its order
  S1_Syntax … S5_Model/       [TR] §§1–5: Definitions.lean, one row per printed item;
                              Remarks.lean, theorems about them whose proofs use §6
  S6_1_StandardLemmas/ …
  S6_8_FundamentalProperty/   [TR] §6.1–§6.8: Lemmas.lean, one record per numbered result
  S6_2_NonStandardLemmas/Definitions.lean   Definitions 6.1–6.3
  CONF/Results.lean           [CONF] Lemma 3.1, Theorem 3.2, Corollary 3.3
  LiteralReadings/            printed items read literally, measured; nothing depends on them
  Examples/                   typing derivations and runs of closed programs; model instances
  INDEX.md                    every result and definition row → file and declaration
Support/                      what the paper leaves implicit, by topic; all [about ours]
docs/adjudications.md         every departure from the printed text, argued
comparator/                   the adequacy statement over a verbatim copy of its trust base
tools/challenge/              the generator of comparator/Challenge/**
scripts/                      the hygiene and axiom checks
Extensions/Purity/            an extension, not a transcription: the pure fragment of BoCa
                              (its own README; `lake build Purity`, not a default target)
```

A **record** for a numbered result gives its number, page and status, the printed
statement, the printed proof transcribed compactly in its own order, and the Lean
declaration with its tag.  The tags are `[as printed]`; `[encoding]` (a representation choice that changes
nothing, such as de Bruijn indices or a graph for a partial function);
`[restricted: …]` and `[variant: …]` (the statement differs, and the tag says how);
`[repair]` (a definition read differently from the display, see below); and
`[about ours]` (not printed, needed by Lean).  The aliases are `TR.lemma_6_N` and,
where `[TR]` names the rule, `TR.«name»` (`TR.«Imm Frame»`, `TR.«wp-bind»`);
`[CONF]`'s results are `CONF.lemma_3_1`, `CONF.theorem_3_2`, `CONF.corollary_3_3`.

## Where the mechanisation departs from the printed text

Where the printed text admits more than one reading, the two documents print
different versions, or the literal reading of a definition does not support a step a
printed proof takes, the mechanisation adopts a reading, tags the declaration
(`[repair]`, `[variant: …]`, `[restricted: …]`) and argues it in
`docs/adjudications.md`: the printed form, the sentences that ground the reading,
the reading adopted and what the literal reading admits.  `Paper/INDEX.md`
(*Repaired definitions*) lists every repaired row.  The main groups, by section of
`docs/adjudications.md`:

**In the trust base of `adequacy` (`[TR]` §§1–3).**

* *Typing rules.*  `⊸E`'s conclusion read as `e₂ e₁` (§12.2); `∀E` as `e ()`
  (§12.14, §12.27); `∀I`'s freshness `'a ∉ dom(Δ)` (§12.44); `[l]I`'s premise
  `Δ ⊨ Γ ⊐ @a` as `[CONF]` Fig. 7's pointwise lift (§12.6, §C.25); `⊑Imm`/`⊑Mut`
  at `@a` (§12.4); the `@aδ` clauses as `[CONF]` Fig. 11's (§12.7); the `Imm̲`
  metafunction's `Mut` and `Unk` clauses (§12.10, §12.11).
* *The axiom table.*  The terms of `swap`, `withbor` and `withload` are `[CONF]`'s
  (§12.20); the axiom types' `∀` binders are schematic (§12.45); `⊓Δ` is the meet
  over `dom(Δ)` (§12.15).
* *The machine.*  `BoLo.Steps` adds the frames `K; e` and `injᵢ K` (§12.42, D6).
  The printed machine is kept as `TR3.Steps`, and every `wp` rule of `[TR]` §6.7 is
  proved over it as well (`TR3.wp_*`).

**In the model (`[TR]` §§4–6), not in the trust base.**

* `↭`'s second clause with `imm` for p. 5's `mut` (§12.39); both printed readings of
  `↭` are kept, and agree inside `wp` (D3).
* The walks' comprehensions as families indexed by locations (§12.36, G6); `▷◁`'s
  second disjunct as the domain of `○` (§12.35); `Res_α` finite (§12.33, D10);
  `Life`'s order as `[CONF]` Fig. 11 labels it (§12.3, G5).
* `ℓ ↦ Imm α P̂` bounded by `⊓β̄`, and a subset in `reb_α`'s `imm` clause
  (§12.66, §12.67).
* Definition 6.3's `ρ ⊟ ρ′` read with the paragraph printed below it (§12.34,
  §12.38, §12.58).
* **The typed world** (§12.69–§12.73, `Support/TypedWorld/`): the `Imm` payload at
  its observable view (§12.69); borrow payloads stratified by a record list
  (§12.70); the `Imm` clause carrying the recorded type (§12.71); `⊸`/`∀` Kripke over
  the record list, and `wp` over the typed worlds the printed proofs' operations
  produce (§12.72).

**The literal readings.**  `Paper/LiteralReadings/` keeps, for several repaired
readings, the configuration that motivated the repair, built in Lean.  Among them:
over the printed machine, the closed terms `inj₁ (free (alloc ()))` and
`free (alloc ()); ()` take no step (`TR3.stuck_wInj`, `TR3.stuck_wSeq`); the cell
`Fig16.LogRel.MutImmCell` at `Mut @a (Imm @b 1)`, whose `⊓β̄` bound §12.66 discusses
(the corresponding statement under `⊔β̄` is argued there, not derived in Lean); and a
`withload` configuration at the literal logical relation
(`Fig16.LogRel.ViewWitness`), which is not a typed world (`ViewWitness.excluded`).
Nothing else depends on them.

## What is not done

* **`[TR]` Lemma 6.40** has no declaration; its record in
  `Paper/S6_2_NonStandardLemmas/Lemmas.lean` says so.
* **Quoted statements were transcribed from the PDFs' text layer**, with symbols the
  extraction garbled restored by hand against rendered pages.  A transcription error
  in a quoted statement would not be caught by Lean; the Lean statements are what the
  checks certify.
* Several results hold at a stated restriction or with an added hypothesis
  (`proved*`, `variant` in `Paper/INDEX.md`); each record names it.
