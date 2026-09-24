# *From Linearity to Borrowing* in Lean 4

This repository is a Lean 4 mechanisation of Wagner, Gierczak, Marshall, Li and
Ahmed, *From Linearity to Borrowing* (PACMPL 9:OOPSLA2:415, 2025).  Throughout,
`[CONF]` is the conference paper and `[TR]` its supplement, which prints the complete
definitions and proofs.

The files follow `[TR]` section by section.  Each printed definition and each
numbered result sits in the file for its section, in printed order as far as Lean's
definition-before-use allows, under a comment that quotes what is printed and gives
its page.  `Paper/INDEX.md` lists every numbered result and every printed definition
with its file and Lean declaration.  The development was carried out in an earlier
working repository and moved here unchanged in statement and proof.

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

If `Δ; Γ ⊢ e : T` as `[TR]` p. 2 reads it (`DerivesWf`: the typing rules, with the
judgments `⊨ Δ` and `Δ ⊢ Γ` that p. 2's boxes presuppose carried as `Δ.Ok` and
`Ctx.ScopedB`), then `Δ; Γ ⊨ e : T` (`SemX`: `[TR]` p. 4's judgment at the repaired
definitions described below).  There is no other hypothesis.  The proof is the
printed one: induction on the derivation, each case closed by its compatibility
lemma, `[TR]` Lemmas 6.152–6.176.

**Adequacy, from a typing derivation alone** — `Fig16.LogRel.Typed.adequacy`, in
`Paper/CONF/Results.lean`:

```lean
theorem adequacy (e : Expr) (hD : DerivesWf LifeCtx.empty ([] : Ctx Ty) e Ty.unit) :
    BoCa.BoLo.Steps Adequacy.emptyMem e Adequacy.emptyMem (.val .unit)
```

Every closed program that `[TR]` p. 2 types at `1` runs, from the empty memory, to
`()` and the empty memory: it terminates and frees everything it allocates.  It is
`[CONF]` Corollary 3.3 at `SemX` (`Fig16.LogRel.Typed.corollary33`, from Theorem 3.2,
`Fig16.LogRel.Typed.theorem32`) composed with the Fundamental Property.  Neither
document prints a proof of Theorem 3.2 or Corollary 3.3; the proofs here are ours
(`docs/adjudications.md` §A.1).

**Why its trust base is `[TR]` §§1–3 only.**  The statement of `adequacy` mentions
the syntax (§1), the typing judgment `DerivesWf` (§2) and the machine `BoLo.Steps`
(§3), and nothing else.  The model — resources, the logic, `wp`, the logical
relation and the typed world of `[TR]` §§4–6, with every repair made there — is
used by the proof and does not occur in the statement.  A reader who accepts the
statement therefore has to check only §§1–3 against the paper, and those
declarations are copied verbatim into `comparator/Challenge/` so that they can be
read in one place.  Two things there differ from the print and are part of what is
trusted: the typing rules and axiom terms as the library reads them, and the two
evaluation frames `K; e` and `injᵢ K` that `BoLo.Steps` adds (see below).

Every declaration's `#print axioms` is within `[propext, Classical.choice,
Quot.sound]`.  `Paper/` and `Support/` contain no `sorry`, `axiom`, `native_decide`,
`implemented_by`, `opaque`, `partial` or `unsafe`.

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
`scripts/check-hygiene.sh` scans every Lean file outside comments for the forbidden
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
(it needs comparator, lean4export and nanoda built locally) and says precisely what
is trusted.

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
  INDEX.md                    every result and definition row → file and declaration
Support/                      what the paper leaves implicit, by topic; all [about ours]
docs/adjudications.md         every departure from the printed text, argued
comparator/                   the adequacy statement over a verbatim copy of its trust base
tools/challenge/              the generator of comparator/Challenge/**
scripts/                      the hygiene and axiom checks
```

A **record** for a numbered result gives its number, page and status, the printed
statement, the printed proof transcribed compactly in its own order, the Lean
declaration with its tag, and a note on how the declaration reads the statement.
The tags are `[as printed]`; `[encoding]` (a representation choice that changes
nothing, such as de Bruijn indices or a graph for a partial function);
`[restricted: …]` and `[variant: …]` (the statement differs, and the tag says how);
`[repair]` (a definition read differently from the display, see below); and
`[about ours]` (not printed, needed by Lean).  The aliases are `TR.lemma_6_N` and,
where `[TR]` names the rule, `TR.«name»` (`TR.«Imm Frame»`, `TR.«wp-bind»`);
`[CONF]`'s results are `CONF.lemma_3_1`, `CONF.theorem_3_2`, `CONF.corollary_3_3`.

## Where the mechanisation departs from the printed text

Lean needs every definition to mean exactly one thing.  In a number of places the
printed text admits more than one reading, the two documents print different
versions, or the literal reading of a definition does not support a step a printed
proof takes.  In each such place the mechanisation adopts a reading, grounded where
possible in the paper's own prose, and records it where the definition is
transcribed (tag `[repair]`) and in `docs/adjudications.md`, which gives for each the
printed form, the sentences that ground the reading, the reading adopted and what
the literal reading admits.  `Paper/INDEX.md` (*Repaired definitions*) lists every
such row.  The main groups:

**In the trust base of `adequacy` (`[TR]` §§1–3).**

* *Typing rules.*  `⊸E`'s printed conclusion `e₁ e₂` is read as `e₂ e₁`, the function
  on the left as in the grammar and the β-rule (§12.2); `∀E` applies a lifetime by `e ()`, following
  `Λ.e ≜ λ_.e` (§12.14, §12.27); `∀I`'s extended context `Δ, ('a ⊏ @b)` carries the
  freshness `'a ∉ dom(Δ)` that extending a partial map requires (§12.44); the
  premise `Δ ⊨ Γ ⊐ @a` of `[l]I`, which `[TR]` does not define, is `[CONF]` Fig. 7's
  pointwise lift (§12.6, §C.25); the conclusions of `⊑Imm`/`⊑Mut`, printed at
  `@b` in `[TR]`, are at `@a` as in `[CONF]` Figs. 7/9 and `[TR]` Lemmas 6.167/6.168
  (§12.4); the `@aδ` clauses are `[CONF]`
  Fig. 11's homomorphic interpretation (§12.7); the `Imm̲` metafunction takes
  `[CONF]` Fig. 9's `Mut` clause and a `Unk` clause (§12.10, §12.11).
* *The axiom table.*  The terms of `swap`, `withbor` and `withload` are `[CONF]`
  Figs. 3b, 14 and 15's, which match the types both documents print (§12.20); the
  `∀` binders of the axiom types are schematic (§12.45), and `⊓Δ` is the meet over
  `dom(Δ)` (§12.15).
* *The machine.*  `[TR]` p. 2 types `e₁; e₂` at any `e₁ : 1` and `injᵢ e` at any
  `e`, and p. 3 prints no evaluation frame `K; e` or `injᵢ K`.  `BoLo.Steps` adds
  those two frames (§12.42, D6).  The printed machine is kept as `TR3.Steps`, and
  every `wp` rule of `[TR]` §6.7 is proved over it as well (`TR3.wp_*`).

**In the model (`[TR]` §§4–6), not in the trust base.**

* The second clause of `↭` is read with `imm` where p. 5 prints `mut`, following
  `[CONF]` Fig. 18b (§12.39); both printed readings of `↭` are kept, and they agree
  inside `wp` (D3).
* The comprehensions of the walks `ex` and `ag` are read as families indexed by
  locations (§12.36, G6); `▷◁`'s second disjunct as the domain of `○` (§12.35);
  `Res_α` carries the `fin` mark `[TR]` prints on `Res` (§12.33, D10); `Life`'s
  order follows `[CONF]` Fig. 11's labelling (§12.3, G5).
* `ℓ ↦ Imm α P̂` bounds `α` by `⊓β̄`, the borrows outstanding at the location, and
  `reb_α`'s `imm` clause keeps a subset of them, following `[CONF]` p. 415:24's
  *"its imm locations are preserved at their original lifetimes"* (§12.66, §12.67).
* Definition 6.3's `ρ ⊟ ρ′` is pinned by the paragraph printed below it
  (§12.34, §12.38, §12.58).
* **The typed world** (§12.69–§12.73).  At the literal reading of `[TR]` p. 4's
  logical relation, the Fundamental Property is proved here from an added
  hypothesis, `WithloadEscrow`; `SemX` reads rows 4.4–4.14 and 5.33 so that it holds
  with none: an `Imm` payload is read at its observable view, as `[CONF]`'s *"there
  is no view at which it would be safe to access the payload"* and `Imm̲`'s `Unk`
  clauses describe (§12.69); borrow payloads are stratified by a record list
  (§12.70); the `Imm` clause carries the type the world recorded at the cell
  (§12.71); `⊸`/`∀` are Kripke over the record list, and `wp` ranges over the typed
  worlds the printed proofs' operations produce (§12.72).  The declarations are in
  `Support/TypedWorld/`.  Both readings are kept: the literal Fundamental Property,
  `Fig16.LogRel.fundamentalProperty` at `Sem` from `WithloadEscrow`, sits beside the
  headline.

Where a Lean statement differs from a printed one — an added hypothesis, a
restriction — its record says so in its tag, and `Paper/INDEX.md` gives the status
(`proved*`, `variant`).

**What the literal readings admit.**  `Paper/LiteralReadings/` builds, for each
repaired reading that matters to a result, the configuration at which the literal
reading and the printed step cannot be reconciled on this carrier, with every
hypothesis discharged in Lean.  Among them: over the printed machine, the closed
terms `inj₁ (free (alloc ()))` and `free (alloc ()); ()`, both typed by p. 2, take no
step (`TR3.stuck_wInj`, `TR3.stuck_wSeq`), so `[CONF]` Corollary 3.3's conclusion is
not reachable there for them (`TR3.corThree_unreachable`); under `α ⊑ ⊔β̄`,
`𝒱⟦Mut @a (Imm @b 1)⟧` is empty at the cell and lifetime set
`Fig16.LogRel.MutImmGap` builds; and at the literal logical relation, a `withload` node
of this carrier at which the Fundamental Property's conclusion at `Sem` is refused
without `WithloadEscrow` (`Fig16.LogRel.ViewWitness.fundamentalProperty_refused`),
a configuration that is not a typed world (`ViewWitness.excluded`).  These are
measurements of what a reading admits on this carrier; nothing else depends on them.

## What is not done

* **`[TR]` Lemma 6.40** has no declaration; its record in
  `Paper/S6_2_NonStandardLemmas/Lemmas.lean` says so.
* **Statements were transcribed from the PDFs' text layer**, with symbols the
  extraction garbled restored by hand; glyph questions were checked against
  rendered pages.  A
  transcription error in a quoted statement would not be caught by Lean; the Lean
  statements are what the checks certify.
* Several results hold at a stated restriction or with an added hypothesis
  (`proved*`, `variant` in `Paper/INDEX.md`); each record names it.
