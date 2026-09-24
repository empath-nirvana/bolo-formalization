import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S3_Dynamics.Definitions
import Paper.S4_LogicalRelation.Definitions
import Paper.S4_LogicalRelation.Remarks
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Paper.S6_8_FundamentalProperty.Lemmas
import Support.Dynamics.Machine
import Support.Dynamics.PrintedWp
import Support.LogicalRelation.Adequacy
import Support.LogicalRelation.ClosedJudgment
import Support.LogicalRelation.ClosingSubstitutions
import Support.LogicalRelation.Compatibility
import Support.Model.Cells
import Support.Model.Empty
import Support.Model.FlatteningCells
import Support.Model.Prelude
import Support.Model.Propositions
import Support.Model.Surgery
import Support.Model.Update
import Support.Statics.Contexts
import Support.Statics.Presupposed
import Support.Syntax.Terms
import Support.TypedWorld.Compatibility
import Support.TypedWorld.Records
import Support.TypedWorld.Relation
import Support.TypedWorld.World

/-!
# [CONF] §3 — the conference paper's numbered results  (pp. 415:17–18)

`[CONF]` numbers three results.  **Lemma 3.1** is `[TR]` 6.151, printed twice; its
declaration is in `Paper/S6_8_FundamentalProperty/Lemmas.lean` and its record here
aliases it (`CONF.lemma_3_1`).  **Theorem 3.2** (adequacy: termination and memory
reclamation) and **Corollary 3.3** (adequacy at `1`) are stated in `[CONF]` and
proved in neither document; the proofs here are the source's.  Each is stated once
per machine — the library's (`BoLo.Steps`, `[TR]` §3 with rows 3.30 and 3.31's two
frames) and `[TR]` §3's as printed (`TR3.Steps`) — and once more at the repaired
judgment (`Fig16.LogRel.Typed.theorem32`, `Fig16.LogRel.Typed.corollary33`).

**The headline.**  `Fig16.LogRel.Typed.adequacy` composes Corollary 3.3 at `SemX`
with 6.151: `DerivesWf ∅ [] e 1 → (∅, e) →* (∅, ())` — termination and memory
reclamation for every closed program `[TR]` p. 2 types at `1`, with no semantic
hypothesis.

**How this file reads.**  The numbered results of the subsection, in printed order as
far as Lean's definition-before-use allows.  Each opens with a record:

* the result's number, page and the source inventory's status (`proved`, `proved*`,
  `variant`; source `docs/paper-inventory.md`);
* the printed statement, quoted, with the extraction's garbled symbols restored;
* the printed proof, transcribed compactly and in its own order, citing the lemmas it
  cites;
* the Lean declaration, moved from the source with its name, statement and proof
  unchanged (its docstring carries the source's tag and its account of the proof),
  and the numbered alias `TR.lemma_6_N` declared after it;
* the inventory row's note.

A result whose declaration an earlier subsection's printed proof needs is declared
in that subsection's file, under a heading saying so; its record and alias stay
here.  A run of declarations the paper does not print, placed in this file only
because a result below needs it and it needs a result above, is marked
`[about ours]` and names the result it serves.  Citations of `docs/…` and `BoCa/…`
are to the source repository (`borrow_lang` at `970a9d0`).
-/

noncomputable section

namespace BoCa.Adequacy
open BoCa.Fig16
open BoCa.Fig16.BoLo (wp NoOwn WRes)
open BoCa.BoLo (Heap)
open BoCa.Lifetime (LifeCtx LSub)

/-! A declaration the record of Theorem 3.2 (Adequacy) cites. -/
/-- **`[CONF]` Theorem 3.2 (Adequacy)**, p. 415:18, over the completed machine:
*"If `⊨ wp(e){⌜P̂⌝}` then `(∅, e) →* (∅, v)` and `P̂(v)` for some `v`."*

`→*` is `BoLo.Steps`, which is the `↦*` of the `wp` in the same row, so the two
occurrences are one relation.  `docs/boca-rules.md` §12.42 is why that machine
is `[TR]` §3's rather than one of ours: §3's `Kont` is elided, and the completion
is two frames and nothing else.
`[as printed]` (`[CONF]` Theorem 3.2, p. 415:18; the `→*` is `[TR]` §3 completed
as §12.42 adjudicates) -/
def Theorem32 : Prop :=
  ∀ (e : Expr) (P : Val → Prop),
    wp e (fun v => Fig16.BoLo.pure (P v)) (PMap.empty : WRes) →
    ∃ v : Val, BoCa.BoLo.Steps emptyMem e emptyMem (.val v) ∧ P v

end BoCa.Adequacy

namespace BoCa.TR3
open BoCa.Fig16
open BoCa.BoLo (Heap)
open BoCa.Fig16.BoLo (Entails sep wand all box top ptoOwn ptoMut ptoImm outlives_comp NoOwn noOwn_empty noOwn_compS hash_lower hash_valid hash_valid_comp hash_shift updV_compS_own hash_compS_own lower_compS_own_inv lower_get_own lower_eq_none_iff get_eq_none_of_flat get_eq_none_of_compatS_own compatS_single_of_get_none loc_infinite compS_reassoc compS_reassoc' compS_exch compS_lcomm updV_frame updV_outlives)

/-! A declaration the record of Theorem 3.2 (Adequacy) cites. -/
/-- **This `wp` is the stronger proposition.**  The two definitions differ in
one conjunct, and §4's containment turns that conjunct one way.
`wp_lt_fig16` at the end of the file is the other half — a term at which
`Fig16Wp`'s row holds and this one's is false — so the entailment is strict.

What that buys a rule depends on where `wp` sits in it.  A rule whose
antecedent does *not* mention `wp` — 6.136, 6.137, 6.138, 6.139, 6.140, 6.141,
6.142, 6.143, 6.145 — composes with this entailment and so **implies** its
`Fig16Wp` counterpart, strictly.  A rule whose antecedent does mention `wp` —
6.135, 6.146, 6.147, 6.148, 6.149 — strengthens the antecedent and the
consequent together, so the two versions are not comparable by this theorem;
each is the printed statement about a different `↦*`, and both are proved.
`[about ours: the two `wp`s, over the two machines]` -/
theorem wp_le_fig16 (e : Expr) (Q : Val → WProp) :
    Entails (wp e Q) (Fig16.BoLo.wp e Q) := by
  intro ρ hw ρf hf
  obtain ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
    hA, hB, hC⟩ := hw ρf hf
  exact ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ', h₁, h₂, h₃, h₄, h₅, h₆, h₇,
    Steps.toWp h₈, h₉, hA, hB, hC⟩

end BoCa.TR3

namespace BoCa.Adequacy
open BoCa.Fig16
open BoCa.Fig16.BoLo (wp NoOwn WRes)
open BoCa.BoLo (Heap)
open BoCa.Lifetime (LifeCtx LSub)

/-! A declaration the record of Theorem 3.2 (Adequacy) cites. -/
/-- **`[CONF]` Theorem 3.2** over `[TR]` §3's machine as printed: `TR3.wp` in
the antecedent and `TR3.Steps` in the conclusion, so again one relation
throughout.

`TR3.wp` is the stronger antecedent and `TR3.Steps` the stronger conclusion, so
this row and `Theorem32` are not comparable — the pattern ledger D6 records for
every §6.7 rule with a `wp` on the left.
`[as printed]` (`[CONF]` Theorem 3.2, p. 415:18, over `[TR]` §3's machine as
`BoCa/TR3.lean` transcribes it) -/
def Theorem32Printed : Prop :=
  ∀ (e : Expr) (P : Val → Prop),
    BoCa.TR3.wp e (fun v => Fig16.BoLo.pure (P v)) (PMap.empty : WRes) →
    ∃ v : Val, BoCa.TR3.Steps emptyMem e emptyMem (.val v) ∧ P v

/-! A declaration the record of Theorem 3.2 (Adequacy) cites. -/
/-- **The memory-reclamation residue.**  `∅ ↭ ρ⁺` says `⦇ρ⁺⦈` carries no `imm`
and no `mut` cell — both clauses of `[TR]` p. 5's `↭` are `⇔`s against
`⦇∅⦈ = ∅` — and `ρ⁺|own = ∅` says `ρ⁺` carries no top-level `own` cell.

This is the conjunct `[CONF]` p. 415:23 calls *"essential for the memory
reclamation component of adequacy (Theorem 3.2), which insists that owned cells
are freed rather than forgotten"*, and it is where that conjunct is spent.
`[about ours: what `[CONF]` Theorem 3.2 reduces to at `ρ = ρ_f = ∅`]` -/
def Reclaim : Prop :=
  ∀ ρ : WRes, ResU.UpdV PMap.empty ρ → NoOwn ρ → ρ = PMap.empty

/-! A declaration the record of Theorem 3.2 (Adequacy) cites. -/
/-- **The memory-reclamation residue, discharged.**  `↭`'s guard gives `✓ρ`, so
`⦇ρ⦈` exists; `ResU.Flat.get` — `[TR]` 6.16's own step, *"the cells of `ρ` are a
subset of those of `⦇ρ⦈`"* — carries a cell of `ρ` at `ℓ` into `⦇ρ⦈` at `ℓ` with
its kind.  `NoOwn` refuses the `own` case outright.  For `imm` and `mut`, `↭`'s
two clauses are `⇔`s against `⦇∅⦈`, and `Fig16.BoLo.flat_empty` says that is
`∅`, so neither cell can be there either.  Hence `ρ` has no cell at all.

The split is on `Cell`'s own sum (`CellU.rep`), not on walk shapes.
`[about ours: `[CONF]` Theorem 3.2's reclamation conjunct at `ρ = ρ_f = ∅`;
no proof of it is printed in either document]` -/
theorem reclaim : Adequacy.Reclaim := by
  intro ρ hupd hno
  refine PMap.ext fun l => ?_
  rw [PMap.empty_get]
  cases hg : ρ.get l with
  | none => rfl
  | some ψ =>
      exfalso
      obtain ⟨σ, hσ⟩ := hupd.2.2
      obtain ⟨χ, hχ, hk, -, -⟩ := ResU.Flat.get hσ hg
      have hfa : ρ.FlatAt l χ := (ResU.flatAt_iff hσ l χ).mpr hχ
      rcases CellU.rep χ with ⟨w, rfl⟩ | ⟨s, w, ξ, hξ, rfl⟩ | ⟨b, w, ξ, hξ, P, hP, rfl⟩
      · have hko : ψ.kind = Kind.own := by rw [← hk]; exact CellU.kind_ownOf w
        have hr : (ρ.restrict Kind.own).get l = some ψ :=
          ResU.restrict_eq_some.mpr ⟨hg, hko⟩
        rw [hno, PMap.empty_get] at hr
        simp at hr
      · have hemp := (hupd.1.1 l s w ξ hξ).mpr hfa
        rw [ResU.flatAt_iff Fig16.BoLo.flat_empty, PMap.empty_get] at hemp
        simp at hemp
      · obtain ⟨w', ξ', h', hP', hfa'⟩ := (hupd.1.2 l b P).mpr ⟨w, ξ, hξ, hP, hfa⟩
        rw [ResU.flatAt_iff Fig16.BoLo.flat_empty, PMap.empty_get] at hfa'
        simp at hfa'

end BoCa.Adequacy

/-!
## Lemma 3.1 (Fundamental Property) · `[CONF]` p. 415:17 · inventory `proved*`

> If Δ; Γ ⊢ e : T then Δ; Γ ⊨ e : T.

**Printed proof, transcribed.** *"The proof of the Fundamental Property is by induction on the syntactic typing judgment, and it is divided into a collection of compatibility lemmas, one per syntactic typing rule, which establishes that its semantic analogue is admissible."*

`[TR]` Lemma 6.151 prints the same statement, and its record in `Paper/S6_8_FundamentalProperty/Lemmas.lean` gives both forms: `Fig16.LogRel.Typed.fundamentalProperty` at the repaired judgment `SemX`, with no hypothesis, and the literal reading at `Sem`, which is refused (`Paper/LiteralReadings/S6_8_FundamentalProperty.lean`).

**Lean.** `BoCa.Fig16.LogRel.Typed.fundamentalProperty`, alias `CONF.lemma_3_1` — the declaration of Lemma 6.151 (Fundamental Property), in `Paper/S6_8_FundamentalProperty/Lemmas.lean`: the same statement, printed twice.

**Inventory note** (source `docs/paper-inventory.md`, row 3.1). This row **is** [TR] 6.151 — [CONF] p. 415:17 prints the same statement, *"If Δ; Γ ⊢ e : T then Δ; Γ ⊨ e : T"*, and the proof it describes is [TR] §6.8's. `Fig16.LogRel.Typed.fundamentalProperty`, at row 6.151's restrictions — `⊧ Δ` carried as `Δ.Ok`, at the definition repairs of `docs/boca-rules.md` §12.69–§12.72 — and no other hypothesis. `Fig16.LogRel.FundamentalProperty`, the literal reading's statement, is refused (`Fig16.LogRel.ViewWitness.fundamentalProperty_refused`, §12.68). Scored here only so that the [CONF] block does not read as unattempted; do not track it twice
-/
alias CONF.lemma_3_1 := BoCa.Fig16.LogRel.Typed.fundamentalProperty

namespace BoCa.Adequacy
open BoCa.Fig16
open BoCa.Fig16.BoLo (wp NoOwn WRes)
open BoCa.BoLo (Heap)
open BoCa.Lifetime (LifeCtx LSub)

/-!
## Theorem 3.2 (Adequacy) · `[CONF]` p. 415:18 · inventory `proved`

> If ⊨ wp(e){⌜P̂⌝} then (∅, e) →* (∅, v) and P̂(v) for some v.

**Printed proof, transcribed.** Neither document prints one.  *"The next section develops proofs for these properties"* (`[CONF]` p. 415:18), and `[CONF]` §4 states no numbered result; `[TR]` §6 ends at 6.176.  The argument here is the source's: `⊨ H` is `H ∅`, so `wp` is read at `ρ = ∅` with its own `∀ρ_f` at `ρ_f = ∅`, and `⌜−⌝` pins `ρ′ = ∅`; the run is then the conclusion's, and what remains is `Adequacy.reclaim` — `∅ ↭ ρ⁺` and `ρ⁺|own = ∅` force `ρ⁺ = ∅`, *"essential for the memory reclamation component of adequacy (Theorem 3.2), which insists that owned cells are freed rather than forgotten"* (`[CONF]` p. 415:23).

**Lean.** `BoCa.Adequacy.theorem32`, alias `CONF.theorem_3_2`.

**Also here.** `BoCa.Adequacy.Theorem32`; `BoCa.Adequacy.Reclaim`; `BoCa.Adequacy.reclaim`; `BoCa.Adequacy.Theorem32Printed`; `BoCa.Adequacy.theorem32Printed`; `BoCa.Fig16.LogRel.Typed.theorem32`; `BoCa.TR3.wp_le_fig16`.

**Inventory note** (source `docs/paper-inventory.md`, row 3.2). `Adequacy.theorem32` proving `Adequacy.Theorem32`, and `Adequacy.theorem32Printed` proving `Adequacy.Theorem32Printed` — the row over each of the two machines. **The statement is `[CONF]`'s and the proof is not**: neither document prints an argument for this row (`docs/adequacy-plan.md` §1), so the status scores the statement alone and the argument below is ours. `⊨ H` is `H ∅`, so `wp` is read at `ρ = ∅` and its own `∀ρ_f` instantiated at `ρ_f = ∅`, and `⌜−⌝` pins `ρ′ = ∅`; the four composites collapse and **every occurrence of `→*` in the unfolding disappears**, which is why one argument serves over both machines and why no termination measure appears — `[TR]` p. 6's `wp` is a total-correctness row that asserts the run. What is left is `Adequacy.reclaim`, `[CONF]` p. 415:23's *"essential for the memory reclamation component"* conjunct: `Fig16.BoLo.flat_empty` gives `⦇∅⦈ = ∅`, `ResU.Flat.get` carries a cell of `ρ⁺` into `⦇ρ⁺⦈` ([TR] 6.16's own step), `NoOwn` refuses the `own` case and `↭`'s two clauses refuse `imm` and `mut` against `⦇∅⦈`. `Adequacy.Theorem32`, the row at 600 dpi — *"If ⊨ wp(e){⌜P̂⌝} then (∅, e) →* (∅, v) and P̂(v) for some v"* — with `⊨ H` read as `H ∅` (`docs/adequacy-plan.md` §2a fixes that reading from three printed things, and `Fig16.LogRel.Sem` already reads it so), `⌜P̂⌝` as the pointwise lift of a meta `P̂ : Val → ℙ`, and `∅` on the memory side as `Adequacy.emptyMem`. Neither implies the other: `wp` sits in the antecedent and `TR3.wp_le_fig16` turns that conjunct one way only, the pattern ledger D6 records for 6.135, 6.146, 6.147, 6.148 and 6.149. **Neither document prints a proof** — [TR] §6 runs 6.1-6.8 and ends at the Fundamental Property (last result 6.176, physical p. 49), and [CONF] §4 develops the model and states no numbered result — so `docs/adequacy-plan.md` §1 records the evidence and lays out the options rather than picking one. What is established about the shape: unfolding `wp(e){⌜P̂⌝}(∅)` at `ρ_f ≔ ∅` pins `ρ′ = ∅` through `⌜−⌝`, collapses the row's four composites, and **leaves no occurrence of `→*` at all**, so the residue is machine-free and is `Adequacy.Reclaim`: `∅ ↭ ρ⁺` and `ρ⁺
-/
/-- **`[CONF]` Theorem 3.2**, over the completed machine.  Neither document
prints an argument, so this one is ours.

`⊨ H` is `H ∅`, so `wp` is read at `ρ = ∅` and its own `∀ρ_f` instantiated at
`ρ_f = ∅`; `⌜−⌝` pins `ρ′ = ∅`.  The four composites collapse by
`ResU.eq_of_comp_empty_left`, `Fig16.BoLo.lower_empty` names both memories, and
what is left is `reclaim`, which empties `ρ⁺` and so makes the run's final
memory `⟦∅⟧`.  No occurrence of `→*` survives the unfolding, and no termination
measure appears: `[TR]` p. 6's `wp` is a total-correctness row that asserts the
run.
`[about ours: `[CONF]` Theorem 3.2's proof, which neither document prints]` -/
theorem theorem32 : Adequacy.Theorem32 := by
  intro e P hwp
  obtain ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ',
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    hwp PMap.empty Fig16.LogRel.hash_empty
  obtain ⟨hρ'e, hPv⟩ := h12
  subst hρ'e
  obtain rfl : (PMap.empty : WRes) = fρ := ResU.eq_of_comp_empty_left h4
  obtain rfl : (PMap.empty : WRes) = fρ' := ResU.eq_of_comp_empty_left h2
  obtain rfl : ρp = fρ'p := ResU.eq_of_comp_empty_left h6
  obtain rfl : ρp = π := ResU.eq_of_comp_empty_left h9
  obtain rfl : ρp = PMap.empty := reclaim ρp h10 h11
  obtain rfl : μ = (fun _ => none) := ResU.Lower.functional h5 Fig16.BoLo.lower_empty
  obtain rfl : μ' = (fun _ => none) := ResU.Lower.functional h7 Fig16.BoLo.lower_empty
  exact ⟨v, h8, hPv⟩

end BoCa.Adequacy

alias CONF.theorem_3_2 := BoCa.Adequacy.theorem32

namespace BoCa.Adequacy
open BoCa.Fig16
open BoCa.Fig16.BoLo (wp NoOwn WRes)
open BoCa.BoLo (Heap)
open BoCa.Lifetime (LifeCtx LSub)

/-! A declaration the record of Theorem 3.2 (Adequacy) cites. -/
/-- **`[CONF]` Theorem 3.2** over `[TR]` §3's machine as printed.  `TR3.wp` has
`Fig16.BoLo.wp`'s shape with `TR3.Steps` in place of `BoLo.Steps`, and the
unfolding above removes every occurrence of `→*`, so the argument is the same
one; the residue `reclaim` mentions no machine.
`[about ours: `[CONF]` Theorem 3.2's proof over `[TR]` §3's machine, which
neither document prints]` -/
theorem theorem32Printed : Adequacy.Theorem32Printed := by
  intro e P hwp
  obtain ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ',
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    hwp PMap.empty Fig16.LogRel.hash_empty
  obtain ⟨hρ'e, hPv⟩ := h12
  subst hρ'e
  obtain rfl : (PMap.empty : WRes) = fρ := ResU.eq_of_comp_empty_left h4
  obtain rfl : (PMap.empty : WRes) = fρ' := ResU.eq_of_comp_empty_left h2
  obtain rfl : ρp = fρ'p := ResU.eq_of_comp_empty_left h6
  obtain rfl : ρp = π := ResU.eq_of_comp_empty_left h9
  obtain rfl : ρp = PMap.empty := reclaim ρp h10 h11
  obtain rfl : μ = (fun _ => none) := ResU.Lower.functional h5 Fig16.BoLo.lower_empty
  obtain rfl : μ' = (fun _ => none) := ResU.Lower.functional h7 Fig16.BoLo.lower_empty
  exact ⟨v, h8, hPv⟩

end BoCa.Adequacy

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! A declaration the record of Theorem 3.2 (Adequacy) cites. -/
/-- **`[CONF]` Theorem 3.2 (Adequacy)** at the tagged `wpTS`, at the empty list:
if `⊨ wp_{[]}(e){⌜P̂⌝}` then `(∅, e) →* (∅, v)` and `P̂(v)` for some `v`.
`[about ours: [CONF] 3.2 at `wpTS`; the proof is `Adequacy.theorem32`'s]` -/
theorem theorem32 (e : Expr) (P : Val → Prop)
    (hwp : wpTS [] e (fun _ v => Fig16.BoLo.pure (P v)) (PMap.empty : WRes)) :
    ∃ v : Val, BoCa.BoLo.Steps Adequacy.emptyMem e Adequacy.emptyMem (.val v) ∧ P v := by
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', -, -,
    h1, h2, h3, h5, h6, h7, h8, h9, h10, h11, -, -, -, -, h12⟩ :=
    hwp PMap.empty PMap.empty [] Fig16.LogRel.hash_empty (ResU.comp_empty_right _)
      TW.empty htg
  obtain ⟨hρ'e, hPv⟩ := h12
  subst hρ'e
  obtain rfl : (PMap.empty : WRes) = fρ' := ResU.eq_of_comp_empty_left h2
  obtain rfl : ρp = fρ'p := ResU.eq_of_comp_empty_left h6
  obtain rfl : ρp = π := ResU.eq_of_comp_empty_left h9
  obtain rfl : ρp = PMap.empty := Adequacy.reclaim ρp h10 h11
  obtain rfl : μ = (fun _ => none) := ResU.Lower.functional h5 Fig16.BoLo.lower_empty
  obtain rfl : μ' = (fun _ => none) := ResU.Lower.functional h7 Fig16.BoLo.lower_empty
  exact ⟨v, h8, hPv⟩

end BoCa.Fig16.LogRel.Typed

namespace BoCa.Adequacy
open BoCa.Fig16
open BoCa.Fig16.BoLo (wp NoOwn WRes)
open BoCa.BoLo (Heap)
open BoCa.Lifetime (LifeCtx LSub)

/-! A declaration the record of Corollary 3.3 (Adequacy at 1) cites. -/
/-- **`[CONF]` Corollary 3.3**, p. 415:18: *"If `⊨ e : 1` then
`(∅, e) →* (∅, ())`."*  `⊨ e : 1` is `Fig16.LogRel.Sem` at `Δ = Γ = ∅`, whose
`ℰ` is `Fig16.BoLo.wp`, so the machine is `Theorem32`'s.

The hypothesis is the **semantic** judgment, so this row appeals to `[CONF]`
Lemma 3.1 (`[TR]` 6.151) nowhere.
`[as printed]` (`[CONF]` Corollary 3.3, p. 415:18) -/
def Corollary33 : Prop :=
  ∀ e : Expr,
    Fig16.LogRel.Sem LifeCtx.empty ([] : Ctx Ty) e Ty.unit →
    BoCa.BoLo.Steps emptyMem e emptyMem (.val .unit)

/-!
## Corollary 3.3 (Adequacy at 1) · `[CONF]` p. 415:18 · inventory `proved`

> If ⊨ e : 1 then (∅, e) →* (∅, ()).

**Printed proof, transcribed.** Neither document prints one.  It is Theorem 3.2 instantiated: `𝒱⟦1⟧δ` is the pure `⌜v = ()⌝`, which is 3.2's `⌜P̂⌝` at `P̂ ≜ (· = ())`, and the judgment at `Δ = Γ = ∅`, `δ = ∅`, `γ = []`, `ρ = ∅` supplies the antecedent.  Its hypothesis is the semantic judgment, so it appeals to Lemma 3.1 nowhere; `Fig16.LogRel.Typed.adequacy` composes the two, from a typing derivation alone.

**Lean.** `BoCa.Adequacy.corollary33`, alias `CONF.corollary_3_3`.

**Also here.** `BoCa.Adequacy.Corollary33`; `BoCa.Adequacy.SemUnitPrinted`; `BoCa.Adequacy.Corollary33Printed`; `BoCa.Adequacy.corollary33Printed`; `BoCa.Fig16.LogRel.Typed.corollary33`; `BoCa.Fig16.LogRel.Typed.adequacy`.

**Literal reading.** `BoCa.TR3.corThree_unreachable`, in `Paper/LiteralReadings/CONF.lean`.

**Inventory note** (source `docs/paper-inventory.md`, row 3.3). `Adequacy.corollary33` proving `Adequacy.Corollary33`, and `Adequacy.corollary33Printed` proving `Adequacy.Corollary33Printed`. **Statement printed, proof ours**, as at 3.2. It is 3.2 instantiated: `Fig16.LogRel.vDen_unit` makes `𝒱⟦1⟧δ` the pure `⌜v = ()⌝`, which is the row's own `⌜P̂⌝`, and `Fig16.LogRel.sem_iff` at `δ = ∅`, `γ = []`, `ρ = ∅` supplies the antecedent — `Adequacy.models_empty`, `Adequacy.gDen_empty` and `Adequacy.psub_nil` are those three. Appeals to [TR] 6.151 nowhere: the hypothesis is the semantic judgment. `Adequacy.Corollary33`, the row at 600 dpi — *"If ⊨ e : 1 then (∅, e) →* (∅, ())"* — with `⊨ e : 1` as `Fig16.LogRel.Sem LifeCtx.empty [] e Ty.unit`, [TR] p. 4's `Δ; Γ ⊨ e : T` at `Δ = Γ = ∅` and at `∅` by 3.2's reading of the bare turnstile. It is **3.2 instantiated** at `P̂ ≜ (· = ())`, because `Fig16.LogRel.vDen_unit` makes `𝒱⟦1⟧δ(v)` the pure `⌜v = ()⌝` and that is `⌜P̂⌝`'s own shape; the rest is `Fig16.LogRel.sem_iff`, `Fig16.LogRel.gDen_mk` and `Expr.psub k [] e = e`, which is the one piece of plumbing that does not exist. **Its printed hypothesis is the SEMANTIC judgment, so it appeals to 3.1 nowhere** — not merely until a final composition. `Adequacy.Corollary33Printed` is the row over [TR] §3's machine as printed, and it is stateable without rebuilding a logical relation: `wp` occurs in `𝒱⟦T⟧δ` only at `⊸` and `∀`, so at `T = 1` the interpretation names no machine (`Fig16LogRel` §11) and `Adequacy.SemUnitPrinted` is `ℰ⟦1⟧δ(e)` there. **`TR3.corThree_unreachable` is not about this row**: it exhibits `TR3.wSeq`, closed and typed at `1` by [TR] p. 2 (`TR3.derives_wSeq`), with no run to `()` on the printed machine — but `TR3.wp_seq_false` refuses the semantic hypothesis at that same term, so what it measures is the composite with 3.1, which over the printed machine also loses 6.154, 6.157 and 6.169.
-/
/-- **`[CONF]` Corollary 3.3**.  3.2 instantiated: `Fig16.LogRel.vDen_unit`
makes `𝒱⟦1⟧δ` the pure `⌜v = ()⌝`, which is 3.2's own `⌜P̂⌝`.
`Fig16.LogRel.sem_iff` at `δ = ∅`, `γ = []`, `ρ = ∅` supplies the antecedent.

The hypothesis is the **semantic** judgment, so this appeals to `[CONF]`
Lemma 3.1 (`[TR]` 6.151) nowhere.
`[about ours: `[CONF]` Corollary 3.3's proof, which neither document prints]` -/
theorem corollary33 : Adequacy.Corollary33 := by
  intro e hsem
  have hwp := Fig16.LogRel.sem_iff.mp hsem Lifetime.LSub.empty [] PMap.empty
    models_empty (gDen_empty _)
  rw [Fig16.LogRel.substAll, psub_nil, vDen_unit_eq] at hwp
  obtain ⟨v, hsteps, hv⟩ := theorem32 e (· = Val.unit) hwp
  subst hv
  exact hsteps

end BoCa.Adequacy

alias CONF.corollary_3_3 := BoCa.Adequacy.corollary33

namespace BoCa.Adequacy
open BoCa.Fig16
open BoCa.Fig16.BoLo (wp NoOwn WRes)
open BoCa.BoLo (Heap)
open BoCa.Lifetime (LifeCtx LSub)

/-! A declaration the record of Corollary 3.3 (Adequacy at 1) cites. -/
/-- `⊨ e : 1` over `[TR]` §3's machine as printed.  `wp` occurs in `𝒱⟦T⟧δ` only
at `⊸` and `∀`, so at `T = 1` the interpretation names no machine
(`Fig16.LogRel.vDen_unit`) and `TR3.wp e (𝒱⟦1⟧δ)` **is** `ℰ⟦1⟧δ(e)` over the
printed machine — `BoCa/Fig16LogRel.lean` §11's own observation.  `𝒟⟦∅⟧` and
`𝒢⟦∅⟧δ([])` name no machine either, so `[TR]` p. 4's `Δ; Γ ⊨ e : T` at
`Δ = Γ = ∅` is this row and no logical relation has to be rebuilt.
`[about ours: `[TR]` p. 4's `Δ; Γ ⊨ e : T` at `Δ = Γ = ∅`, `T = 1`, over
`BoCa/TR3.lean`'s machine]` -/
def SemUnitPrinted (e : Expr) : Prop :=
  ∀ δ : LSub, LifeCtx.Models LifeCtx.empty δ →
    BoCa.TR3.wp e (Fig16.LogRel.vDen .unit δ) (PMap.empty : WRes)

/-! A declaration the record of Corollary 3.3 (Adequacy at 1) cites. -/
/-- **`[CONF]` Corollary 3.3** over `[TR]` §3's machine as printed.

`BoCa.TR3.corThree_unreachable` is **not** about this row: it exhibits a closed
term `[TR]` p. 2 types at `1` whose run to `()` the printed machine has not, and
what that measures is the composite with `[CONF]` Lemma 3.1 — the printed
hypothesis here is the semantic judgment, which `BoCa.TR3.wp_seq_false` refuses
at that same term.  `docs/boca-rules.md` §12.42's reading of §3 as elided is
what the pair argues for.
`[as printed]` (`[CONF]` Corollary 3.3, p. 415:18, over `[TR]` §3's machine as
`BoCa/TR3.lean` transcribes it) -/
def Corollary33Printed : Prop :=
  ∀ e : Expr, SemUnitPrinted e → BoCa.TR3.Steps emptyMem e emptyMem (.val .unit)

/-! A declaration the record of Corollary 3.3 (Adequacy at 1) cites. -/
/-- **`[CONF]` Corollary 3.3** over `[TR]` §3's machine as printed, from
`SemUnitPrinted` by `theorem32Printed`.
`[about ours: `[CONF]` Corollary 3.3's proof over `[TR]` §3's machine, which
neither document prints]` -/
theorem corollary33Printed : Adequacy.Corollary33Printed := by
  intro e hsem
  have hwp := hsem Lifetime.LSub.empty models_empty
  rw [vDen_unit_eq] at hwp
  obtain ⟨v, hsteps, hv⟩ := theorem32Printed e (· = Val.unit) hwp
  subst hv
  exact hsteps

end BoCa.Adequacy

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! A declaration the record of Corollary 3.3 (Adequacy at 1) cites. -/
/-- **`[CONF]` Corollary 3.3** at `SemX`: if `⊨ e : 1` then `(∅, e) →* (∅, ())`.
`[about ours: [CONF] 3.3 at `SemX`; the proof is `Adequacy.corollary33`'s]` -/
theorem corollary33 (e : Expr) (hsem : SemX LifeCtx.empty ([] : Ctx Ty) e Ty.unit) :
    BoCa.BoLo.Steps Adequacy.emptyMem e Adequacy.emptyMem (.val .unit) := by
  have hwp := hsem LSub.empty [] [] PMap.empty Adequacy.models_empty (gDenX_nil _ _)
  rw [substAll, Adequacy.psub_nil] at hwp
  obtain ⟨v, hsteps, hv⟩ := theorem32 e (· = Val.unit) hwp
  subst hv
  exact hsteps

/-! A declaration the record of Corollary 3.3 (Adequacy at 1) cites. -/
/-- **The end-to-end guarantee**: a closed program `[TR]` p. 2 types at `1` (under its
presuppositions, `DerivesWf`) runs from the empty memory to `()` and the empty memory —
termination and memory reclamation — through `fundamental` (6.151 at `SemX`, no hypothesis)
and `corollary33`.  `[about ours: [CONF] Lemma 3.1 composed with Corollary 3.3, at `SemX`]` -/
theorem adequacy (e : Expr) (hD : DerivesWf LifeCtx.empty ([] : Ctx Ty) e Ty.unit) :
    BoCa.BoLo.Steps Adequacy.emptyMem e Adequacy.emptyMem (.val .unit) :=
  corollary33 e (fundamental _ _ _ _ hD ok_empty (fun s hs => absurd hs (by simp)))

end BoCa.Fig16.LogRel.Typed

end
