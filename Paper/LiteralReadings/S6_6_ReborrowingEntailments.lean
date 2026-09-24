import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S4_LogicalRelation.Definitions
import Paper.S5_Model.Definitions
import Support.Model.Composition
import Support.Model.Propositions
import Support.Model.Singletons

/-!
# Literal readings — [TR] §6.6

* 6.130: `reborrow_emp_outside_stratum`, a resource outside `Res_α` against
  `↺_α emp` — the hypothesis the Lean adds is not free — at the resource
  `RebExample` builds;
* 6.131 (`↺V₁`): `RefPrintedChainResidual`, what the `Ref` bullet's printed chain
  leaves at our objects, recorded as a `def … : Prop` and not derived; no
  obstruction to it is verified.

**How this file reads.**  Each run opens with the result it measures and says where
that result's record is.  Each declaration carries its tag; an
`[about ours: …]` tag names what is measured.  Nothing in the paper tree depends on
this file.
-/

noncomputable section

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
### Lemma 6.131 (↺V₁) — literal reading

The printed statement, the printed proof and the adjudication are in `Paper/S6_6_ReborrowingEntailments/Lemmas.lean`, under the record of Lemma 6.131 (↺V₁).
-/
/-- **What `[TR]` 6.131's `Ref` bullet leaves, followed as printed.**  After
"Apply IH", "Apply theorem 6.130", "Apply `↺⋆`" and the unit law the antecedent
is `↺_α (↺_α 𝒱⟦Imm̲ 'a T′⟧δ(v′))` and the goal is `↺_α 𝒱⟦Imm 'a T′⟧δ(v)`, with
`Imm` the constructor (clause (5)).  This is that entailment: the modality is
doubled and the value is the cell's *contents* `v′` where the goal names the
*location* `v`.  It is not derived, and no obstruction to it has been verified;
`reborrow_vDen`'s `Ref` block takes `[TR]` 6.121 (`↺↦`) at this step instead.
`[about ours: the residual of 6.131's printed `Ref` chain, at our objects]` -/
def RefPrintedChainResidual (α : Life) (x : LifeVar) (δ : LSub) (T : Ty) (v : Val) : Prop :=
  ∀ v' : Val,
    reborrow α (reborrow α (vDen (T.immReborrow (.var x)) δ v'))
      ⊨ reborrow α (vDen (Ty.imm (.var x) T) δ v)

end BoCa.Fig16.LogRel

namespace BoCa.Fig16.RebExample

/-! `[about ours]` — what the Lean of Lemma 6.130 needs; the paper prints nothing here. -/
private def mutWit (w : Nat) : ResU Nat Nat := ResU.single 1 (CellU.ownOf w)

private theorem mutWit_stratum (w : Nat) (α : Life) : (mutWit w).InStratum α := by
  intro l ψ e
  obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
  exact trivial

private def mutInv : Nat → SPropS Nat Nat 3 := fun _ _ => True

private def mutCell (v w : Nat) : CellU Nat Nat :=
  CellU.mutOf 3 v (mutWit w) (mutWit_stratum w 3) mutInv trivial

/-- `ρ ≜ ℓ₀ ↦ mut(3, v, ℓ₁ ↦ own(w), λ_ _. ⊤)`. -/
private def mutRes (v w : Nat) : ResU Nat Nat := ResU.single 0 (mutCell v w)

private theorem mutRes_zero (v w : Nat) : (mutRes v w).get 0 = some (mutCell v w) :=
  ResU.single_get_self _ _

/-- **`reb_α` is not satisfied by everything.**  `@ρ ⊐ α` refuses a lifetime the
resource does not outlive: `@ρ = 3` here, so no `ρ′` whatever is a reborrow of
`ρ` at `α = 1`.
`[about ours: a non-inhabitant of the printed set]` -/
theorem not_reb_of_at (v w : Nat) (ρ' : ResU Nat Nat) : ¬ ResU.Reb 1 (mutRes v w) ρ' := by
  rintro ⟨hs, -⟩
  have hn : (3 : Nat) < 1 := hs 0 (mutCell v w) (mutRes_zero v w)
  omega

end BoCa.Fig16.RebExample

namespace BoCa.Fig16.BoLo

/-!
### Lemma 6.130 — literal reading

The printed statement, the printed proof and the adjudication are in `Paper/S6_6_ReborrowingEntailments/Lemmas.lean`, under the record of Lemma 6.130.
-/
/-- **The added hypothesis is not free.**  `RebExample`'s `mut` witness is
`ℓ₀ ↦ mut(3, v, ℓ₁ ↦ own(w), −)`, whose borrow does not outlive `α = 1`, and
`RebExample.not_reb_of_at` refuses it *every* `ρ′` — `∅` with the rest.  So
`↻_1 emp` does not reach this resource, while `⊤` does, and 6.130's hypothesis
is what separates them.
`[about ours: a resource outside `Res_α`, measured against `↻_α emp`]` -/
theorem reborrow_emp_outside_stratum (v w : Nat) :
    ¬ reborrow 1 (emp : SPropU Nat Nat) (RebExample.mutRes v w) := by
  rintro ⟨ρ', hr, -⟩
  exact RebExample.not_reb_of_at v w ρ' hr

end BoCa.Fig16.BoLo

end
