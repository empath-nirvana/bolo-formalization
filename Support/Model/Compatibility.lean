import Paper.S5_Model.Definitions
import Support.Model.Cells
import Support.Model.Composition
import Support.Model.Prelude
import Support.Model.WalkSplitting

/-!
# Support — Model — Compatibility

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
cell-level compatibility read off tags, values and witnesses, and `○` at an `imm` cell.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- **`▶◀` is exactly "two `imm` cells that agree up to lifetimes".**  `[TR]`
p. 5's defining equation binds one `v` and one `ρ` across two `imm` cells and
leaves the two lifetime sets free, so `▶◀` says precisely: both tags are `imm`,
the values agree, the witnesses agree.  Left to right is `CellU.CompatS.kinds`
and `CellU.CompatS.imm_imm`; right to left rebuilds both cells through
`CellU.rep`.  Every "agree up to lifetimes" in `[TR]` §6.1 is this.
`[about ours: `CellU.erase` and `CellU.wit` are this file's projections; what
the equivalence says is the printed phrase "agree up to lifetimes"]` -/
theorem CellU.compatS_iff {ψ₁ ψ₂ : CellU Loc Val} :
    CellU.CompatS ψ₁ ψ₂ ↔
      (ψ₁.kind = Kind.imm ∧ ψ₂.kind = Kind.imm ∧
        ψ₁.erase = ψ₂.erase ∧ ψ₁.wit = ψ₂.wit) := by
  constructor
  · rintro ⟨s₁, s₂, v, ρ, k₁, k₂, rfl, rfl⟩
    exact ⟨rfl, rfl, rfl, by rw [CellU.wit_immOf, CellU.wit_immOf]⟩
  · rintro ⟨k₁, k₂, hv, hw⟩
    rcases CellU.rep ψ₁ with ⟨v₁, rfl⟩ | ⟨s₁, v₁, τ₁, m₁, rfl⟩ |
        ⟨b₁, v₁, τ₁, m₁, P₁, w₁, rfl⟩
    · exact absurd k₁ (by simp)
    · rcases CellU.rep ψ₂ with ⟨v₂, rfl⟩ | ⟨s₂, v₂, τ₂, m₂, rfl⟩ |
          ⟨b₂, v₂, τ₂, m₂, P₂, w₂, rfl⟩
      · exact absurd k₂ (by simp)
      · rw [CellU.erase_immOf, CellU.erase_immOf] at hv
        rw [CellU.wit_immOf, CellU.wit_immOf] at hw
        subst hv; subst hw
        exact ⟨s₁, s₂, v₁, τ₁, m₁, m₂, rfl, rfl⟩
      · exact absurd k₂ (by simp)
    · exact absurd k₁ (by simp)

/-- **`○` hands an `imm` operand back as an `imm` cell over the same value and
the same witness.**  Only four clauses admit an `imm` cell on the left — (1),
(2) and the two halves of (5) — and each returns either that cell or its `●`
with another `imm` cell over the same witness.  This is 6.12's case (1) and
6.14's "the resulting composites still agree on overlapping imm cells up to
lifetimes", at the cell level; it is also what carries an `imm` cell of `ρ`
through the two `○`s of `ag(ρ)`. -/
theorem CellU.CompR.imm_left {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompR ψ₁ ψ₂ ψ)
    (hk : ψ₁.kind = Kind.imm) :
    ψ.kind = Kind.imm ∧ ψ.erase = ψ₁.erase ∧ ψ.wit = ψ₁.wit := by
  cases h with
  | same χ => exact ⟨hk, rfl, rfl⟩
  | strict k =>
      have hc := CellU.compS_spec _ _ k
      exact ⟨CellU.CompS.kind hc, (CellU.CompS.erase hc).1, (CellU.CompS.wit hc).1⟩
  | mutMut => exact absurd hk (by simp)
  | mutOwn => exact absurd hk (by simp)
  | ownMut => exact absurd hk (by simp)
  | immOwn => exact ⟨rfl, rfl, rfl⟩
  | ownImm => exact absurd hk (by simp)
  | immMut => exact ⟨rfl, rfl, rfl⟩
  | mutImm => exact absurd hk (by simp)

/-- **Which operand a `○` composite takes its witness from.**  The composite is
`own` only when both operands are, so where it is not, at least one operand is
not `own` and the composite carries that operand's witness.  This is the
bookkeeping 6.14's "the same value and subresource inside of it" needs, since
`CellU.CompR.wit` compares two operands only when neither is `own`. -/
theorem CellU.CompR.wit_of_ne_own {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompR ψ₁ ψ₂ ψ)
    (hk : ψ.kind ≠ Kind.own) :
    (ψ₁.kind ≠ Kind.own ∧ ψ.wit = ψ₁.wit) ∨ (ψ₂.kind ≠ Kind.own ∧ ψ.wit = ψ₂.wit) := by
  cases h with
  | same χ => exact Or.inl ⟨hk, rfl⟩
  | strict k =>
      exact Or.inl ⟨by rw [(CellU.CompatS.kinds k).1]; simp,
        (CellU.CompS.wit (CellU.compS_spec _ _ k)).1⟩
  | mutMut a b v τ ha hb P Q hP hQ =>
      exact Or.inl ⟨by simp,
        (CellU.wit_mutOf _ _ _ _ _ _).trans (CellU.wit_mutOf a v τ ha P hP).symm⟩
  | mutOwn => exact Or.inl ⟨by simp, rfl⟩
  | ownMut => exact Or.inr ⟨by simp, rfl⟩
  | immOwn => exact Or.inl ⟨by simp, rfl⟩
  | ownImm => exact Or.inr ⟨by simp, rfl⟩
  | immMut => exact Or.inl ⟨by simp, rfl⟩
  | mutImm => exact Or.inr ⟨by simp, rfl⟩

/-- **The cell level of `[TR]` Lemma 6.12.**  A cell `▶◀` the left operand of a
`○` is `▶◀` the value of that `○`.  `▶◀` forces that operand to be `imm`, and
`CellU.CompR.imm_left` then keeps the value and the witness fixed.
`[about ours: the cell-level step `[TR]` Lemma 6.12's proof takes at a location
where both `ρ₂` and `ρ₃` are defined]` -/
theorem CellU.CompatS.of_compR_left {χ ψ₁ ψ₂ ψ : CellU Loc Val}
    (h : CellU.CompatS χ ψ₁) (hc : CellU.CompR ψ₁ ψ₂ ψ) : CellU.CompatS χ ψ := by
  obtain ⟨k, k₁, hv, hw⟩ := CellU.compatS_iff.mp h
  obtain ⟨m₁, m₂, m₃⟩ := CellU.CompR.imm_left hc k₁
  exact CellU.compatS_iff.mpr ⟨k, m₁, hv.trans m₂.symm, hw.trans m₃.symm⟩

end BoCa.Fig16

end
