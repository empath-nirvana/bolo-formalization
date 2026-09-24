import Paper.S5_Model.Definitions
import Support.Model.Algebra
import Support.Model.Prelude
import Support.Model.Walks

/-!
# Support — Model — Flattening

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
validity and lowering: the pointwise facts behind Lemmas 6.7, 6.10 and 6.30, and the union of two memories.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- `dom(ρ₁ ◐ ρ₂) = dom(ρ₁) ∪ dom(ρ₂)`, pointwise and in the negative: a
composite is undefined at `ℓ` exactly when both operands are.  Read off `◐`'s
three pieces, so it holds at every guard and every cell-level operation.
`[about ours: the step "unfolding ○, dom(ρ₁ ○ ρ₂) = dom(ρ₁) ∪ dom(ρ₂)" of
`[TR]` Lemma 6.30's proof, at §12's schema and written pointwise, `dom` not
being an object on this carrier]` -/
theorem ResU.Comp.eq_none_iff {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.Comp R C ρ₁ ρ₂ ρ) (l : Loc) :
    ρ.get l = none ↔ (ρ₁.get l = none ∧ ρ₂.get l = none) := by
  rcases ResU.Comp.get h l with ⟨e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ |
      ⟨ψ₁, ψ₂, ψ, e₁, e₂, e, -⟩ <;> rw [e, e₁, e₂] <;> simp

/-- `ex(ρ₁)_● ● ex(ρ₂)_●` is `imm`-free: 6.36 (`ExS.immFree`, §18) at each
factor, and `●` cannot manufacture an `imm` cell out of two non-`imm` ones.
This is the side condition 6.35's proof hands to 6.30.
`[about ours: `ResU.ImmFree` is `[TR]` p. 5's `ρ|imm = ∅` written pointwise;
this closes it under `●`]` -/
theorem ResU.ImmFree.compS {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    (h₁ : ρ₁.ImmFree) (h₂ : ρ₂.ImmFree) : ρ.ImmFree :=
  ResU.ImmFree.comp (fun ψ₁ ψ₂ ψ hc k₁ _ => CellU.compS_ne_imm ψ₁ ψ₂ ψ hc k₁) h h₁ h₂

end BoCa.Fig16

end
