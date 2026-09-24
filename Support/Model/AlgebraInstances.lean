import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Support.Model.Algebra
import Support.Model.Composition
import Support.Model.Prelude

/-!
# Support — Model — AlgebraInstances

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
Lemmas 6.2 and 6.3 at `○`, Lemmas 6.41 and 6.42 as one statement, and the lifetime of a `●` composite.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- `[TR]` Lemma 6.2 at `○`.  `[as printed]` -/
theorem ResU.CompR.comm {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompR ρ₁ ρ₂ ρ) :
    ResU.CompR ρ₂ ρ₁ ρ :=
  ResU.Comp.comm (fun _ _ a => a.symm) (fun _ _ _ a => a.comm) h

/-- `[TR]` Lemma 6.3 at `○`.  `[as printed]` -/
theorem ResU.CompR.assoc (ρ₁ ρ₂ ρ₃ w : ResU Loc Val) :
    (∃ x, ResU.CompR ρ₂ ρ₃ x ∧ ResU.CompR ρ₁ x w) ↔
    (∃ y, ResU.CompR ρ₁ ρ₂ y ∧ ResU.CompR y ρ₃ w) :=
  ResU.Comp.assoc (fun _ _ ψ h => ⟨ψ, h⟩)
    (fun ψ₁ ψ₂ ψ₃ ω => CellU.compR_assoc ψ₁ ψ₂ ψ₃ ω) ρ₁ ρ₂ ρ₃ w

/-- **`[TR]` Lemmas 6.41 and 6.42** (p. 15): if `ℓ ↦ own(−) ▶◀ ρ` — resp.
`ℓ ↦ mut(−,−,−,−) ▶◀ ρ` — then `ℓ ∉ ρ`.  One theorem for any cell whose tag is
not `imm`; `hk` names the cell the print fixes.  The print states two lemmas,
so by the inventory preamble's rule the `[as printed]` tag sits on the two
instances below, not here.
`[variant: 6.41 and 6.42 stated once for any cell whose tag is not `imm`; the
printed instances are `ResU.compatS_single_own` and `ResU.compatS_single_mut`]`
-/
theorem ResU.compatS_single_not_imm {l : Loc} {ψ : CellU Loc Val} {ρ : ResU Loc Val}
    (hk : ψ.kind ≠ Kind.imm) (h : ResU.CompatS (ResU.single l ψ) ρ) : ρ.get l = none := by
  cases e : ρ.get l with
  | none => rfl
  | some χ =>
      exact absurd (CellU.CompatS.kinds (h l ψ χ (ResU.single_get_self l ψ) e)).1 hk

/-- The lifetime of a strict composite is the meet of the two: `●` unions the
lifetime sets and `@` is their meet, so `@(ψ₁ ● ψ₂) = @ψ₁ ⊓ @ψ₂`.  This is the
cell-level content of `[TR]` Lemma 6.45.
`[about ours: the cell-level fact the resource-level 6.45 is proved from]` -/
theorem CellU.CompS.at {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompS ψ₁ ψ₂ ψ) :
    ψ.at = ψ₁.at ⊓ ψ₂.at := by
  obtain ⟨s₁, s₂, v, ρ, k₁, k₂, k₃, e₁, e₂, e₃⟩ := h
  subst e₁; subst e₂; subst e₃
  rfl

/-- **`Res_α` is preserved and reflected by `●`.**  All three cells are `imm`
(`CellU.CompS.kind`, `CellU.CompatS.kinds`), `@` of the composite is the meet of
the operands' (`CellU.CompS.at`), and a meet clears `α` exactly when both do.
This is the cell-level content of `[TR]` Lemma 6.45 at `[α]`'s own conjunct.
`[about ours: the cell-level fact the resource-level 6.45 is proved from]` -/
theorem CellU.CompS.inStratum {ψ₁ ψ₂ ψ : CellU Loc Val} (hC : CellU.CompS ψ₁ ψ₂ ψ)
    (α : Life) : ψ.InStratum α ↔ (ψ₁.InStratum α ∧ ψ₂.InStratum α) := by
  obtain ⟨s₁, s₂, v, σ, k₁, k₂, k₃, e₁, e₂, e₃⟩ := hC
  subst e₁; subst e₂; subst e₃
  exact Nat.max_lt

end BoCa.Fig16

end
