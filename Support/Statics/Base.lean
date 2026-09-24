import Support.Syntax

/-!
# Support — Statics — Base

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
context plumbing for the typing judgment.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa
open BoCa.Lifetime

/-- `Γ = Γ₁, Γ₂` — a genuine partition of the live slots, positions preserved.
    Exchange is free (positions are independent), weakening and contraction are
    not expressible. -/
inductive Ctx.Split {τ : Type} : Ctx τ → Ctx τ → Ctx τ → Prop where
  | nil : Ctx.Split [] [] []
  | left  {Γ Γ₁ Γ₂ : Ctx τ} {T : τ} : Ctx.Split Γ Γ₁ Γ₂ →
      Ctx.Split (⟨T, true⟩ :: Γ) (⟨T, true⟩ :: Γ₁) (⟨T, false⟩ :: Γ₂)
  | right {Γ Γ₁ Γ₂ : Ctx τ} {T : τ} : Ctx.Split Γ Γ₁ Γ₂ →
      Ctx.Split (⟨T, true⟩ :: Γ) (⟨T, false⟩ :: Γ₁) (⟨T, true⟩ :: Γ₂)
  | dead  {Γ Γ₁ Γ₂ : Ctx τ} {T : τ} : Ctx.Split Γ Γ₁ Γ₂ →
      Ctx.Split (⟨T, false⟩ :: Γ) (⟨T, false⟩ :: Γ₁) (⟨T, false⟩ :: Γ₂)

end BoCa

end
