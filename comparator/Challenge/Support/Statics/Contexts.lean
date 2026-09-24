
/-!
Verbatim from `Support/Statics/Contexts.lean`: the declarations of that file the judged statement
reaches (see `comparator/Challenge.lean`), with their namespaces and `open`s.
-/

noncomputable section

namespace BoCa

structure Slot (τ : Type) where
  ty   : τ
  live : Bool
  deriving Repr, DecidableEq, Inhabited

abbrev Ctx (τ : Type) := List (Slot τ)

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
