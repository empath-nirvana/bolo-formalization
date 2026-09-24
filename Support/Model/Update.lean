import Paper.S5_Model.Definitions
import Paper.S6_2_NonStandardLemmas.Definitions
import Support.Model.Prelude
import Support.Model.Singletons

/-!
# Support — Model — Update

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
the update relation `↭` at both printed readings, `reb_α` read at one location, and the form `[TR]` §6 unfolds `↭` to.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

theorem ResU.Upd.symm {ρ₁ ρ₂ : ResU Loc Val} (h : ρ₁.Upd ρ₂) : ρ₂.Upd ρ₁ :=
  ⟨fun l s v χ hs => (h.1 l s v χ hs).symm, fun l b P => (h.2 l b P).symm⟩

theorem CellU.Sim.symm {ψ ψ' : CellU Loc Val} (h : CellU.Sim ψ ψ') :
    CellU.Sim ψ' ψ := by
  rcases h with ⟨a, P, h₁, h₂⟩ | ⟨s, v, χ, hh, e₁, e₂⟩
  · exact Or.inl ⟨a, P, h₂, h₁⟩
  · exact Or.inr ⟨s, v, χ, hh, e₂, e₁⟩

theorem ResU.borrowPart_eq_some {ρ : ResU Loc Val} {l : Loc} {ψ : CellU Loc Val} :
    ρ.borrowPart.get l = some ψ ↔ (ρ.get l = some ψ ∧ ψ.kind ≠ Kind.own) := by
  rw [show ρ.borrowPart = ρ.restrictOn (fun k => !(k == Kind.own)) from rfl,
    ResU.restrictOn_eq_some]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa using h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by simpa using h2⟩

end BoCa.Fig16

end
