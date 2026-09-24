import Paper.S5_Model.Definitions
import Support.Model.Prelude

/-!
# Support — Model — Singletons

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
restriction `ρ∣ι`, singleton resources `ℓ ↦ ψ`, the order `ρ ≤ ρ′`, and the walks and restrictions of singletons.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

theorem ResU.restrictOn_eq_some {ρ : ResU Loc Val} {p : Kind → Bool} {l : Loc}
    {ψ : CellU Loc Val} :
    (ρ.restrictOn p).get l = some ψ ↔ (ρ.get l = some ψ ∧ p ψ.kind = true) := by
  have hdef : (ρ.restrictOn p).get l
      = (ρ.get l).bind (fun ψ => if p ψ.kind then some ψ else none) := rfl
  rw [hdef]
  cases hf : ρ.get l with
  | none => simp
  | some ψ' =>
      simp only [Option.bind_some]
      by_cases hk : p ψ'.kind = true
      · rw [if_pos hk]
        exact ⟨fun he => by cases Option.some.inj he; exact ⟨rfl, hk⟩, fun he => he.1⟩
      · rw [if_neg hk]
        refine ⟨fun he => absurd he (by simp), fun he => ?_⟩
        cases Option.some.inj he.1
        exact absurd he.2 hk

end BoCa.Fig16

end
