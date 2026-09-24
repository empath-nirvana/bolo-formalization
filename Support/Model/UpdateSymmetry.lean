import Paper.S5_Model.Definitions
import Paper.S6_2_NonStandardLemmas.Lemmas
import Support.Model.Update

/-!
# Support — Model — UpdateSymmetry

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
`↭` is symmetric, and `ρ ↭ ρ` read off validity.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

theorem ResU.UpdV.symm {ρ₁ ρ₂ : ResU Loc Val} (h : ρ₁.UpdV ρ₂) : ρ₂.UpdV ρ₁ :=
  ⟨h.1.symm, h.2.2, h.2.1⟩

/-- **What `[TR]`'s guard does to Lemma 6.47.**  At `[TR]` p. 5's `↭`, `ρ ↭ ρ`
is exactly `✓ρ`: both clauses are trivially true of a resource and itself, so all
that `ρ ↭ ρ` says is the guard.  6.47 prints `ρ ↭ ρ` with no hypothesis, and that
unconditional statement is the one `[CONF]` Fig. 18b's unguarded row supports.
`[about ours: what the divergence between the two printed rows costs at
Lemma 6.47]` -/
theorem ResU.updV_self_iff (ρ : ResU Loc Val) : ρ.UpdV ρ ↔ ρ.Valid :=
  ⟨fun h => h.2.1, fun h => ⟨ResU.Upd.refl ρ, h, h⟩⟩

end BoCa.Fig16

end
