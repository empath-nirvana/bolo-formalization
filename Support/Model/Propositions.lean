import Paper.S1_Syntax.Definitions
import Paper.S5_Model.Definitions
import Support.Model.Algebra
import Support.Model.Composition

/-!
# Support — Model — Propositions

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
the propositions of `[TR]` p. 6 as used by §6.2: entailment, `emp`, the outlives relation `@ρ ⊐ α` and the `wp` row at the unguarded `↭`.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

theorem emp_empty : (emp : SPropU Loc Val) PMap.empty := ⟨rfl, trivial⟩

/-- `∅ ● ρ = ρ` — `[TR]` Lemma 6.4 with the operands transposed, which Lemma 6.2
licenses.  `[as printed]` -/
theorem compS_empty_left (ρ : ResU Loc Val) : ResU.CompS PMap.empty ρ ρ :=
  ResU.CompS.comm (ResU.comp_empty_right ρ)

theorem eq_of_compS_empty_left {ρ₂ ρ : ResU Loc Val} (h : ResU.CompS PMap.empty ρ₂ ρ) :
    ρ = ρ₂ :=
  ResU.CompS.functional h (compS_empty_left ρ₂)

/-- **`ℓ ↦M_α P̂` is inhabited exactly where the cell is.**  The printed
equation `ρ = ℓ ↦ mut(β, v, ρ′, P̂)` pins the cell's own invariant, so the `P̂` a
`mut` cell can be seen through is `ofS Q̂` for the cell's own
`Q̂ : Val → SProp_β`, and every such cell exhibits one. -/
theorem ptoMut_of_cell (l : Loc) (α b : Life) (hb : α ⊑ b) (v : Val)
    (σ : ResU Loc Val) (h : σ.InStratum b) (Q : Val → SPropS Loc Val b)
    (hw : Q v ⟨σ, h⟩) :
    ptoMut l α (ofS Q) (ResU.single l (CellU.mutOf b v σ h Q hw)) :=
  ⟨b, v, σ, h, Q, hw, hb, rfl, rfl⟩

end BoCa.Fig16.BoLo

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-- The composite `#` asserts is defined is valid, wherever it is named.
`[about ours: the second conjunct of the printed `#`, read at a named
composite]` -/
theorem hash_valid_comp {ρ₁ ρ₂ σ : WRes} (h : ResU.Hash ρ₁ ρ₂)
    (hc : ResU.CompS ρ₁ ρ₂ σ) : ResU.Valid σ := by
  obtain ⟨x, hx, hv⟩ := h.2
  cases ResU.CompS.functional hx hc
  exact hv

end BoCa.Fig16.BoLo

end
