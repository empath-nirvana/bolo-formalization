import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S4_LogicalRelation.Definitions
import Paper.S5_Model.Definitions
import Support.Model.Notation
import Support.Model.Propositions
import Support.Statics.Contexts

/-!
# Support — LogicalRelation — Facts

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
`⌜p⌝ ⋆ P` and the context relation read pointwise.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-- `(⌜p⌝ ⋆ P)(ρ) ⟺ p ∧ P(ρ)`.
`[about ours: `⋆` at `[TR]` p. 6's own `⌜⌝` row, read at the graph]` -/
theorem pure_sep_iff {p : Prop} {P : WProp} {ρ : WRes} : (⌜p⌝ ⋆ P) ρ ↔ (p ∧ P ρ) := by
  constructor
  · rintro ⟨ρ₁, ρ₂, hc, ⟨rfl, hp⟩, hP⟩
    rw [eq_of_compS_empty_left hc]
    exact ⟨hp, hP⟩
  · rintro ⟨hp, hP⟩
    exact ⟨PMap.empty, ρ, compS_empty_left ρ, ⟨rfl, hp⟩, hP⟩

theorem pure_sep_mk {p : Prop} {P : WProp} {ρ : WRes} (hp : p) (hP : P ρ) :
    (⌜p⌝ ⋆ P) ρ := pure_sep_iff.mpr ⟨hp, hP⟩

theorem gDen_iff {δ : LSub} {Γ : Ctx Ty} {γ : List Val} {ρ : WRes} :
    gDen δ Γ γ ρ ↔ (Ctx.LiveWithin Γ γ ∧ gSep δ Γ γ ρ) := pure_sep_iff

end BoCa.Fig16.LogRel

end
