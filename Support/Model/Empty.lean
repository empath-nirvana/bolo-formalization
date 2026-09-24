import Paper.S1_Syntax.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Support.Model.Prelude
import Support.Model.WalkSplitting

/-!
# Support — Model — Empty

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
the walks and restrictions of the empty resource.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps)

/-- `∅` has an aliasable walk. -/
theorem agW_empty : AgW (PMap.empty : WRes) PMap.empty := by
  have hre : ∀ k, ResU.restrict (PMap.empty : WRes) k = PMap.empty := fun k =>
    PMap.ext fun l => ResU.restrict_get_none (PMap.empty_get l)
  have hsites : ∀ k, ResU.Sites (PMap.empty : WRes) k ([] : List BoCa.Loc) :=
    fun _ => ⟨List.nodup_nil, fun _ =>
      ⟨fun h => absurd h (by simp), by rintro ⟨ψ, e, -⟩; cases e⟩⟩
  refine AgW.mk (wm := []) (wi := []) (a := PMap.empty) (bm := PMap.empty)
    (bi := PMap.empty) (hsites _) (hsites _) AgWitsM.nil AgWitsI.nil
    BigComp.nil BigComp.nil ?_ (ResU.comp_empty_right _)
  rw [hre]; exact ResU.comp_empty_right _

end BoCa.Fig16.BoLo

namespace BoCa.DefectB
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)

theorem restrict_empty (k : Kind) :
    ResU.restrict (PMap.empty : ResU Nat BoCa.Val) k = PMap.empty :=
  PMap.ext fun l => ResU.restrict_get_none (PMap.empty_get l)

theorem agW_empty : AgW (PMap.empty : ResU Nat BoCa.Val) PMap.empty := by
  refine AgW.mk (wm := []) (wi := []) (a := PMap.empty) (bm := PMap.empty)
    (bi := PMap.empty) ?_ ?_ AgWitsM.nil AgWitsI.nil BigComp.nil BigComp.nil
    ?_ (ResU.comp_empty_right _)
  · exact ⟨List.nodup_nil, fun l => ⟨fun h => absurd h (by simp),
      by rintro ⟨ψ, e, -⟩; cases e⟩⟩
  · exact ⟨List.nodup_nil, fun l => ⟨fun h => absurd h (by simp),
      by rintro ⟨ψ, e, -⟩; cases e⟩⟩
  · rw [restrict_empty]; exact ResU.comp_empty_right _

end BoCa.DefectB

end
