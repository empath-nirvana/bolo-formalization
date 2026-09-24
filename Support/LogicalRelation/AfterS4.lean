import Paper.S1_Syntax.Definitions
import Paper.S4_LogicalRelation.Definitions
import Paper.S5_Model.Definitions
import Support.Syntax

/-!
# Support — LogicalRelation — AfterS4

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
facts about the logical relation used by later sections.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-- `Δ; Γ ⊨ e : T` as a proposition: a persistent proposition holds exactly when
it holds of `∅`. -/
noncomputable def Sem (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty) : Prop :=
  SemTy Δ Γ e T PMap.empty

end BoCa.Fig16.LogRel

end
