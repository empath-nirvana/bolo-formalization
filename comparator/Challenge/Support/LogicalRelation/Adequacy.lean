import Challenge.Paper.S1_Syntax.Definitions
import Challenge.Paper.S2_Statics.Definitions
import Challenge.Paper.S3_Dynamics.Definitions
import Challenge.Support.Lifetimes.Terms
import Challenge.Support.Statics.Contexts
import Challenge.Support.Statics.Presupposed
import Challenge.Support.Syntax.Terms

/-!
Verbatim from `Support/LogicalRelation/Adequacy.lean`: the declarations of that file the judged statement
reaches (see `comparator/Challenge.lean`), with their namespaces and `open`s.
The source also imports `Paper.S4_LogicalRelation.Definitions`, `Paper.S5_Model.Definitions`, `Support.LogicalRelation.Facts`; no declaration
copied here uses anything from them.
-/

noncomputable section

namespace BoCa.Adequacy
-- The source block also opens `BoCa.Fig16` and `BoCa.Fig16.BoLo (wp NoOwn WRes)`,
-- the model, which is not replicated here; `emptyMem` uses neither.
open BoCa.BoLo (Heap)
open BoCa.Lifetime (LifeCtx LSub)

/-- `∅` on the memory side of `(∅, e) →* (∅, v)`: `[TR]` p. 3's
`Mem ∋ μ : Loc ⇀ Val` at the empty map.
`[about ours: the empty `μ` of `[TR]` p. 3's `Mem` row]` -/
def emptyMem : Heap := fun _ => none

end BoCa.Adequacy

end
