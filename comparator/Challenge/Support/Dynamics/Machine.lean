import Challenge.Paper.S1_Syntax.Definitions
import Challenge.Paper.S2_Statics.Definitions
import Challenge.Paper.S3_Dynamics.Definitions
import Challenge.Support.Statics.Contexts
import Challenge.Support.Syntax.Terms

/-!
Verbatim from `Support/Dynamics/Machine.lean`: the declarations of that file the judged statement
reaches (see `comparator/Challenge.lean`), with their namespaces and `open`s.
-/

noncomputable section

namespace BoCa.BoLo
open BoCa.Lifetime

/-- `↦*`. -/
inductive Steps : Heap → Expr → Heap → Expr → Prop where
  | refl (μ : Heap) (e : Expr) : Steps μ e μ e
  | more {μ μ₁ μ' : Heap} {e e₁ e' : Expr}
      (h : Step1 μ e μ₁ e₁) (t : Steps μ₁ e₁ μ' e') : Steps μ e μ' e'

end BoCa.BoLo

end
