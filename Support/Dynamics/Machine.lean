import Paper.S1_Syntax.Definitions
import Paper.S3_Dynamics.Definitions

/-!
# Support — Dynamics — Machine

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
the machines' plumbing: frame composition, the reflexive-transitive closure `→*`, and heap deletion.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa.TR3.Kont
open BoCa.BoLo (Heap)

/-- `K ∘ K'`, so that `(K ∘ K')[e] = K[K'[e]]`. -/
def comp : Kont → Kont → Kont
  | .hole,         K' => K'
  | .pairL K e₂,   K' => .pairL (comp K K') e₂
  | .pairR v K,    K' => .pairR v (comp K K')
  | .letpair K e₂, K' => .letpair (comp K K') e₂
  | .case K e₁ e₂, K' => .case (comp K K') e₁ e₂
  | .appR f K,     K' => .appR f (comp K K')
  | .appL K v,     K' => .appL (comp K K') v

end BoCa.TR3.Kont

namespace BoCa.TR3
open BoCa.BoLo (Heap)

/-- `→*`, the reflexive-transitive closure `[TR]` §6.7 writes `⟶*`. -/
inductive Steps : Heap → Expr → Heap → Expr → Prop where
  | refl (μ : Heap) (e : Expr) : Steps μ e μ e
  | more {μ μ₁ μ' : Heap} {e e₁ e' : Expr}
      (h : Step1 μ e μ₁ e₁) (t : Steps μ₁ e₁ μ' e') : Steps μ e μ' e'

end BoCa.TR3

namespace BoCa.BoLo.Kont
open BoCa.Lifetime

/-- `K ∘ K'`, so that `K[K'[e]] = (K ∘ K')[e]`. -/
def comp : Kont → Kont → Kont
  | .hole,          K' => K'
  | .pairL K e₂,    K' => .pairL (comp K K') e₂
  | .pairR v K,     K' => .pairR v (comp K K')
  | .letpair K e₂,  K' => .letpair (comp K K') e₂
  | .case K e₁ e₂,  K' => .case (comp K K') e₁ e₂
  | .appR f K,      K' => .appR f (comp K K')
  | .appL K v,      K' => .appL (comp K K') v
  | .seq K e₂,      K' => .seq (comp K K') e₂
  | .inj₁ K,        K' => .inj₁ (comp K K')
  | .inj₂ K,        K' => .inj₂ (comp K K')

end BoCa.BoLo.Kont

namespace BoCa.BoLo
open BoCa.Lifetime

/-- `↦*`. -/
inductive Steps : Heap → Expr → Heap → Expr → Prop where
  | refl (μ : Heap) (e : Expr) : Steps μ e μ e
  | more {μ μ₁ μ' : Heap} {e e₁ e' : Expr}
      (h : Step1 μ e μ₁ e₁) (t : Steps μ₁ e₁ μ' e') : Steps μ e μ' e'

end BoCa.BoLo

end
