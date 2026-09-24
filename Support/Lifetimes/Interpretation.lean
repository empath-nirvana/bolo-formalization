import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions

/-!
# Support — Lifetimes — Interpretation

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
extension of a lifetime interpretation `δ` by one variable.
-/

noncomputable section

namespace BoCa.Lifetime.LSub

def extend (δ : LSub) (x : LifeVar) (v : Nat) : LSub := ⟨(x, v) :: δ.entries⟩

end BoCa.Lifetime.LSub

end
