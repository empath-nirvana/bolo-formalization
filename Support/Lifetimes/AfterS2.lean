import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions

/-!
# Support — Lifetimes — AfterS2

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
lifetime-substitution plumbing used after the statics.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa.Lifetime.LSub

def extend (δ : LSub) (x : LifeVar) (v : Nat) : LSub := ⟨(x, v) :: δ.entries⟩

end BoCa.Lifetime.LSub

end
