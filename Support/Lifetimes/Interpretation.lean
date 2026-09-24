import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Support.Lifetimes.Terms

/-!
# Support — Lifetimes — Interpretation

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
extension of a lifetime interpretation `δ` by one variable.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa.Lifetime.LSub

def extend (δ : LSub) (x : LifeVar) (v : Nat) : LSub := ⟨(x, v) :: δ.entries⟩

theorem find?_extend (δ : LSub) (x : LifeVar) (v : Nat) (y : LifeVar) :
    (δ.extend x v).find? y = if x = y then some v else δ.find? y := by
  simp [find?, extend, assocFind]

end BoCa.Lifetime.LSub

end
