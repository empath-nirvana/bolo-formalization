import Paper.S1_Syntax.Definitions
import Paper.S5_Model.Definitions
import Support.Syntax

/-!
# Support — LogicalRelation — AfterS5

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
the pieces of the logical relation that are not printed clauses: closing substitutions and free lifetime variables.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.MutImmGap
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont)

theorem empty_inStratum (b : Life) :
    ResU.InStratum (Loc := BoCa.Loc) (Val := BoCa.Val) b PMap.empty :=
  fun _ _ e => absurd e (by simp)

end BoCa.Fig16.LogRel.MutImmGap

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-- `γ(e)` — `BoCa/Subst.lean`'s parallel substitution, for the reason
`BoCa/LogRel.lean` convention L5 gives: a fold of `Expr.subst 0` is the closing
substitution only for a closed `γ`. -/
def substAll (γ : List Val) (e : Expr) : Expr := Expr.psub 0 γ e

/-- `'x` occurs free in `T`, with `∀'y ⊏ @b. T` binding `'y` in `T` and **not**
in `@b` — the binder's own bound is in the outer scope.  `𝒱⟦T⟧δ` reads `δ` only
at these variables, which is what lets a capture-avoiding renaming move the
binder: the new name is chosen outside them. -/
def LFree (x : LifeVar) : Ty → Prop
  | .unit          => False
  | .unk           => False
  | .ref T         => LFree x T
  | .imm a T       => a.mentions x = true ∨ LFree x T
  | .mut a T       => a.mentions x = true ∨ LFree x T
  | .box a T       => a.mentions x = true ∨ LFree x T
  | .sum T₁ T₂     => LFree x T₁ ∨ LFree x T₂
  | .tensor T₁ T₂  => LFree x T₁ ∨ LFree x T₂
  | .lolli T₁ T₂   => LFree x T₁ ∨ LFree x T₂
  | .all y b T     => b.mentions x = true ∨ (x ≠ y ∧ LFree x T)

end BoCa.Fig16.LogRel

end
