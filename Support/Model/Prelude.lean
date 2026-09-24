import Mathlib

/-!
# Support — Model — Prelude

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
the carrier's prelude: `min`/`max` arithmetic, the finite-domain predicate, casts, bundled bijections, and the index `ι ∈ {own, imm, mut}` of `ρ∣ι`.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa.Fig16

theorem minLeL (a b : Nat) : min a b ≤ a := by omega

theorem minLeR (a b : Nat) : min a b ≤ b := by omega

theorem leMaxL (a b : Nat) : a ≤ max a b := by omega

theorem leMaxR (a b : Nat) : b ≤ max a b := by omega

/-- `f` has finite domain: some list of locations covers it. -/
def FinDom {Loc A : Type} (f : Loc → Option A) : Prop :=
  ∃ d : List Loc, ∀ l, f l ≠ none → l ∈ d

theorem cast_left {A B : Type} (h : A = B) (x : A) : cast h.symm (cast h x) = x := by
  cases h; rfl

theorem cast_right {A B : Type} (h : A = B) (y : B) : cast h (cast h.symm y) = y := by
  cases h; rfl

/-- Ours: a bijection, bundled.  Proof apparatus, not the paper's. -/
structure Equiv (A B : Type) where
  /-- The forward map. -/
  toFun : A → B
  /-- The inverse. -/
  invFun : B → A
  /-- `invFun ∘ toFun = id`. -/
  leftInv : ∀ a, invFun (toFun a) = a
  /-- `toFun ∘ invFun = id`. -/
  rightInv : ∀ b, toFun (invFun b) = b

/-- `ι ∈ {own, mut, imm}` (`[TR]` p. 5, in `ρ|ι`). -/
inductive Kind where
  /-- `own`. -/
  | own
  /-- `imm`. -/
  | imm
  /-- `mut`. -/
  | mut
  deriving DecidableEq

end BoCa.Fig16

end
