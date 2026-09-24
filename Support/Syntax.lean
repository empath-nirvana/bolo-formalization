import Paper.S1_Syntax.Definitions
import Support.Lifetimes.AfterS1

/-!
# Support — Syntax

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
substitution and shifting on de Bruijn terms, value inversion lemmas, and the pretty names of `[TR]` p. 3's derived forms.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa

theorem IsVal.pair_left {a b : Expr} (h : IsVal (.pair a b)) : IsVal a := by
  cases h; assumption

theorem IsVal.pair_right {a b : Expr} (h : IsVal (.pair a b)) : IsVal b := by
  cases h; assumption

@[simp] theorem isVal_pair_iff {a b : Expr} : IsVal (.pair a b) ↔ IsVal a ∧ IsVal b :=
  ⟨fun h => ⟨h.pair_left, h.pair_right⟩, fun h => .pair h.1 h.2⟩

theorem IsVal.inj₁_inv {a : Expr} (h : IsVal (.inj₁ a)) : IsVal a := by cases h; assumption

@[simp] theorem isVal_inj₁_iff {a : Expr} : IsVal (.inj₁ a) ↔ IsVal a :=
  ⟨IsVal.inj₁_inv, .inj₁⟩

theorem IsVal.inj₂_inv {a : Expr} (h : IsVal (.inj₂ a)) : IsVal a := by cases h; assumption

@[simp] theorem isVal_inj₂_iff {a : Expr} : IsVal (.inj₂ a) ↔ IsVal a :=
  ⟨IsVal.inj₂_inv, .inj₂⟩

def Expr.shift (d : Nat) (c : Nat) : Expr → Expr
  | .var i         => if i < c then .var i else .var (i + d)
  | .unit          => .unit
  | .pair e₁ e₂    => .pair (e₁.shift d c) (e₂.shift d c)
  | .inj₁ e        => .inj₁ (e.shift d c)
  | .inj₂ e        => .inj₂ (e.shift d c)
  | .lam b         => .lam (b.shift d (c + 1))
  | .loc ℓ         => .loc ℓ
  | .prim p        => .prim p
  | .seq e₁ e₂     => .seq (e₁.shift d c) (e₂.shift d c)
  | .letpair e₁ e₂ => .letpair (e₁.shift d c) (e₂.shift d (c + 2))
  | .case e e₁ e₂  => .case (e.shift d c) (e₁.shift d (c + 1)) (e₂.shift d (c + 1))
  | .app f a       => .app (f.shift d c) (a.shift d c)

theorem IsVal.shift {e : Expr} (h : IsVal e) (d c : Nat) : IsVal (e.shift d c) := by
  induction h generalizing c with
  | unit => exact .unit
  | pair _ _ ih₁ ih₂ => exact .pair (ih₁ c) (ih₂ c)
  | inj₁ _ ih => exact .inj₁ (ih c)
  | inj₂ _ ih => exact .inj₂ (ih c)
  | lam => exact .lam
  | loc => exact .loc
  | prim => exact .prim
  | storeV _ ih => simp only [Expr.shift]; exact .storeV (ih c)

def Val.shift (d : Nat) (c : Nat) (v : Val) : Val := ⟨v.1.shift d c, v.2.shift d c⟩

@[simp] theorem Val.val_shift (d c : Nat) (v : Val) :
    (Val.shift d c v).val = v.val.shift d c := rfl

def Expr.subst (j : Nat) (s : Val) : Expr → Expr
  | .var i         => if i = j then s.val else if i > j then .var (i - 1) else .var i
  | .unit          => .unit
  | .pair e₁ e₂    => .pair (e₁.subst j s) (e₂.subst j s)
  | .inj₁ e        => .inj₁ (e.subst j s)
  | .inj₂ e        => .inj₂ (e.subst j s)
  | .lam b         => .lam (b.subst (j + 1) (s.shift 1 0))
  | .loc ℓ         => .loc ℓ
  | .prim p        => .prim p
  | .seq e₁ e₂     => .seq (e₁.subst j s) (e₂.subst j s)
  | .letpair e₁ e₂ => .letpair (e₁.subst j s) (e₂.subst (j + 2) (s.shift 2 0))
  | .case e e₁ e₂  =>
      .case (e.subst j s) (e₁.subst (j + 1) (s.shift 1 0)) (e₂.subst (j + 1) (s.shift 1 0))
  | .app f a       => .app (f.subst j s) (a.subst j s)

theorem IsVal.subst {e : Expr} (h : IsVal e) (j : Nat) (s : Val) :
    IsVal (e.subst j s) := by
  induction h generalizing j s with
  | unit => exact .unit
  | pair _ _ ih₁ ih₂ => exact .pair (ih₁ j s) (ih₂ j s)
  | inj₁ _ ih => exact .inj₁ (ih j s)
  | inj₂ _ ih => exact .inj₂ (ih j s)
  | lam => exact .lam
  | loc => exact .loc
  | prim => exact .prim
  | storeV _ ih => simp only [Expr.subst]; exact .storeV (ih j s)

def Val.subst (j : Nat) (s : Val) (v : Val) : Val := ⟨v.1.subst j s, v.2.subst j s⟩

@[simp] theorem Val.val_subst (j : Nat) (s v : Val) :
    (Val.subst j s v).val = v.val.subst j s := rfl

def load'  : Expr := .val (.prim .load)

def store' : Expr := .val (.prim .store)

def unit' : Expr := .val .unit

def v0 : Expr := .var 0

def v1 : Expr := .var 1

def v2 : Expr := .var 2

def v3 : Expr := .var 3

end BoCa

namespace BoCa.Lifetime
open BoCa.Lifetime

/-- Does this lifetime mention the variable `x`? -/
def Life.mentions (x : LifeVar) : Life → Bool
  | .var y    => x == y
  | .top      => false
  | .join a b => a.mentions x || b.mentions x
  | .meet a b => a.mentions x || b.mentions x

/-- One past the largest variable index in a lifetime.  Used to choose a `∀`
    binder fresh for some collection of types. -/
def Life.varBound : Life → Nat
  | .var x    => x + 1
  | .top      => 0
  | .join a b => max a.varBound b.varBound
  | .meet a b => max a.varBound b.varBound

/-- A simultaneous substitution on lifetime variables. -/
abbrev LSubst := List (LifeVar × Life)

def Life.applySub (σ : LSubst) : Life → Life
  | .var x    => match assocFind x σ with
                 | some a => a
                 | none   => .var x
  | .top      => .top
  | .join a b => .join (a.applySub σ) (b.applySub σ)
  | .meet a b => .meet (a.applySub σ) (b.applySub σ)

end BoCa.Lifetime

namespace BoCa
open BoCa.Lifetime

/-- One past the largest lifetime index anywhere in `T`, binders included.
    Used to pick capture-avoiding renamings. -/
def Ty.lifeBound : Ty → Nat
  | .unit         => 0
  | .unk          => 0
  | .ref T        => T.lifeBound
  | .imm a T      => max a.varBound T.lifeBound
  | .mut a T      => max a.varBound T.lifeBound
  | .box a T      => max a.varBound T.lifeBound
  | .all x b T    => max (x + 1) (max b.varBound T.lifeBound)
  | .sum    T₁ T₂ => max T₁.lifeBound T₂.lifeBound
  | .tensor T₁ T₂ => max T₁.lifeBound T₂.lifeBound
  | .lolli  T₁ T₂ => max T₁.lifeBound T₂.lifeBound

/-- Would applying `σ` capture a free `'y`?  (`LSubst` is an abbreviation for a
    `List`, so these cannot be dot-notation methods.) -/
def lsubCaptures (σ : LSubst) (y : LifeVar) : Bool :=
  σ.any (fun p => p.2.mentions y)

/-- `σ` with the binding for `'y` removed — `'y` is shadowed. -/
def lsubDrop (σ : LSubst) (y : LifeVar) : LSubst :=
  σ.filter (fun p => p.1 != y)

/-- One past the largest variable index `σ` mentions, key or value. -/
def lsubRangeBound (σ : LSubst) : Nat :=
  σ.foldr (fun p acc => max (max (p.1 + 1) p.2.varBound) acc) 0

/-- `T` with the simultaneous lifetime substitution `σ` applied, renaming `∀`
    binders where necessary to avoid capture. -/
def Ty.applyLSub (σ : LSubst) : Ty → Ty
  | .unit         => .unit
  | .unk          => .unk
  | .ref T        => .ref (T.applyLSub σ)
  | .imm a T      => .imm (a.applySub σ) (T.applyLSub σ)
  | .mut a T      => .mut (a.applySub σ) (T.applyLSub σ)
  | .box a T      => .box (a.applySub σ) (T.applyLSub σ)
  | .sum    T₁ T₂ => .sum    (T₁.applyLSub σ) (T₂.applyLSub σ)
  | .tensor T₁ T₂ => .tensor (T₁.applyLSub σ) (T₂.applyLSub σ)
  | .lolli  T₁ T₂ => .lolli  (T₁.applyLSub σ) (T₂.applyLSub σ)
  | .all y b T    =>
      let σ' := lsubDrop σ y                    -- `'y` is shadowed inside `T`
      if lsubCaptures σ' y then
        let z := max (y + 1) (max (lsubRangeBound σ') T.lifeBound)
        .all z (b.applySub σ) (T.applyLSub ((y, Life.var z) :: σ'))
      else
        .all y (b.applySub σ) (T.applyLSub σ')

/-- `T[@a/'x]` — the substitution `∀E` performs. -/
def Ty.instLife (x : LifeVar) (a : Life) (T : Ty) : Ty := T.applyLSub [(x, a)]

structure Slot (τ : Type) where
  ty   : τ
  live : Bool
  deriving Repr, DecidableEq, Inhabited

abbrev Ctx (τ : Type) := List (Slot τ)

end BoCa

namespace BoCa

/-- `γ(e)` under `k` binders. -/
def Expr.psub (k : Nat) (γ : List Val) : Expr → Expr
  | .var i         =>
      if i < k then .var i
      else match γ[i - k]? with
           | some v => .val (v.shift k 0)
           | none   => .var (i - γ.length)
  | .unit          => .unit
  | .pair e₁ e₂    => .pair (Expr.psub k γ e₁) (Expr.psub k γ e₂)
  | .inj₁ e        => .inj₁ (Expr.psub k γ e)
  | .inj₂ e        => .inj₂ (Expr.psub k γ e)
  | .lam b         => .lam (Expr.psub (k + 1) γ b)
  | .loc ℓ         => .loc ℓ
  | .prim p        => .prim p
  | .seq e₁ e₂     => .seq (Expr.psub k γ e₁) (Expr.psub k γ e₂)
  | .letpair e₁ e₂ => .letpair (Expr.psub k γ e₁) (Expr.psub (k + 2) γ e₂)
  | .case e e₁ e₂  =>
      .case (Expr.psub k γ e) (Expr.psub (k + 1) γ e₁) (Expr.psub (k + 1) γ e₂)
  | .app f a       => .app (Expr.psub k γ f) (Expr.psub k γ a)

end BoCa

end
