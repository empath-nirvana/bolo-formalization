import Paper.S1_Syntax.Definitions

/-!
# Support — Syntax — Terms

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
value inversion lemmas, shifting and substitution on de Bruijn terms (single and parallel), and the names of `[TR]` p. 3's derived forms and of the first de Bruijn variables.  Declaration names are the source repository's (`borrow_lang` at
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

/-- A value whose root is an application is `store v`: its function part is the
    primitive `store` and its argument is a value. -/
theorem IsVal.app_fun {f a : Expr} (h : IsVal (.app f a)) : f = .prim .store := by
  cases h; rfl

theorem IsVal.app_arg {f a : Expr} (h : IsVal (.app f a)) : IsVal a := by
  cases h; assumption

@[simp] theorem isVal_app_iff {f a : Expr} :
    IsVal (.app f a) ↔ f = .prim .store ∧ IsVal a :=
  ⟨fun h => ⟨h.app_fun, h.app_arg⟩, fun h => h.1 ▸ .storeV h.2⟩

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

end BoCa

namespace BoCa.Val

/-- The inclusion lands in `IsVal`, at the spelling `Expr.val v` rather than
    `v.val`, so that `h ▸ Val.isVal v` rewrites where a term was written with
    the inclusion. -/
theorem isVal (v : Val) : IsVal (Expr.val v) := v.2

end BoCa.Val

namespace BoCa

def load'  : Expr := .val (.prim .load)

def store' : Expr := .val (.prim .store)

def unit' : Expr := .val .unit

def v0 : Expr := .var 0

def v1 : Expr := .var 1

def v2 : Expr := .var 2

def v3 : Expr := .var 3

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
