import Challenge.Paper.S1_Syntax.Definitions

/-!
Verbatim from `Support/Syntax/Terms.lean`: the declarations of that file the judged statement
reaches (see `comparator/Challenge.lean`), with their namespaces and `open`s.
-/

noncomputable section

namespace BoCa

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

def load'  : Expr := .val (.prim .load)

def store' : Expr := .val (.prim .store)

def unit' : Expr := .val .unit

def v0 : Expr := .var 0

def v1 : Expr := .var 1

def v2 : Expr := .var 2

def v3 : Expr := .var 3

end BoCa

end
