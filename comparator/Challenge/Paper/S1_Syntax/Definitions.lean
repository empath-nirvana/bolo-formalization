
/-!
Verbatim from `Paper/S1_Syntax/Definitions.lean`: the declarations of that file the judged statement
reaches (see `comparator/Challenge.lean`), with their namespaces and `open`s.
-/

noncomputable section

namespace BoCa

abbrev Loc := Nat

/-- The four nullary productions of `[TR]` p. 1's `Prim`; `store v` is row 1.15. -/
inductive Prim where
  | alloc | free | load | store
  deriving DecidableEq, Repr

/-- `[TR]` p. 1's `Expr`, carrying its `Val` productions (`e ::= v`, row 1.17). -/
inductive Expr where
  | var     (i : Nat)                 -- x
  | unit                              -- ()
  | pair    (e₁ e₂ : Expr)            -- (e₁,e₂)
  | inj₁    (e : Expr)
  | inj₂    (e : Expr)
  | lam     (body : Expr)             -- λx.e, and Λ.e ≜ λ_.e
  | loc     (ℓ : Loc)                 -- ℓ
  /-- `p` at one of the four nullary `Prim` productions. -/
  | prim    (p : Prim)
  | seq     (e₁ e₂ : Expr)            -- e₁ ; e₂
  | letpair (e₁ e₂ : Expr)            -- let (x,y) = e₁; e₂   — binds 2 (y = 0, x = 1)
  | case    (e e₁ e₂ : Expr)          -- case e {inj₁ x. e₁, inj₂ x. e₂} — binds 1 each
  | app     (f a : Expr)              -- e₂ e₁
  deriving Repr

/-- `[TR]` p. 1's `Val`, as the subset of `Expr` its production `e ::= v` makes
    it: one clause per printed `Val` production, `Λ.e` folded into `λx.e`
    (row 1.8) and `store v` as the application the grammar derives it as.
    `[about ours]` -/
inductive IsVal : Expr → Prop where
  | unit                                                  : IsVal .unit
  | pair {a b : Expr} (h₁ : IsVal a) (h₂ : IsVal b)       : IsVal (.pair a b)
  | inj₁ {a : Expr} (h : IsVal a)                         : IsVal (.inj₁ a)
  | inj₂ {a : Expr} (h : IsVal a)                         : IsVal (.inj₂ a)
  | lam {b : Expr}                                        : IsVal (.lam b)
  | loc {ℓ : Loc}                                         : IsVal (.loc ℓ)
  | prim {p : Prim}                                       : IsVal (.prim p)
  | storeV {a : Expr} (h : IsVal a)                       : IsVal (.app (.prim .store) a)

/-- `Val ⊆ Expr`. -/
abbrev Val := {e : Expr // IsVal e}

end BoCa

namespace BoCa.Val

def unit : Val := ⟨.unit, .unit⟩

def pair (v w : Val) : Val := ⟨.pair v.1 w.1, .pair v.2 w.2⟩

def inj₁ (v : Val) : Val := ⟨.inj₁ v.1, .inj₁ v.2⟩

def inj₂ (v : Val) : Val := ⟨.inj₂ v.1, .inj₂ v.2⟩

def lam (body : Expr) : Val := ⟨.lam body, .lam⟩

def loc (ℓ : Loc) : Val := ⟨.loc ℓ, .loc⟩

def prim (p : Prim) : Val := ⟨.prim p, .prim⟩

end BoCa.Val

namespace BoCa

/-- `[TR]` p. 1's production `e ::= v`: the inclusion. -/
abbrev Expr.val (v : Val) : Expr := v.1

end BoCa

namespace BoCa.Lifetime

abbrev LifeVar := Nat

inductive Life where
  /-- `'a`. -/
  | var (a : LifeVar)
  /-- `⊤`. -/
  | top
  /-- `@a ⊔ @b`. -/
  | join (a b : Life)
  /-- `@a ⊓ @b`. -/
  | meet (a b : Life)
  deriving DecidableEq, Repr, Inhabited

structure LifeCtx where
  entries : List (LifeVar × Life)
  deriving Repr, DecidableEq, Inhabited

end BoCa.Lifetime

namespace BoCa
open BoCa.Lifetime

/-- `all` is `∀`; the name avoids the keyword. -/
inductive Ty where
  | unit
  | sum    (T₁ T₂ : Ty)
  | tensor (T₁ T₂ : Ty)
  | lolli  (T₁ T₂ : Ty)
  | ref    (T : Ty)
  /-- `Imm @a T`. -/
  | imm    (a : Life) (T : Ty)
  /-- `Mut @a T`. -/
  | mut    (a : Life) (T : Ty)
  /-- `[@a] T`. -/
  | box    (a : Life) (T : Ty)
  /-- `∀'x ⊏ @b. T`. -/
  | all    (x : LifeVar) (b : Life) (T : Ty)
  /-- `Unk`. -/
  | unk
  deriving DecidableEq, Repr, Inhabited

end BoCa

end
