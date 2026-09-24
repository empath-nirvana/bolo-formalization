
/-!
Verbatim from `Paper/S1_Syntax/Definitions.lean`: the declarations of that file the judged statement
reaches (see `comparator/Challenge.lean`), with their namespaces and `open`s.
-/

noncomputable section

namespace BoCa

abbrev Loc := Nat

/-- The four NULLARY productions of `[TR]` p. 1's `Prim`.  The fifth,
    `store v`, is `store` applied to `v` — `Prim ∋ p ::= … ∣ store v`
    and `Expr ∋ e ::= … ∣ e₂ e₁` derive the same string, and the grammar
    identifies them, so `store v` is `Expr.app (.prim .store) v` and `IsVal`
    says it is a value (`Val.storeV`). -/
inductive Prim where
  | alloc | free | load | store
  deriving DecidableEq, Repr

/-- `[TR]` p. 1's `Expr`, carrying its `Val` productions too — the grammar is
    one grammar and `e ::= v` says so. -/
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
    it.  The eight clauses are the eight printed `Val` productions, `Λ.e` folded
    into `λx.e` and `p` split by whether the `Prim` production carries a value:
    `prim` at the four nullary schemes, `storeV` at `store v`, which is the
    application the grammar derives it as. -/
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

/-- `[TR]` p. 1's production `e ::= v` — the INCLUSION, not a constructor. -/
abbrev Expr.val (v : Val) : Expr := v.1

end BoCa

namespace BoCa.Lifetime

/-- Lifetime variables.  Nat-indexed rather than named: freshness (`LifeCtx.freshVar`) is then
    "one more than the largest in scope", and the pretty-printer recovers
    `'a`, `'b`, … for the tests. -/
abbrev LifeVar := Nat

/-- `Life`, verbatim from the grammar. -/
inductive Life where
  /-- `'a` — a lifetime variable.  ([TR] prints `'`; §12.8.) -/
  | var (a : LifeVar)
  /-- `⊤` — the longest lifetime. -/
  | top
  /-- `@a ⊔ @b` — join: the *longer* of the two. -/
  | join (a b : Life)
  /-- `@a ⊓ @b` — meet: the *shorter* of the two. -/
  | meet (a b : Life)
  deriving DecidableEq, Repr, Inhabited

structure LifeCtx where
  entries : List (LifeVar × Life)
  deriving Repr, DecidableEq, Inhabited

end BoCa.Lifetime

namespace BoCa
open BoCa.Lifetime

/-- `T ::= 1 | T₁ ⊕ T₂ | T₁ ⊗ T₂ | T₁ ⊸ T₂ | Ref T | Imm @a T | Mut @a T
          | [@a]T | ∀'a ⊏ @b. T | Unk`.

    `all` is `∀`; the name avoids the keyword.  Its binder is *named* (a
    `LifeVar`) rather than de Bruijn, because `Life` has no binding structure
    of its own and the paper's own `∀'a ⊏ @b. T` is named. -/
inductive Ty where
  | unit
  | sum    (T₁ T₂ : Ty)
  | tensor (T₁ T₂ : Ty)
  | lolli  (T₁ T₂ : Ty)
  | ref    (T : Ty)
  /-- `Imm @a T` — an immutable borrow at lifetime `@a`. -/
  | imm    (a : Life) (T : Ty)
  /-- `Mut @a T` — a **mutable** borrow at lifetime `@a` ([CONF] Fig. 9,
      p. 415:10; [TR] §1 p. 1).  "If we keep mutation, we can still keep
      `forget` as long as we drop `dupl`, a combination that is called a
      mutable borrow" ([CONF] p. 415:10).

      So the *type* is the same shape as `Imm`, and everything about it is in
      what the operations do **not** offer: there is no `copy` at `Mut`, which
      is what makes it exclusive. -/
  | mut    (a : Life) (T : Ty)
  /-- `[@a] T` — the outlives modality at lifetime `@a`. -/
  | box    (a : Life) (T : Ty)
  /-- `∀'x ⊏ @b. T`. -/
  | all    (x : LifeVar) (b : Life) (T : Ty)
  /-- `Unk` — the distinguished unknown of §2.4 ([TR] §1 p. 1; [CONF] Fig. 8).
      "there is *no* view at which it would be safe to access the payload, so
      we map these types to a new, distinguished unknown type, `Unk`, for which
      the only operation that is defined is `forget`" ([CONF] p. 415:9). -/
  | unk
  deriving DecidableEq, Repr, Inhabited

end BoCa

end
