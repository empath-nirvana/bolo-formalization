/-!
# [TR] §1 Syntax  (physical p. 1)

    Var     ∋ x, y, …
    Loc     ∋ ℓ
    Val     ∋ v  ::= () ∣ (v₁, v₂) ∣ inj₁ v ∣ inj₂ v ∣ λx.e ∣ Λ.e ∣ ℓ ∣ p
    Prim    ∋ p  ::= alloc ∣ free ∣ load ∣ store ∣ store v
    Expr    ∋ e  ::= x ∣ v ∣ (e₁, e₂) ∣ inj₁ e ∣ inj₂ e ∣ e₁ ; e₂ ∣ let (x, y) = e₁ in e₂
                   ∣ case e {inj₁ x.e₁ ∣ inj₂ y.e₂} ∣ e₂ e₁
    LifeVar ∋ 'a, 'b, …
    Life    ∋ @a, @b, … ::= ' ∣ ⊤ ∣ @a ⊔ @b ∣ @a ⊓ @b
    LifeCtx ∋ Δ  : LifeVar ⇀ Life
    Type    ∋ T  ::= 1 ∣ T₁ ⊕ T₂ ∣ T₁ ⊗ T₂ ∣ T₁ ⊸ T₂ ∣ Ref T ∣ [@a] T
                   ∣ Imm @a T ∣ Mut @a T ∣ ∀ 'a ⊏ @b. T ∣ Unk

`e ::= v` makes values a subset of expressions, and they are one here: a single
`Expr`, the predicate `IsVal` picking out the value forms, and `Val` the subtype.
`Λ.e` is `λ_.e` (row 1.8) and `store v` is `store` applied to `v` (row 1.15).

**How this file reads.**  Each printed item is a row of `[TR]`'s section, in the
order the page prints it, as far as Lean's definition-before-use allows; a row
that has to come earlier than printed does so because something printed before
it is defined through it.  Each row opens with a comment giving its number, the
printed form, the page, a tag, and the reason the Lean has the shape it has:

* `[as printed]` — the Lean is the printed item, symbol for symbol;
* `[encoding]` — it differs only by a representation choice that changes nothing
  (de Bruijn indices, a graph for a partial function, a list for a finite map);
* `[repair]` — it deliberately differs, and the comment gives the adjudication
  and the sentences of the paper that ground it;
* `[about ours]` — a declaration the paper does not print, placed here only
  because Lean needs it before the next printed row.

Row numbers are those of `Paper/INDEX.md` (*Definitions*); `§N` citations are
to `docs/adjudications.md`.
-/

noncomputable section

namespace BoCa

/-!
### 1.2 · `Loc ∋ ℓ` · [TR] p. 1 · `[encoding]`

A countably infinite name supply as `Nat` — but the declaration is an `abbrev`, hence reducible, so `BoCa.Loc`, `BoCa.Lifetime.LifeVar` and the semantic lifetime carrier are all definitionally `Nat`: three sorts p. 1 prints as distinct that Lean cannot tell apart
-/
abbrev Loc := Nat

/-!
### 1.11 · `Prim ∋ p ::= alloc` · [TR] p. 1 · `[as printed]`

Nullary constructor

### 1.12 · `Prim ::= … ∣ free` · [TR] p. 1 · `[as printed]`

Nullary constructor

### 1.13 · `Prim ::= … ∣ load` · [TR] p. 1 · `[as printed]`

Nullary constructor

### 1.14 · `Prim ::= … ∣ store` · [TR] p. 1 · `[as printed]`

Nullary constructor
-/
/-- The four NULLARY productions of `[TR]` p. 1's `Prim`.  The fifth,
    `store v`, is `store` applied to `v` — `Prim ∋ p ::= … ∣ store v`
    and `Expr ∋ e ::= … ∣ e₂ e₁` derive the same string, and the grammar
    identifies them, so `store v` is `Expr.app (.prim .store) v` and `IsVal`
    says it is a value (`Val.storeV`). -/
inductive Prim where
  | alloc | free | load | store
  deriving DecidableEq, Repr

/-!
### 1.1 · `Var ∋ x, y, …` · [TR] p. 1 · `[encoding]`

De Bruijn indices for names; capture-freedom is `BoCa.Expr.shift`/`BoCa.Expr.subst`, and `BoCa.Ctx.Solo` recovers `x : T`

### 1.16 · `Expr ∋ e ::= x` · [TR] p. 1 · `[encoding]`

De Bruijn index; the `i < c` cutoff in `BoCa.Expr.shift` and `i = j` in `BoCa.Expr.subst` are the standard discipline

### 1.18 · `Expr ::= … ∣ (e₁, e₂)` · [TR] p. 1 · `[as printed]`

Binary, both fields `Expr`

### 1.19 · `Expr ::= … ∣ inj₁ e` · [TR] p. 1 · `[as printed]`

Unary over `Expr`; [TR] p. 2's ⊕I prints the term as `i e`, the same former

### 1.20 · `Expr ::= … ∣ inj₂ e` · [TR] p. 1 · `[as printed]`

Unary over `Expr`

### 1.21 · `Expr ::= … ∣ e₁ ; e₂` · [TR] p. 1 · `[as printed]`

Binary, non-binding; matches [TR] p. 2's 1E term

### 1.22 · `Expr ::= … ∣ let (x, y) = e₁ in e₂` · [TR] p. 1 · `[encoding]`

De Bruijn, binding two in the body (`y` = 0, `x` = 1): `BoCa.Expr.shift` uses `c+2` and `BoCa.Expr.subst` uses `j+2` there, and `BoCa.Derives.tensorE` pushes `T₂` then `T₁`. [TR] p. 2's ⊗E prints the same form with `;` for `in` — the paper disagreeing with itself, not the Lean

### 1.23 · `Expr ::= … ∣ case e {inj₁ x.e₁ ∣ inj₂ y.e₂}` · [TR] p. 1 · `[encoding]`

De Bruijn, binding one in each branch. [TR] p. 2's ⊕E prints `match es {x₁ ⇒ e₁, x₂ ⇒ e₂}` for the same former — again the paper against itself

### 1.24 · `Expr ::= … ∣ e₂ e₁` · [TR] p. 1 · `[as printed]`

One binary application node, as printed; the constructor's fields are (function, argument) where the production's subscripts number the argument first, which is premise-ordering only. [TR] p. 2's ⊸E contradicts this production (see row 2.10)
-/
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

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
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

/-- No expression form outside the eight printed `Val` productions is a value. -/
@[simp] theorem not_isVal_var {i : Nat} : ¬ IsVal (.var i) := fun h => nomatch h

@[simp] theorem not_isVal_seq {a b : Expr} : ¬ IsVal (.seq a b) := fun h => nomatch h

@[simp] theorem not_isVal_letpair {a b : Expr} : ¬ IsVal (.letpair a b) := fun h => nomatch h

@[simp] theorem not_isVal_case {a b c : Expr} : ¬ IsVal (.case a b c) := fun h => nomatch h

/-- `Val ⊆ Expr`. -/
abbrev Val := {e : Expr // IsVal e}

end BoCa

namespace BoCa.Val

/-!
### 1.3 · `Val ∋ v ::= ()` · [TR] p. 1 · `[as printed]`

Nullary: `BoCa.Expr.unit` carrying its `BoCa.IsVal` proof, so its `.val` IS that expression (row 1.17)
-/
def unit : Val := ⟨.unit, .unit⟩

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
@[simp] theorem val_unit : (Val.unit).val = Expr.unit := rfl

/-!
### 1.4 · `Val ::= … ∣ (v₁, v₂)` · [TR] p. 1 · `[as printed]`

Binary, both fields `Val` — not `Expr`, matching the printed metavariables — and its `.val` is `BoCa.Expr.pair` of the two projections by `rfl`, which is the identification row 1.17 makes
-/
def pair (v w : Val) : Val := ⟨.pair v.1 w.1, .pair v.2 w.2⟩

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
@[simp] theorem val_pair (v w : Val) : (Val.pair v w).val = .pair v.val w.val := rfl

/-!
### 1.5 · `Val ::= … ∣ inj₁ v` · [TR] p. 1 · `[as printed]`

Field is `Val`, as printed
-/
def inj₁ (v : Val) : Val := ⟨.inj₁ v.1, .inj₁ v.2⟩

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
@[simp] theorem val_inj₁ (v : Val) : (Val.inj₁ v).val = .inj₁ v.val := rfl

/-!
### 1.6 · `Val ::= … ∣ inj₂ v` · [TR] p. 1 · `[as printed]`

Field is `Val`, as printed
-/
def inj₂ (v : Val) : Val := ⟨.inj₂ v.1, .inj₂ v.2⟩

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
@[simp] theorem val_inj₂ (v : Val) : (Val.inj₂ v).val = .inj₂ v.val := rfl

/-!
### 1.7 · `Val ::= … ∣ λx.e` · [TR] p. 1 · `[encoding]`

De Bruijn: the binder is dropped, the body is an `Expr` as the printed `λx.e`'s is; `BoCa.Val.shift`/`BoCa.Val.subst` push under it at `c+1`

### 1.8 · `Val ::= … ∣ Λ.e` · [TR] p. 1 · `[repair]`

Two printed-distinct value formers become one term. `BoCa.Derives.lolliI` and `BoCa.Derives.allI` conclude about the same `.val (.lam e)`, and `BoCa.Derives.allE` types `.app e (.val .unit)`, which `BoCa.Derives.lolliE` also types at `T₁ = 1`: typing is syntax-directed at neither λ nor application, and every inversion on those shapes carries both cases. [TR] p. 2's ∀I prints the term as `Λ.e`, so the print does keep them apart. Adjudicated at `docs/adjudications.md` §12.14, with the consequence at §12.27: the print cannot be taken as printed, since [TR] p. 2's ∀E concludes `e[]`, a term in no `Expr` production and in no ↦ rule, while [TR] p. 4's own `𝒱⟦∀ 'a ⊏ @b. T⟧δ(v) ≜ ∀ α ⊏ @bδ. ℰ⟦T⟧δ(v ())` applies `v` to `()`, which only ⊸↦ reduces — so a `Λ.e` kept distinct from `λ` never steps. [CONF] p. 415:8 says outright that `Λ.e` is shorthand for `λ_.e`, and the authority used is [TR] p. 4 against [TR] p. 1, not [CONF] Fig. 1
-/
def lam (body : Expr) : Val := ⟨.lam body, .lam⟩

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
@[simp] theorem val_lam (b : Expr) : (Val.lam b).val = .lam b := rfl

/-!
### 1.9 · `Val ::= … ∣ ℓ` · [TR] p. 1 · `[as printed]`

Locations are values, as printed; substitution leaves them alone
-/
def loc (ℓ : Loc) : Val := ⟨.loc ℓ, .loc⟩

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
@[simp] theorem val_loc (ℓ : Loc) : (Val.loc ℓ).val = .loc ℓ := rfl

/-- The value formers are injective, being the `Expr` formers.  `loc` is the
    one the test fixtures read heaps back through; the others follow the same
    way from `Val.ext`. -/
@[simp] theorem loc_inj {ℓ k : Loc} : Val.loc ℓ = Val.loc k ↔ ℓ = k :=
  ⟨fun h => Expr.loc.inj (congrArg Subtype.val h), fun h => h ▸ rfl⟩

/-!
### 1.10 · `Val ::= … ∣ p` · [TR] p. 1 · `[encoding]`

The production ranges over the five `Prim` schemes, one of which carries a value; Lean splits it by exactly that. `BoCa.Val.prim` takes the four nullary schemes and `BoCa.Val.storeV` is `store v` (row 1.15), which is the application `(store) v` the same grammar derives — so the split adds no term former, and `BoCa.Prim` keeps its `DecidableEq` by staying outside `BoCa.Expr`. The split changes nothing: the two together are in bijection with the printed production's instances, and no value outside the five schemes exists
-/
def prim (p : Prim) : Val := ⟨.prim p, .prim⟩

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
@[simp] theorem val_prim (p : Prim) : (Val.prim p).val = .prim p := rfl

/-!
Row 1.10, continued.

### 1.15 · `Prim ::= … ∣ store v` · [TR] p. 1 · `[encoding]`

The fifth production, at the term the printed grammar derives it as: `store v` is `Prim ::= … ∣ store v` and the application `e₂ e₁` at once, and a paper grammar identifies the two, so `BoCa.Val.storeV` at `v` is `.app (.prim .store) v` with the `BoCa.IsVal` clause that makes it a value (row 1.17). `BoCa.BoLo.Head.store`, `BoCa.TR3.Head.store` and the `wp` store rules are stated at it, so the store dynamics is stated at the printed value AND at the printed application, those being one term. [CONF] Fig. 1 is captioned "(excerpts)" and prints neither this production nor [TR] p. 1's `Val ::= … ∣ Λ.e`
-/
def storeV (v : Val) : Val := ⟨.app (.prim .store) v.1, .storeV v.2⟩

/-! `[about ours]` — what Lean needs before the next printed definition; the paper prints nothing here. -/
@[simp] theorem val_storeV (v : Val) :
    (Val.storeV v).val = .app (.prim .store) v.val := rfl

end BoCa.Val

namespace BoCa

/-!
### 1.17 · `Expr ::= … ∣ v` · [TR] p. 1 · `[encoding]`

The print makes `Val` a SUBSET of `Expr`: `(v₁,v₂)` is derivable through `v` and through the pair production, and the two derivations name one term. Named choice: ONE inductive `BoCa.Expr` carrying the value formers, an inductively defined `BoCa.IsVal` over it, and `BoCa.Val`, the subtype `{e // IsVal e}`, with `BoCa.Expr.val` the inclusion `e ::= v` — a projection, not a constructor — so `Expr.val (Val.pair v₁ v₂) = Expr.pair (Expr.val v₁) (Expr.val v₂)` holds by `rfl` and the two derivations ARE one term. The subtype rather than a bare predicate because the paper quantifies over values as a type — [TR] p. 1's `Mem ∋ μ : Loc ⇀ Val`, p. 6's `P̂ : Val → SProp` — and that is what `BoCa.BoLo.Heap`, `BoCa.BoLo.wp` and `BoCa.Fig16.LogRel.vDen` are stated at.
-/
/-- `[TR]` p. 1's production `e ::= v` — the INCLUSION, not a constructor. -/
abbrev Expr.val (v : Val) : Expr := v.1

end BoCa

namespace BoCa.Lifetime

/-!
### 1.25 · `LifeVar ∋ 'a, 'b, …` · [TR] p. 1 · `[encoding]`

Nat-indexed names, so freshness is "one past the largest in scope" (`BoCa.Ty.lifeBound`) and `BoCa.Lifetime.varName` pretty-prints `'a, 'b, …`. Same reducible-`Nat` collision as row 1.2
-/
/-- Lifetime variables.  Nat-indexed rather than named: freshness (`LifeCtx.freshVar`) is then
    "one more than the largest in scope", and the pretty-printer recovers
    `'a`, `'b`, … for the tests. -/
abbrev LifeVar := Nat

/-!
### 1.26 · `Life ∋ @a, @b… ::= '` · [TR] p. 1 · `[encoding]`

p. 1 prints a BARE apostrophe with no variable; Lean reads it as `'a`, a `LifeVar`. Forced — on the literal reading `Life` has no variables and `LifeVar`, `LifeCtx : LifeVar ⇀ Life`, `∀'a ⊏ @b.T` and ⟦Δ⟧ all go vacuous; [CONF] Fig. 7 (p. 415:8) prints `'a` and [TR] p. 3's `@aδ` has the case `@a = 'a`. A repair of the print, not a representation change (`docs/adjudications.md` §12.8)

### 1.27 · `Life ::= … ∣ ⊤` · [TR] p. 1 · `[as printed]`

Nullary; the syntactic ⊤, distinct from the semantic `BoCa.Fig16.Life.top`, which is 0

### 1.28 · `Life ::= … ∣ @a ⊔ @b` · [TR] p. 1 · `[as printed]`

Binary only, as printed — there is no n-ary join, which is why [TR] p. 3's `⊓Δ` is meta-notation (row 2.59)

### 1.29 · `Life ::= … ∣ @a ⊓ @b` · [TR] p. 1 · `[as printed]`

Binary only, as printed. Four constructors against four productions — no extra, no ⊥
-/
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

/-!
### 1.30 · `LifeCtx ∋ Δ : LifeVar ⇀ Life` · [TR] p. 1 · `[encoding]`

Association list for the finite partial map, innermost binding wins (`BoCa.Lifetime.assocFind`), so duplicate keys shadow and the denotation is still a function; `BoCa.Lifetime.LifeCtx.Models` only ever consults lookup, so shadowed entries are invisible to ⟦Δ⟧. Two restrictions the print does not state: the map is finite, and `BoCa.Lifetime.LifeCtx.dom` is a list that may repeat. The codomain is the SYNTACTIC `Life`, as printed — unlike `LSub` at row 2.51
-/
structure LifeCtx where
  entries : List (LifeVar × Life)
  deriving Repr, DecidableEq, Inhabited

end BoCa.Lifetime

namespace BoCa
open BoCa.Lifetime

/-!
### 1.31 · `Type ∋ T ::= 𝟙` · [TR] p. 1 · `[as printed]`

Nullary; distinct from `BoCa.Val.unit` despite the shared name

### 1.32 · `Type ::= … ∣ T₁ ⊕ T₂` · [TR] p. 1 · `[as printed]`

Binary

### 1.33 · `Type ::= … ∣ T₁ ⊗ T₂` · [TR] p. 1 · `[as printed]`

Binary

### 1.34 · `Type ::= … ∣ T₁ ⊸ T₂` · [TR] p. 1 · `[as printed]`

Binary linear arrow

### 1.35 · `Type ::= … ∣ Ref T` · [TR] p. 1 · `[as printed]`

Unary, carries no lifetime — as printed, and the reason `Ref` is the owned type

### 1.36 · `Type ::= … ∣ [@a] T` · [TR] p. 1 · `[as printed]`

`Life` then `Ty`, matching the printed argument order

### 1.37 · `Type ::= … ∣ Imm @a T` · [TR] p. 1 · `[as printed]`

`Life` then `Ty`. Not the metafunction `Imm̲` of [TR] p. 3, which is row 2.49

### 1.38 · `Type ::= … ∣ Mut @a T` · [TR] p. 1 · `[as printed]`

Same shape as `imm`, as printed; the exclusivity is entirely in which operations exist, not in the type

### 1.39 · `Type ::= … ∣ ∀ 'a ⊏ @b. T` · [TR] p. 1 · `[as printed]`

Named binder, as the print's own binder is named; the bound glyph is a bare ⊏ (strict), matching `BoCa.Derives.allE`'s use of `BoCa.Lifetime.LifeCtx.EntailsLt`. Capture is avoided by `BoCa.Ty.applyLSub`'s freshening branch, which is ours (row 1.43)

### 1.40 · `Type ::= … ∣ Unk` · [TR] p. 1 · `[as printed]`

Nullary. Ten productions against ten constructors — no extra, none missing
-/
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
