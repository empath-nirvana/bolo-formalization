import Challenge.Paper.S1_Syntax.Definitions
import Challenge.Support.Syntax.Terms

/-!
Verbatim from `Paper/S3_Dynamics/Definitions.lean`: the declarations of that file the judged statement
reaches (see `comparator/Challenge.lean`), with their namespaces and `open`s.
The source also imports `Mathlib`; no declaration
copied here uses anything from it.
-/

noncomputable section

namespace BoCa.BoLo
open BoCa.Lifetime

/-- [TR] §3's evaluation contexts. -/
inductive Kont where
  | hole
  | pairL   (K : Kont) (e : Expr)        -- `(K, e)`
  | pairR   (v : Val)  (K : Kont)        -- `(v, K)`
  | letpair (K : Kont) (e : Expr)        -- `let (x,y) = K in e`
  | case    (K : Kont) (e₁ e₂ : Expr)    -- `case K {…}`
  | appR    (e : Expr) (K : Kont)        -- `e K`  — argument-first
  | appL    (K : Kont) (v : Val)         -- `K v`
  | seq     (K : Kont) (e : Expr)        -- `K; e`      (added, see above)
  | inj₁    (K : Kont)                   -- `inj₁ K`    (added)
  | inj₂    (K : Kont)                   -- `inj₂ K`    (added)
  deriving Repr

end BoCa.BoLo

namespace BoCa.BoLo.Kont
open BoCa.Lifetime

/-- `K[e]`. -/
def plug : Kont → Expr → Expr
  | .hole,          e => e
  | .pairL K e₂,    e => .pair (plug K e) e₂
  | .pairR v K,     e => .pair (.val v) (plug K e)
  | .letpair K e₂,  e => .letpair (plug K e) e₂
  | .case K e₁ e₂,  e => .case (plug K e) e₁ e₂
  | .appR f K,      e => .app f (plug K e)
  | .appL K v,      e => .app (plug K e) (.val v)
  | .seq K e₂,      e => .seq (plug K e) e₂
  | .inj₁ K,        e => .inj₁ (plug K e)
  | .inj₂ K,        e => .inj₂ (plug K e)

end BoCa.BoLo.Kont

namespace BoCa.BoLo
open BoCa.Lifetime

/-- A flat physical memory, `μ : Loc ⇀ Val` ([TR] §3). -/
abbrev Heap := Loc → Option Val

end BoCa.BoLo

namespace BoCa.BoLo.Heap
open BoCa.Lifetime

/-- `μ / ℓ` — [TR]'s `free` REMOVES the entry (`μ ⊎ [ℓ↦v] ↦ μ`), so a later
    `load` is genuinely stuck. -/
def del (μ : Heap) (ℓ : Loc) : Heap := fun k => if k = ℓ then none else μ k

/-- `μ[ℓ ↦ v]`. -/
def upd (μ : Heap) (ℓ : Loc) (v : Val) : Heap := fun k => if k = ℓ then some v else μ k

end BoCa.BoLo.Heap

namespace BoCa.BoLo
open BoCa.Lifetime

/-- The head reductions of [TR] §3 (the `↦` box of p. 4), read on heaps.
    `alloc` is NONDETERMINISTIC in the fresh location, as printed. -/
inductive Head : Heap → Expr → Heap → Expr → Prop where
  | beta (μ : Heap) (b : Expr) (v : Val) :
      Head μ (.app (.val (.lam b)) (.val v)) μ (b.subst 0 v)
  | alloc (μ : Heap) (v : Val) (ℓ : Loc) (h : μ ℓ = none) :
      Head μ (.app (.val (.prim .alloc)) (.val v)) (μ.upd ℓ v) (.val (.loc ℓ))
  | free (μ : Heap) (ℓ : Loc) (v : Val) (h : μ ℓ = some v) :
      Head μ (.app (.val (.prim .free)) (.val (.loc ℓ))) (μ.del ℓ) (.val v)
  | load (μ : Heap) (ℓ : Loc) (v : Val) (h : μ ℓ = some v) :
      Head μ (.app (.val (.prim .load)) (.val (.loc ℓ))) μ (.val v)
  /-- `store↦` — `[TR]` p. 4's `(µ, store ℓ v) ↦ (µ[ℓ ↦ v], ())`.  Its function
      part `store ℓ` is `[TR]` p. 1's value `store v`, which is the application
      `(store) ℓ`, so the printed left-hand side is this one term and no rule
      coerces between two spellings of it. -/
  | store (μ : Heap) (ℓ : Loc) (v w : Val) (h : μ ℓ = some w) :
      Head μ (.app (.app (.val (.prim .store)) (.val (.loc ℓ))) (.val v))
        (μ.upd ℓ v) (.val .unit)
  /-- `1↦` — `[TR]` p. 4 prints `(µ, (); e) ↦ (µ, e)`, at a literal `()` and not at
      an arbitrary value.  `1E` types `e₁; e₂` at `e₁ : 1` and `𝒱⟦1⟧` holds only of
      `()`, so nothing in the paper needs the wider rule. -/
  | seq (μ : Heap) (e : Expr) : Head μ (.seq (.val .unit) e) μ e
  | letpair (μ : Heap) (v₁ v₂ : Val) (e : Expr) :
      Head μ (.letpair (.val (.pair v₁ v₂)) e) μ ((e.subst 0 (v₂.shift 1 0)).subst 0 v₁)
  | case₁ (μ : Heap) (v : Val) (e₁ e₂ : Expr) :
      Head μ (.case (.val (.inj₁ v)) e₁ e₂) μ (e₁.subst 0 v)
  | case₂ (μ : Heap) (v : Val) (e₁ e₂ : Expr) :
      Head μ (.case (.val (.inj₂ v)) e₁ e₂) μ (e₂.subst 0 v)

/-- `(μ, K[e]) ↦ (μ', K[e'])` — one step.

    Stated as a `def` rather than an inductive family: the index `K[e]` is not a
    constructor application, so an inductive would need dependent elimination at
    every inversion, and there are many. -/
def Step1 (μ : Heap) (e : Expr) (μ' : Heap) (e' : Expr) : Prop :=
  ∃ (K : Kont) (a a' : Expr), e = K.plug a ∧ e' = K.plug a' ∧ Head μ a μ' a'

end BoCa.BoLo

namespace BoCa

/-- `copy ≜ λx. (x, x)`  — the conference paper calls it `dupl`
    (docs/boca-rules.md §12.21).  Uses the linear `x` twice. -/
def copy : Expr := .val (.lam (.pair v0 v0))

/-- `forget ≜ λx. ()`  — never uses `x`, so it needs weakening. -/
def forget : Expr := .val (.lam unit')

/-- `let x = e; body` is sugar for `(λx. body) e` — the grammar in Fig. 1 has no
    `let`, only `e₁; e₂` and `let (x,y) = e₁; e₂`. -/
def elet (e : Expr) (body : Expr) : Expr := .app (.val (.lam body)) e

def lam2 (body : Expr) : Expr := .val (.lam (.val (.lam body)))

/-- `withswap ≜ λx λf. let (y, z) = f (load x); store x y; (x, z)`.

    **Unlike `swap`, `withload` and `withbor`, this one is not a §12.20 case.**
    Verified at 900 dpi on both sources: [TR] p. 4 prints
    `λx.λf.let (y, z) = f (load x); store x y; (x, z)` and [CONF] **Fig. 15**
    (p. 415:17) prints the identical term, and it does match its ascribed type
    `Mut @a T₁ ⊸ (T₁ ⊸ T₁ ⊗ T₂) ⊸ (Mut @a T₁) ⊗ T₂` in both halves: the
    callback returns the pair `(y, z) : T₁ ⊗ T₂`, the *old* payload's
    replacement `y` is stored back, and the result `(x, z)` is the borrow
    together with `z : T₂`.  Note also that `f` is **not** a thunk here — the
    callback's type is a bare `⊸`, with no `∀` — so, unlike `withbor` and
    `withload`, there is no lifetime application to restore either.  Phases 4
    and 5 both had to take [CONF]'s version over [TR]'s; Phase 6 does not.

    It is ill-typed in the base system for the usual reasons: `x` is used three
    times, and `load`/`store` are marked `⊬` by [CONF] Fig. 3b (p. 415:4) and
    have no rule at all in [TR] p. 2.

    de Bruijn: under `λx λf` the binders are `x = 1`, `f = 0`; the `letpair`
    pushes `y = 1`, `z = 0` and shifts them to `x = 3`, `f = 2`. -/
def withswap : Expr :=
  lam2 (.letpair (.app v0 (.app load' v1))
         (.seq (.app (.app store' v3) v1)
               (.pair v3 v0)))

end BoCa

end
