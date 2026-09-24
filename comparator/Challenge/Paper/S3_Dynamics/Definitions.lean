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
  | seq     (K : Kont) (e : Expr)        -- `K; e`      (row 3.30)
  | inj₁    (K : Kont)                   -- `inj₁ K`    (row 3.31)
  | inj₂    (K : Kont)                   -- `inj₂ K`    (row 3.31)
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

abbrev Heap := Loc → Option Val

end BoCa.BoLo

namespace BoCa.BoLo.Heap
open BoCa.Lifetime

/-- `μ` with `ℓ` removed, the result of `free↦`.  `[about ours]` -/
def del (μ : Heap) (ℓ : Loc) : Heap := fun k => if k = ℓ then none else μ k

/-- `μ[ℓ ↦ v]`. -/
def upd (μ : Heap) (ℓ : Loc) (v : Val) : Heap := fun k => if k = ℓ then some v else μ k

end BoCa.BoLo.Heap

namespace BoCa.BoLo
open BoCa.Lifetime

/-- The head reductions of `[TR]` p. 4's `↦` box: `TR3.Head` under other names. -/
inductive Head : Heap → Expr → Heap → Expr → Prop where
  | beta (μ : Heap) (b : Expr) (v : Val) :
      Head μ (.app (.val (.lam b)) (.val v)) μ (b.subst 0 v)
  | alloc (μ : Heap) (v : Val) (ℓ : Loc) (h : μ ℓ = none) :
      Head μ (.app (.val (.prim .alloc)) (.val v)) (μ.upd ℓ v) (.val (.loc ℓ))
  | free (μ : Heap) (ℓ : Loc) (v : Val) (h : μ ℓ = some v) :
      Head μ (.app (.val (.prim .free)) (.val (.loc ℓ))) (μ.del ℓ) (.val v)
  | load (μ : Heap) (ℓ : Loc) (v : Val) (h : μ ℓ = some v) :
      Head μ (.app (.val (.prim .load)) (.val (.loc ℓ))) μ (.val v)
  /-- `store↦` -/
  | store (μ : Heap) (ℓ : Loc) (v w : Val) (h : μ ℓ = some w) :
      Head μ (.app (.app (.val (.prim .store)) (.val (.loc ℓ))) (.val v))
        (μ.upd ℓ v) (.val .unit)
  /-- `1↦` -/
  | seq (μ : Heap) (e : Expr) : Head μ (.seq (.val .unit) e) μ e
  | letpair (μ : Heap) (v₁ v₂ : Val) (e : Expr) :
      Head μ (.letpair (.val (.pair v₁ v₂)) e) μ ((e.subst 0 (v₂.shift 1 0)).subst 0 v₁)
  | case₁ (μ : Heap) (v : Val) (e₁ e₂ : Expr) :
      Head μ (.case (.val (.inj₁ v)) e₁ e₂) μ (e₁.subst 0 v)
  | case₂ (μ : Heap) (v : Val) (e₁ e₂ : Expr) :
      Head μ (.case (.val (.inj₂ v)) e₁ e₂) μ (e₂.subst 0 v)

/-- `(μ,e) ↦ (μ',e')  ⟹  (μ, K[e]) → (μ', K[e'])`. -/
def Step1 (μ : Heap) (e : Expr) (μ' : Heap) (e' : Expr) : Prop :=
  ∃ (K : Kont) (a a' : Expr), e = K.plug a ∧ e' = K.plug a' ∧ Head μ a μ' a'

end BoCa.BoLo

namespace BoCa

def copy : Expr := .val (.lam (.pair v0 v0))

def forget : Expr := .val (.lam unit')

def elet (e : Expr) (body : Expr) : Expr := .app (.val (.lam body)) e

def lam2 (body : Expr) : Expr := .val (.lam (.val (.lam body)))

/-- De Bruijn: under `λx λf`, `x = 1`, `f = 0`; the `letpair` pushes `y = 1`,
    `z = 0`, shifting them to `x = 3`, `f = 2`. -/
def withswap : Expr :=
  lam2 (.letpair (.app v0 (.app load' v1))
         (.seq (.app (.app store' v3) v1)
               (.pair v3 v0)))

end BoCa

end
