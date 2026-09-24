import Challenge.Paper.S1_Syntax.Definitions
import Challenge.Paper.S3_Dynamics.Definitions
import Challenge.Support.Lifetimes.Substitution
import Challenge.Support.Lifetimes.Terms
import Challenge.Support.Statics.Contexts
import Challenge.Support.Syntax.Terms

/-!
Verbatim from `Paper/S2_Statics/Definitions.lean`: the declarations of that file the judged statement
reaches (see `comparator/Challenge.lean`), with their namespaces and `open`s.
-/

noncomputable section

namespace BoCa
open BoCa.Lifetime

/-- `•` — every slot already consumed.  This is what `1I`, `ID`'s tail and the
    axiom table's unwritten `Γ` (§12.19) demand. -/
inductive Ctx.Dead {τ : Type} : Ctx τ → Prop where
  | nil                                   : Ctx.Dead []
  | cons {T : τ} {Γ : Ctx τ} : Ctx.Dead Γ → Ctx.Dead (⟨T, false⟩ :: Γ)

/-- `Γ = x : T`, with `x` at de Bruijn index `i` — `ID`'s context. -/
inductive Ctx.Solo {τ : Type} : Ctx τ → Nat → τ → Prop where
  | here  {T : τ} {Γ : Ctx τ} : Ctx.Dead Γ → Ctx.Solo (⟨T, true⟩ :: Γ) 0 T
  | there {S T : τ} {Γ : Ctx τ} {i : Nat} : Ctx.Solo Γ i T →
      Ctx.Solo (⟨S, false⟩ :: Γ) (i + 1) T

end BoCa

namespace BoCa

/-- `swap ≜ λx.λy₂. let y₁ = load x; store x y₂; (x, y₁)` — **[CONF] Fig. 3b**
    (p. 415:4), not [TR] p. 4.  §12.20.

    **The two documents print different bodies, and we follow [CONF].
    [variant: [CONF] Fig. 3b's body, not [TR] p. 4's.]**
    [TR] p. 4 prints `swap ≜ λx.λy. let z = load x; store x y; (x, y)`: `z` is
    bound and never used, and the pair returns `y`, the **new** payload, where
    the type ascribed on [TR] p. 3 — `Ref T₁ ⊸ T₂ ⊸ Ref T₂ ⊗ T₁` — makes the
    second component the **old** one.  [CONF] Fig. 2c (p. 415:4) is the
    decisive witness: `let x = alloc v; let (x′,y) = swap x (); free x′; y` is
    stated to return `v`, and it does so only under Fig. 3b's body.
    `Paper/Examples/Programs.lean` runs it (`BoCa.Programs.fig2c`).

    Three things matter about the term ([CONF] p. 415:5): it returns the
    reference as well as the payload, threading it so it can be reused; it
    permits a *strong update*, sound only because linearity guarantees the
    reference is unique; and its implementation is **ill-typed** — it uses the
    linear `x` three times — yet is semantically sound at the ascribed type.
    That last point is the seed of the whole approach: borrow operations are
    typed axiomatically and validated in the logic. -/
def swap : Expr :=
  lam2 (elet (.app load' v1)
             (.seq (.app (.app store' v2) v1)
                   (.pair v2 v0)))

end BoCa

namespace BoCa
open BoCa.Lifetime

/-- `Ref T₁ ⊸ T₂ ⊸ Ref T₂ ⊗ T₁`.  Note `(Ref T₂) ⊗ T₁`. -/
def axSwapTy (T₁ T₂ : Ty) : Ty := .lolli (.ref T₁) (.lolli T₂ (.tensor (.ref T₂) T₁))

/-- `Imm @a T ⊸ Imm @a T ⊗ Imm @a T`.  ([CONF] calls it `dupl`, §12.21.) -/
def axCopyTy (a : Life) (T : Ty) : Ty := .lolli (.imm a T) (.tensor (.imm a T) (.imm a T))

def axForgetImmTy (a : Life) (T : Ty) : Ty := .lolli (.imm a T) .unit

def axForgetMutTy (a : Life) (T : Ty) : Ty := .lolli (.mut a T) .unit

def axForgetUnkTy : Ty := .lolli .unk .unit

end BoCa

namespace BoCa

/-- `withbor ≜ λx.λf. (x, f () x)`  — [CONF] **Fig. 15** (p. 415:17).  Uses the
    linear `x` twice: it hands the borrower a borrow of `x` and *also* returns
    `x` itself.

    **The two documents print different bodies here; docs/adjudications.md
    §12.20.  [variant: [CONF] Fig. 15's body, not [TR] p. 4's.]**
    [TR] p. 4 and [CONF] p. 415:6 both print
    `withbor ≜ λx.λf. (x, f x)`, without the lifetime application.  That is the
    *pre-lifetime* (§2.2) reading and it does not match the §2.3 type

        Ref T₁ ⊸ (∀'a ⊏ ⊓Δ. Imm 'a T₁ ⊸ ['a]T₂) ⊸ Ref T₁ ⊗ T₂

    in which `f` is a **thunk**: `𝒱⟦∀'a ⊏ @b. T⟧δ(v) ≜ ∀α ⊏ @bδ. ℰ⟦T⟧δ(v ())`
    ([TR] p. 4), so `f` must be forced with `()` before it can be applied to the
    borrow.  Only [CONF] Fig. 15's body matches that type, and [TR]'s own proof
    of Lemma 6.172 writes `wp (v () ℓ)` (l. 2523), so we take Fig. 15's.  §12.20
    records the same disagreement for `swap` ([CONF] Fig. 3b) and `withload`
    ([CONF] Fig. 14).  [CONF] p. 415:6's body is correct at §2.2's own
    un-thunked type `Ref T₁ ⊸ (Imm T₁ ⊸ T₂) ⊸ (Ref T₁) ⊗ T₂`, which is simply
    earlier than the type it is being matched against here.

    Operationally this is visible: with the [TR] body, `withbor x (Λ.λb. e)`
    reduces to `(x, λb. e)` — the borrower is handed `x` as its *lifetime*
    argument and never receives the borrow at all. -/
def withbor : Expr := lam2 (.pair v1 (.app (.app v0 unit') v1))

end BoCa

namespace BoCa
open BoCa.Lifetime

/-- `(1) Ref T₁ ⊸ (∀'a ⊏ ⊓Δ. Imm 'a T₁ ⊸ ['a]T₂) ⊸ Ref T₁ ⊗ T₂` -/
def axWithbor1Ty (x : LifeVar) (bnd : Life) (T₁ T₂ : Ty) : Ty :=
  .lolli (.ref T₁)
    (.lolli (.all x bnd (.lolli (.imm (.var x) T₁) (.box (.var x) T₂)))
            (.tensor (.ref T₁) T₂))

/-- `(2) Ref T₁ ⊸ (∀'a ⊏ ⊓Δ. Mut 'a T₁ ⊸ ['a]T₂) ⊸ Ref T₁ ⊗ T₂`, side
    condition `Δ ⊢ T₁ ⊐ @b` (§12.9, existential). -/
def axWithbor2Ty (x : LifeVar) (bnd : Life) (T₁ T₂ : Ty) : Ty :=
  .lolli (.ref T₁)
    (.lolli (.all x bnd (.lolli (.mut (.var x) T₁) (.box (.var x) T₂)))
            (.tensor (.ref T₁) T₂))

/-- `(3) Mut @a T₁ ⊸ (∀'b ⊏ ⊓Δ. Mut 'b T₁ ⊸ ['b]T₂) ⊸ Mut @a T₁ ⊗ T₂` -/
def axWithbor3Ty (a : Life) (x : LifeVar) (bnd : Life) (T₁ T₂ : Ty) : Ty :=
  .lolli (.mut a T₁)
    (.lolli (.all x bnd (.lolli (.mut (.var x) T₁) (.box (.var x) T₂)))
            (.tensor (.mut a T₁) T₂))

end BoCa

namespace BoCa

/-- `withload ≜ λx λf. f () (load x)` — [CONF] **Fig. 14** (p. 415:16).

    **§12.20 — the two documents differ, and we follow [CONF].
    [variant: [CONF] Fig. 14's body, not [TR] p. 4's.]**  [TR] p. 4
    prints `withload ≜ λx.λf. (x, f (load x))`, which does not match the type
    both documents print: the type
    `Imm @a T₁ ⊸ (∀'b ⊏ ⊓Δ. Imm̲ 'b T₁ ⊸ ['b]T₂) ⊸ T₂` returns a bare `T₂`,
    and that body returns a pair — and it also drops the lifetime application
    that makes `f` a thunk (`𝒱⟦∀'a ⊏ @b. T⟧δ(v) ≜ ∀α ⊏ @bδ. ℰ⟦T⟧δ(v ())`,
    [TR] p. 4).  `withbor` is the same disagreement — [TR] p. 4's
    `λx.λf. (x, f x)` against [CONF] Fig. 15's `λxλf. (x, f () x)` — resolved the
    same way: [CONF] Fig. 14 is the version here.

    It is ill-typed in the base system for the usual reason and one more: it
    applies `load`, which [CONF] Fig. 3b (p. 415:4) marks `⊬` and for which
    [TR] p. 2 prints no rule at all. -/
def withload : Expr := lam2 (.app (.app v0 unit') (.app load' v1))

end BoCa

namespace BoCa
open BoCa.Lifetime

/-- `Mut @a T₁ ⊸ (T₁ ⊸ T₁ ⊗ T₂) ⊸ Mut @a T₁ ⊗ T₂`.  The callback is a bare
    `⊸`: no thunk, no fresh lifetime, no modality on its result. -/
def axWithswapTy (a : Life) (T₁ T₂ : Ty) : Ty :=
  .lolli (.mut a T₁) (.lolli (.lolli T₁ (.tensor T₁ T₂)) (.tensor (.mut a T₁) T₂))

/-- `Imm̲ 'b T`, the reborrow metafunction.  Structural, hence total. -/
def Ty.immReborrow (b : Life) : Ty → Ty
  | .unit          => .unit                                          -- (1)
  | .sum    T₁ T₂  => .sum    (T₁.immReborrow b) (T₂.immReborrow b)   -- (2)
  | .tensor T₁ T₂  => .tensor (T₁.immReborrow b) (T₂.immReborrow b)   -- (3)
  | .lolli  _  _   => .unk                                           -- (4)
  | .ref T         => .imm b T                                 -- (5) constructor
  | .imm a T       => .imm a T                                 -- (6) constructor
  | .box _ T       => T.immReborrow b                          -- (7) recursive
  | .all _ _ _     => .unk                                           -- (8)
  -- (9) `Imm̲ 'b (Mut @a T) ≜ Imm 'b T` — [CONF] Fig. 9 only (§12.10).  The
  -- index is the LOAD's fresh `'b`, not the mutable borrow's own `@a`: [CONF]
  -- p. 415:11 says so in as many words, and an `Imm @a T` here would be
  -- "allowed to escape the scope of the load".  The `@a` is therefore dropped.
  | .mut _ T       => .imm b T                                 -- (9) constructor
  | .unk           => .unk                                     -- §12.11, ours

/-- `Imm @a T₁ ⊸ (∀'b ⊏ ⊓Δ. Imm̲ 'b T₁ ⊸ ['b]T₂) ⊸ T₂`.  The underlined `Imm̲`
    is the metafunction (§12.28); at a declarative `T₁` it is a total function
    computing a real type, never a suspension. -/
def axWithloadTy (a : Life) (x : LifeVar) (bnd : Life) (T₁ T₂ : Ty) : Ty :=
  .lolli (.imm a T₁)
    (.lolli (.all x bnd (.lolli (Ty.immReborrow (.var x) T₁) (.box (.var x) T₂)))
            T₂)

end BoCa

namespace BoCa.Lifetime

structure LSub where
  entries : List (LifeVar × Nat)
  deriving Repr, DecidableEq, Inhabited

end BoCa.Lifetime

namespace BoCa.Lifetime.LSub

def find? (δ : LSub) (x : LifeVar) : Option Nat := assocFind x δ.entries

end BoCa.Lifetime.LSub

namespace BoCa.Lifetime

def Life.interp (δ : LSub) : Life → Option Nat
  | .var x    => δ.find? x
  | .top      => some SLife.top
  -- §12.7: `⊔ ↦ ⊔`, not `⊔ ↦ ⊓` as [TR] p. 3 prints.
  | .join a b => (a.interp δ).bind fun m => (b.interp δ).bind fun n => some (SLife.join m n)
  | .meet a b => (a.interp δ).bind fun m => (b.interp δ).bind fun n => some (SLife.meet m n)

def LifeCtx.Models (Δ : LifeCtx) (δ : LSub) : Prop :=
  ∀ x u, Δ.find? x = some u →
    ∃ m n, δ.find? x = some m ∧ u.interp δ = some n ∧ SLife.Lt m n

/-- `Δ ⊨ @a` — the real, non-computable definition. -/
def LifeCtx.Defines (Δ : LifeCtx) (a : Life) : Prop :=
  ∀ δ, Δ.Models δ → ∃ n, a.interp δ = some n

/-- `Δ ⊨ @a ⊏ @b`, the real definition ([TR] p. 3).  Definedness of both sides
    is part of it, since `@aδ ⊏ @bδ` presupposes both are defined. -/
def LifeCtx.EntailsLt (Δ : LifeCtx) (a b : Life) : Prop :=
  ∀ δ, Δ.Models δ → ∃ m n, a.interp δ = some m ∧ b.interp δ = some n ∧ SLife.Lt m n

end BoCa.Lifetime

namespace BoCa
open BoCa.Lifetime

/-- `Δ ⊢ T ⊐ @a` — the seven rules of [TR] §2 p. 2.  `Outlives` below is
    this inductive, at the index the judgment names.

    The three absences are the mechanism, not an oversight: no rule for `⊸`
    (an opaque closure may capture a borrow), none for `∀` (a thunk, same
    reason), and none for `Unk` (incompleteness (13), where a rule would in
    fact be sound). -/
inductive OutlivesRules (Δ : LifeCtx) (a : Life) : Ty → Prop where
  | unit                                                       : OutlivesRules Δ a .unit
  | tensor {T₁ T₂} : OutlivesRules Δ a T₁ → OutlivesRules Δ a T₂ →
      OutlivesRules Δ a (.tensor T₁ T₂)
  | sum    {T₁ T₂} : OutlivesRules Δ a T₁ → OutlivesRules Δ a T₂ →
      OutlivesRules Δ a (.sum T₁ T₂)
  | ref    {T}     : OutlivesRules Δ a T                       → OutlivesRules Δ a (.ref T)
  /-- §12.17: [TR]'s strict, non-disjunctive rule, not [CONF] Fig. 7's. -/
  | box    {b T}   : Δ.EntailsLt a b                           → OutlivesRules Δ a (.box b T)
  | imm    {b T}   : Δ.EntailsLt a b                           → OutlivesRules Δ a (.imm b T)
  | mut    {b T}   : Δ.EntailsLt a b                           → OutlivesRules Δ a (.mut b T)

/-- `Δ ⊢ T ⊐ @a`.  [TR] p. 2's judgment-form header presupposes `⊨ Δ` and
    `Δ ⊨ @a`, and prints nothing after `@a` (600 dpi), so this
    is exactly `OutlivesRules` — the index is unrestricted, `⊤` included.
    §C.25. -/
def Outlives (Δ : LifeCtx) (T : Ty) (a : Life) : Prop :=
  OutlivesRules Δ a T

end BoCa

namespace BoCa.Lifetime

/-- `Δ ⊨ @a ⊑ @b` — [CONF] Fig. 11's "(and similarly for `⊑̇`)", at the
    carrier's lattice order `Le`.  §2, §12.3. -/
def LifeCtx.EntailsLe (Δ : LifeCtx) (a b : Life) : Prop :=
  ∀ δ, Δ.Models δ → ∃ m n, a.interp δ = some m ∧ b.interp δ = some n ∧ SLife.Le m n

end BoCa.Lifetime

namespace BoCa
open BoCa.Lifetime

/-- `Δ ⊨ Γ ⊐ @a`, the premise of the context-directed `[]I`, read as [CONF]
    Figs. 6/7 spell it out: `∀x ∈ dom(Γ). Δ ⊢ Γ(x) ⊐ @a` (§12.6).  `dom(Γ)` is
    the **live** slots; a consumed slot is no longer in scope. -/
def Ctx.Outlives (Δ : LifeCtx) (Γ : Ctx Ty) (a : Life) : Prop :=
  Δ.Defines a ∧ ∀ s ∈ Γ, s.live = true → OutlivesRules Δ a s.ty

end BoCa

namespace BoCa.Lifetime

/-- `⊓ dom(Δ)` as a right fold of binary meets, with `⊓∅ = ⊤` (§12.15). -/
def meetOfDomL : List (LifeVar × Life) → Life
  | []          => .top
  | (x, _) :: t => .meet (.var x) (meetOfDomL t)

def LifeCtx.meetOfDom (Δ : LifeCtx) : Life := meetOfDomL Δ.entries

end BoCa.Lifetime

end
