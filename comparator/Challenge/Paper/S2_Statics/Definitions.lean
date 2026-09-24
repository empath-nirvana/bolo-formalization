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

/-- `•` — every slot already consumed. -/
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

/-- `swap ≜ λx.λy₂. let y₁ = load x; store x y₂; (x, y₁)` — [CONF] Fig. 3b
    (p. 415:4). -/
def swap : Expr :=
  lam2 (elet (.app load' v1)
             (.seq (.app (.app store' v2) v1)
                   (.pair v2 v0)))

end BoCa

namespace BoCa
open BoCa.Lifetime

/-- `Ref T₁ ⊸ T₂ ⊸ Ref T₂ ⊗ T₁`. -/
def axSwapTy (T₁ T₂ : Ty) : Ty := .lolli (.ref T₁) (.lolli T₂ (.tensor (.ref T₂) T₁))

def axCopyTy (a : Life) (T : Ty) : Ty := .lolli (.imm a T) (.tensor (.imm a T) (.imm a T))

def axForgetImmTy (a : Life) (T : Ty) : Ty := .lolli (.imm a T) .unit

def axForgetMutTy (a : Life) (T : Ty) : Ty := .lolli (.mut a T) .unit

def axForgetUnkTy : Ty := .lolli .unk .unit

end BoCa

namespace BoCa

/-- `withbor ≜ λx.λf. (x, f () x)` — [CONF] Fig. 15 (p. 415:17). -/
def withbor : Expr := lam2 (.pair v1 (.app (.app v0 unit') v1))

end BoCa

namespace BoCa
open BoCa.Lifetime

/-- `(1) Ref T₁ ⊸ (∀'a ⊏ ⊓Δ. Imm 'a T₁ ⊸ ['a]T₂) ⊸ Ref T₁ ⊗ T₂` -/
def axWithbor1Ty (x : LifeVar) (bnd : Life) (T₁ T₂ : Ty) : Ty :=
  .lolli (.ref T₁)
    (.lolli (.all x bnd (.lolli (.imm (.var x) T₁) (.box (.var x) T₂)))
            (.tensor (.ref T₁) T₂))

/-- `(2) Ref T₁ ⊸ (∀'a ⊏ ⊓Δ. Mut 'a T₁ ⊸ ['a]T₂) ⊸ Ref T₁ ⊗ T₂` -/
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

/-- `withload ≜ λx λf. f () (load x)` — [CONF] Fig. 14 (p. 415:16). -/
def withload : Expr := lam2 (.app (.app v0 unit') (.app load' v1))

end BoCa

namespace BoCa
open BoCa.Lifetime

def axWithswapTy (a : Life) (T₁ T₂ : Ty) : Ty :=
  .lolli (.mut a T₁) (.lolli (.lolli T₁ (.tensor T₁ T₂)) (.tensor (.mut a T₁) T₂))

/-- `Imm̲ 'b T`, the reborrow metafunction. -/
def Ty.immReborrow (b : Life) : Ty → Ty
  | .unit          => .unit                                          -- (1)
  | .sum    T₁ T₂  => .sum    (T₁.immReborrow b) (T₂.immReborrow b)   -- (2)
  | .tensor T₁ T₂  => .tensor (T₁.immReborrow b) (T₂.immReborrow b)   -- (3)
  | .lolli  _  _   => .unk                                           -- (4)
  | .ref T         => .imm b T                                 -- (5) constructor
  | .imm a T       => .imm a T                                 -- (6) constructor
  | .box _ T       => T.immReborrow b                          -- (7) recursive
  | .all _ _ _     => .unk                                           -- (8)
  -- (9) [CONF] Fig. 9 (§12.10).  The index is the load's fresh `'b`, not the
  -- mutable borrow's `@a` ([CONF] p. 415:11).
  | .mut _ T       => .imm b T                                 -- (9) constructor
  | .unk           => .unk                                     -- §12.11

/-- `Imm @a T₁ ⊸ (∀'b ⊏ ⊓Δ. Imm̲ 'b T₁ ⊸ ['b]T₂) ⊸ T₂`. -/
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
  -- §12.7
  | .join a b => (a.interp δ).bind fun m => (b.interp δ).bind fun n => some (SLife.join m n)
  | .meet a b => (a.interp δ).bind fun m => (b.interp δ).bind fun n => some (SLife.meet m n)

def LifeCtx.Models (Δ : LifeCtx) (δ : LSub) : Prop :=
  ∀ x u, Δ.find? x = some u →
    ∃ m n, δ.find? x = some m ∧ u.interp δ = some n ∧ SLife.Lt m n

def LifeCtx.Defines (Δ : LifeCtx) (a : Life) : Prop :=
  ∀ δ, Δ.Models δ → ∃ n, a.interp δ = some n

def LifeCtx.EntailsLt (Δ : LifeCtx) (a b : Life) : Prop :=
  ∀ δ, Δ.Models δ → ∃ m n, a.interp δ = some m ∧ b.interp δ = some n ∧ SLife.Lt m n

end BoCa.Lifetime

namespace BoCa
open BoCa.Lifetime

/-- The seven rules of `Δ ⊢ T ⊐ @a`.  There is no rule for `⊸`, `∀` or `Unk`. -/
inductive OutlivesRules (Δ : LifeCtx) (a : Life) : Ty → Prop where
  | unit                                                       : OutlivesRules Δ a .unit
  | tensor {T₁ T₂} : OutlivesRules Δ a T₁ → OutlivesRules Δ a T₂ →
      OutlivesRules Δ a (.tensor T₁ T₂)
  | sum    {T₁ T₂} : OutlivesRules Δ a T₁ → OutlivesRules Δ a T₂ →
      OutlivesRules Δ a (.sum T₁ T₂)
  | ref    {T}     : OutlivesRules Δ a T                       → OutlivesRules Δ a (.ref T)
  | box    {b T}   : Δ.EntailsLt a b                           → OutlivesRules Δ a (.box b T)
  | imm    {b T}   : Δ.EntailsLt a b                           → OutlivesRules Δ a (.imm b T)
  | mut    {b T}   : Δ.EntailsLt a b                           → OutlivesRules Δ a (.mut b T)

/-- `Δ ⊢ T ⊐ @a`, at an unrestricted index (§C.25). -/
def Outlives (Δ : LifeCtx) (T : Ty) (a : Life) : Prop :=
  OutlivesRules Δ a T

end BoCa

namespace BoCa.Lifetime

def LifeCtx.EntailsLe (Δ : LifeCtx) (a b : Life) : Prop :=
  ∀ δ, Δ.Models δ → ∃ m n, a.interp δ = some m ∧ b.interp δ = some n ∧ SLife.Le m n

end BoCa.Lifetime

namespace BoCa
open BoCa.Lifetime

def Ctx.Outlives (Δ : LifeCtx) (Γ : Ctx Ty) (a : Life) : Prop :=
  Δ.Defines a ∧ ∀ s ∈ Γ, s.live = true → OutlivesRules Δ a s.ty

end BoCa

namespace BoCa.Lifetime

def meetOfDomL : List (LifeVar × Life) → Life
  | []          => .top
  | (x, _) :: t => .meet (.var x) (meetOfDomL t)

def LifeCtx.meetOfDom (Δ : LifeCtx) : Life := meetOfDomL Δ.entries

end BoCa.Lifetime

end
