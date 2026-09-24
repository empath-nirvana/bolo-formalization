import Challenge.Paper.S1_Syntax.Definitions
import Challenge.Paper.S2_Statics.Definitions
import Challenge.Paper.S3_Dynamics.Definitions
import Challenge.Support.Lifetimes.Substitution
import Challenge.Support.Lifetimes.Terms
import Challenge.Support.Statics.Contexts

/-!
Verbatim from `Support/Statics/Presupposed.lean`: the declarations of that file the judged statement
reaches (see `comparator/Challenge.lean`), with their namespaces and `open`s.
The source also imports `Paper.S4_LogicalRelation.Definitions`, `Support.Lifetimes.Interpretation`; no declaration
copied here uses anything from them.
-/

noncomputable section

namespace BoCa.Lifetime.LifeCtx

def empty : LifeCtx := ⟨[]⟩

end BoCa.Lifetime.LifeCtx

namespace BoCa
open BoCa.Lifetime

/-- **`Δ ⊢ T`, decided.**  Nine of the ten constructors, as [TR] p. 2 prints
them; `Unk` has no rule there, so no type mentioning it passes.

Two clauses say more than `BoCa.WfTy` records, and both say what the page
writes.  The `∀` rule's premise is `Δ, ('a ⊏ @b) ⊢ T`, an extension and not a
shadowing, so `'a ∉ dom(Δ)` is asked here; definition
row 2.25 records that `WfTy.all` carries no such premise.  And `Δ ⊨ @a` is
asked as `Life.wf`, which is the sound half of it: the semantic relation is
weaker only at an unsatisfiable `Δ`, which p. 2's judgment box excludes by
"Presumes ⊨ Δ" and which no constructor of `WfTy` carries (row 2.19).
`[about ours: the decidable sufficient condition for [TR] p. 2's `Δ ⊢ T`]` -/
def Ty.wfB : Ty → LifeCtx → Bool
  | .unit,         _ => true
  | .unk,          _ => false
  | .ref T,        Δ => T.wfB Δ
  | .sum    T₁ T₂, Δ => T₁.wfB Δ && T₂.wfB Δ
  | .tensor T₁ T₂, Δ => T₁.wfB Δ && T₂.wfB Δ
  | .lolli  T₁ T₂, Δ => T₁.wfB Δ && T₂.wfB Δ
  | .box a T,      Δ => a.wf Δ && T.wfB Δ
  | .imm a T,      Δ => a.wf Δ && T.wfB Δ
  | .mut a T,      Δ => a.wf Δ && T.wfB Δ
  | .all y b T,    Δ => (Δ.find? y).isNone && b.wf Δ && T.wfB (Δ.extend y b)

/-- `'x` is a BINDER of `T` — a `∀` former's own variable, at any depth.  This
    is not `LFree`, which is about occurrences: `Ty.wfB`'s `∀` clause asks the
    binder to be outside `dom(Δ)` (row 2.25, ours, since [TR] p. 2 writes the
    premise's context as the extension `Δ, ('a ⊏ @b)`), so what an extension
    can collide with is binders and not free occurrences.
    `[about ours: the Barendregt side of `Ty.wfB`'s `∀` clause]` -/
def Ty.bindsB : Ty → LifeVar → Bool
  | .unit,         _ => false
  | .unk,          _ => false
  | .ref T,        x => T.bindsB x
  | .sum    T₁ T₂, x => T₁.bindsB x || T₂.bindsB x
  | .tensor T₁ T₂, x => T₁.bindsB x || T₂.bindsB x
  | .lolli  T₁ T₂, x => T₁.bindsB x || T₂.bindsB x
  | .box _ T,      x => T.bindsB x
  | .imm _ T,      x => T.bindsB x
  | .mut _ T,      x => T.bindsB x
  | .all y _ T,    x => (y == x) || T.bindsB x

/-- **`T` is well-SCOPED in `Δ`** — `Ty.wfB` minus the formation question.
    Clause for clause the same except at `Unk`, which `Ty.wfB` refuses because
    [TR] p. 2 prints no formation rule for it — while p. 3's axiom table types
    `forget : Unk ⊸ 1`, and `Imm̲ 'b (T₁ ⊸ T₂) ≜ Unk` puts `Unk` inside
    `withload`'s own type at every function payload.  Scoping is all the
    Barendregt convention needs: a binder fresh for `Δ` is free in no
    `Δ`-scoped type, and `Unk` binds and mentions nothing.
    `[about ours: the scoping half of [TR] p. 2's `Δ ⊢ T`]` -/
def Ty.scopedB : Ty → LifeCtx → Bool
  | .unit,         _ => true
  | .unk,          _ => true
  | .ref T,        Δ => T.scopedB Δ
  | .sum    T₁ T₂, Δ => T₁.scopedB Δ && T₂.scopedB Δ
  | .tensor T₁ T₂, Δ => T₁.scopedB Δ && T₂.scopedB Δ
  | .lolli  T₁ T₂, Δ => T₁.scopedB Δ && T₂.scopedB Δ
  | .box a T,      Δ => a.wf Δ && T.scopedB Δ
  | .imm a T,      Δ => a.wf Δ && T.scopedB Δ
  | .mut a T,      Δ => a.wf Δ && T.scopedB Δ
  | .all y b T,    Δ => (Δ.find? y).isNone && b.wf Δ && T.scopedB (Δ.extend y b)

inductive DerivesWf : LifeCtx → Ctx Ty → Expr → Ty → Prop where
  | var {Δ Γ i T} (h : Ctx.Solo Γ i T) : DerivesWf Δ Γ (.var i) T
  | unitI {Δ Γ} (h : Ctx.Dead Γ) : DerivesWf Δ Γ (.val .unit) .unit
  | unitE {Δ Γ Γ₁ Γ₂ e₁ e₂ T} (hs : Ctx.Split Γ Γ₁ Γ₂)
      (h₁ : DerivesWf Δ Γ₁ e₁ .unit) (h₂ : DerivesWf Δ Γ₂ e₂ T) :
      DerivesWf Δ Γ (.seq e₁ e₂) T
  | tensorI {Δ Γ Γ₁ Γ₂ e₁ e₂ T₁ T₂} (hs : Ctx.Split Γ Γ₁ Γ₂)
      (h₁ : DerivesWf Δ Γ₁ e₁ T₁) (h₂ : DerivesWf Δ Γ₂ e₂ T₂) :
      DerivesWf Δ Γ (.pair e₁ e₂) (.tensor T₁ T₂)
  /-- `⊗E`, with the eliminated type ranging over the types `Δ ⊢ T` admits;
      that is what puts `x₁ ∶ T₁, x₂ ∶ T₂` inside `Δ ⊢ Γ` at the premise. -/
  | tensorE {Δ Γ Γp Γb ep eb T₁ T₂ T} (hs : Ctx.Split Γ Γp Γb)
      (hwf : (Ty.tensor T₁ T₂).scopedB Δ = true)
      (hp : DerivesWf Δ Γp ep (.tensor T₁ T₂))
      (hb : DerivesWf Δ (⟨T₂, true⟩ :: ⟨T₁, true⟩ :: Γb) eb T) :
      DerivesWf Δ Γ (.letpair ep eb) T
  | sumI₁ {Δ Γ e T₁ T₂} (h : DerivesWf Δ Γ e T₁) :
      DerivesWf Δ Γ (.inj₁ e) (.sum T₁ T₂)
  | sumI₂ {Δ Γ e T₁ T₂} (h : DerivesWf Δ Γ e T₂) :
      DerivesWf Δ Γ (.inj₂ e) (.sum T₁ T₂)
  /-- `⊕E`, with the eliminated type ranging over the types `Δ ⊢ T` admits;
      that is what puts `x_b ∶ T_b` inside `Δ ⊢ Γ` at each branch. -/
  | sumE {Δ Γ Γs Γb es e₁ e₂ T₁ T₂ T} (hs : Ctx.Split Γ Γs Γb)
      (hwf : (Ty.sum T₁ T₂).scopedB Δ = true)
      (h₀ : DerivesWf Δ Γs es (.sum T₁ T₂))
      (h₁ : DerivesWf Δ (⟨T₁, true⟩ :: Γb) e₁ T)
      (h₂ : DerivesWf Δ (⟨T₂, true⟩ :: Γb) e₂ T) :
      DerivesWf Δ Γ (.case es e₁ e₂) T
  /-- `⊸I`, with the argument type ranging over the types `Δ ⊢ T` admits; that
      is what puts `x ∶ T₁` inside `Δ ⊢ Γ` at the premise. -/
  | lolliI {Δ Γ b T₁ T₂} (hwf : T₁.scopedB Δ = true)
      (h : DerivesWf Δ (⟨T₁, true⟩ :: Γ) b T₂) :
      DerivesWf Δ Γ (.val (.lam b)) (.lolli T₁ T₂)
  | lolliE {Δ Γ Γ₁ Γ₂ f a T₁ T₂} (hs : Ctx.Split Γ Γ₁ Γ₂)
      (ha : DerivesWf Δ Γ₁ a T₁) (hf : DerivesWf Δ Γ₂ f (.lolli T₁ T₂)) :
      DerivesWf Δ Γ (.app f a) T₂
  /-- `∀I`, with [TR] p. 2's `Δ ⊢ ∀('a ⊏ @b). T` supplying `Δ ⊧ @b` and the
      Barendregt side supplying the binder's freshness for `Γ`'s binders. -/
  | allI {Δ Γ x b S e T} (hx : Δ.find? x = none) (hb : b.wf Δ = true)
      (hnb : ∀ s ∈ Γ, s.live = true → s.ty.bindsB x = false)
      (h : DerivesWf (Δ.extend x b) (⟨S, false⟩ :: Γ) e T) :
      DerivesWf Δ Γ (.val (.lam e)) (.all x b T)
  | allE {Δ Γ e x b T a} (h : DerivesWf Δ Γ e (.all x b T)) (hlt : Δ.EntailsLt a b) :
      DerivesWf Δ Γ (.app e (.val .unit)) (Ty.instLife x a T)
  | boxIctx {Δ Γ e T a} (h : DerivesWf Δ Γ e T) (hΓ : Ctx.Outlives Δ Γ a) :
      DerivesWf Δ Γ e (.box a T)
  | boxE {Δ Γ e T a} (h : DerivesWf Δ Γ e (.box a T)) : DerivesWf Δ Γ e T
  | immSub {Δ Γ e a b T} (h : DerivesWf Δ Γ e (.imm b T)) (hle : Δ.EntailsLe a b) :
      DerivesWf Δ Γ e (.imm a T)
  | mutSub {Δ Γ e a b T} (h : DerivesWf Δ Γ e (.mut b T)) (hle : Δ.EntailsLe a b) :
      DerivesWf Δ Γ e (.mut a T)
  | allocAx {Δ Γ T} (hΓ : Ctx.Dead Γ) :
      DerivesWf Δ Γ (.val (.prim .alloc)) (.lolli T (.ref T))
  | freeAx {Δ Γ T} (hΓ : Ctx.Dead Γ) :
      DerivesWf Δ Γ (.val (.prim .free)) (.lolli (.ref T) T)
  | swapAx {Δ Γ T₁ T₂} (hΓ : Ctx.Dead Γ) : DerivesWf Δ Γ swap (axSwapTy T₁ T₂)
  | copyAx {Δ Γ a T} (hΓ : Ctx.Dead Γ) : DerivesWf Δ Γ copy (axCopyTy a T)
  | forgetImmAx {Δ Γ a T} (hΓ : Ctx.Dead Γ) :
      DerivesWf Δ Γ forget (axForgetImmTy a T)
  | forgetMutAx {Δ Γ a T} (hΓ : Ctx.Dead Γ) :
      DerivesWf Δ Γ forget (axForgetMutTy a T)
  | forgetUnkAx {Δ Γ} (hΓ : Ctx.Dead Γ) : DerivesWf Δ Γ forget axForgetUnkTy
  /-- Form (1), with the table's metavariables ranging over the types
      `Δ ⊢ T` admits. -/
  | withbor1Ax {Δ Γ T₁ T₂} (hΓ : Ctx.Dead Γ) (x : LifeVar) (hx : Δ.find? x = none)
      (hwf : (axWithbor1Ty x Δ.meetOfDom T₁ T₂).scopedB Δ = true) :
      DerivesWf Δ Γ withbor (axWithbor1Ty x Δ.meetOfDom T₁ T₂)
  /-- Form (2), keeping the printed side condition beside it. -/
  | withbor2Ax {Δ Γ T₁ T₂} (hΓ : Ctx.Dead Γ) (x : LifeVar) (hx : Δ.find? x = none)
      (hside : ∃ b, Δ.Defines b ∧ Outlives Δ T₁ b)
      (hwf : (axWithbor2Ty x Δ.meetOfDom T₁ T₂).scopedB Δ = true) :
      DerivesWf Δ Γ withbor (axWithbor2Ty x Δ.meetOfDom T₁ T₂)
  | withbor3Ax {Δ Γ a T₁ T₂} (hΓ : Ctx.Dead Γ) (x : LifeVar) (hx : Δ.find? x = none)
      (hwf : (axWithbor3Ty a x Δ.meetOfDom T₁ T₂).scopedB Δ = true) :
      DerivesWf Δ Γ withbor (axWithbor3Ty a x Δ.meetOfDom T₁ T₂)
  | withloadAx {Δ Γ a T₁ T₂} (hΓ : Ctx.Dead Γ) (x : LifeVar) (hx : Δ.find? x = none)
      (hwf : (axWithloadTy a x Δ.meetOfDom T₁ T₂).scopedB Δ = true) :
      DerivesWf Δ Γ withload (axWithloadTy a x Δ.meetOfDom T₁ T₂)
  | withswapAx {Δ Γ a T₁ T₂} (hΓ : Ctx.Dead Γ) :
      DerivesWf Δ Γ withswap (axWithswapTy a T₁ T₂)

end BoCa

end
