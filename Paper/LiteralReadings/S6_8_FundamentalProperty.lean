import Paper.LiteralReadings.S4_LogicalRelation
import Paper.LiteralReadings.S6_7_WeakestPreconditionRules
import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S3_Dynamics.Definitions
import Paper.S4_LogicalRelation.Definitions
import Paper.S4_LogicalRelation.Remarks
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Paper.S6_2_NonStandardLemmas.Lemmas
import Paper.S6_7_WeakestPreconditionRules.Lemmas
import Paper.S6_8_FundamentalProperty.Lemmas
import Support.Dynamics.Machine
import Support.Dynamics.PrintedWp
import Support.Lifetimes.Interpretation
import Support.Lifetimes.Substitution
import Support.Lifetimes.Terms
import Support.LogicalRelation.ClosedJudgment
import Support.LogicalRelation.ClosingSubstitutions
import Support.LogicalRelation.Compatibility
import Support.LogicalRelation.Facts
import Support.Model.Cells
import Support.Model.Composition
import Support.Model.Entailments
import Support.Model.Notation
import Support.Model.Prelude
import Support.Model.Propositions
import Support.Model.ReborrowRule
import Support.Model.Singletons
import Support.Model.UpdateSymmetry
import Support.Statics.Contexts
import Support.Statics.Presupposed
import Support.Syntax.Terms
import Support.TypedWorld.Images
import Support.TypedWorld.Invariant
import Support.TypedWorld.Records
import Support.TypedWorld.Relation
import Support.TypedWorld.World

/-!
# Literal readings — [TR] §6.8

* 6.151: `ViewWitness.fundamentalProperty_refused` — at a `withloadAx` node of our
  carrier, the statement at `Sem` without `WithloadEscrow` is refused (the
  configuration and its runs, source `BoCa/ViewWitness.lean`, move here with it);
  `ViewWitness.excluded` — that configuration is not a typed world with the
  argument in its type (source `BoCa/TypedViewWitness.lean`);
* 6.151, the antecedent read as the rule figures alone (`Derives` instead of p. 2's
  `DerivesWf`): `FundamentalPropertyOverRules`, `not_everyDerivationWf`, the route
  through `DerivesIn` (`fundamental_of_open`, `fundamental_in`,
  `fundamentalProperty_of`) and `not_everyDerivationInRegime`; and `SemArising`,
  which is not a route to the row (`sem_of_semArising` concludes at `gDenB`);
* 6.154, 6.155, 6.157, 6.169, 6.170: each compatibility lemma's step measured over
  `[TR]` §3's printed machine (`…_refuted_on_TR3`, `…_step_on_TR3`,
  `swap_step_blocked_on_TR3`), at the closed terms `[TR]` p. 2 types there;
* 6.162: `MutGapClosed.gap_closed`, the old carrier's counterexample type run
  through the printed `mut` cell, which stores the predicate.

**How this file reads.**  Each run opens with the result it measures and says where
that result's record is.  The declarations are the source's, with their tags; a
`[about ours: …]` tag names what is measured.  Nothing in the paper tree depends on
this file.
-/

noncomputable section

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
### Lemma 6.151 (Fundamental Property) — literal reading

The printed statement, the printed proof and the adjudication are in `Paper/S6_8_FundamentalProperty/Lemmas.lean`, under the record of Lemma 6.151 (Fundamental Property).
-/
/-- **6.151's antecedent read as the rule figures alone**, i.e. over
`BoCa.Derives`, which is [TR] p. 2's typing rules and nothing else and which
therefore consumes `Δ ⊢ T` at no constructor
(`docs/definition-inventory.md` row 2.19).

The two readings differ, and `not_everyDerivationWf` is where: `witness` is
`∅; • ⊢ λ().() : ∀('a ⊏ 'a). 1`, whose bound mentions its own binder — a
`Derives` node, and no `DerivesWf` node, since `DerivesWf.allI` reads p. 2's
own `Δ ⊧ @b` beside `'a ∉ dom(Δ)`.  So this quantifier reaches derivations the
presuppositions exclude, which is why it is kept apart from
`FundamentalProperty` rather than identified with it.

`fundamentalProperty_of` is this reading, from `fundamental_in` and
`EveryDerivationInRegime`.
`[about ours: 6.151's antecedent over `BoCa.Derives`]` -/
def FundamentalPropertyOverRules : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty), Derives Δ Γ e T → Sem Δ Γ e T

/-! Lemma 6.151 (Fundamental Property), literal reading, continued. -/
/-- **`Δ; Γ ⊨ e : T` with the slot conditions.**  Input: `𝒢⟦Γ⟧δ(γ)` carrying
`TyBounded` at each live slot.  Output: `TyBounded` at `T`, so the induction
feeds itself instead of having to recover the fact from the denotation.
`[restricted: to `gDenB` contexts — `[TR]` p. 4's `𝒢⟦Γ⟧δ` with a scope
condition of the kind its own `dom(Γ) ⊆ dom(δ)` already is]` -/
def SemArising (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty) : Prop :=
  ∀ δ γ ρ, Δ.Models δ → gDenB Δ δ Γ γ ρ →
    wp (substAll γ e) (fun v ρ' => vDen T δ v ρ' ∧ TyAt δ T ρ') ρ

/-! Lemma 6.151 (Fundamental Property), literal reading, continued. -/
/-- The projection adequacy uses: at `ρ = ∅` the input condition is
`gSepB_dead`, so the restriction costs nothing there. -/
theorem sem_of_semArising {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T : Ty}
    (h : SemArising Δ Γ e T) :
    ∀ δ γ ρ, Δ.Models δ → gDenB Δ δ Γ γ ρ → wp (substAll γ e) (vDen T δ) ρ :=
  fun δ γ ρ hδ hg => wp_mono (fun _ _ hx => hx.1) _ _ (h δ γ ρ hδ hg)

/-! Lemma 6.151 (Fundamental Property), literal reading, continued. -/
/-- **The resources the calculus puts together, at a licence `L`.**  Three of
the four places `[CONF]` 415:19–24 names are operations on resources: the empty
resource, the composition `●` — and either part of one, since a slot is read
off a composite — and the reborrow `reb_α`, which mints the borrow it takes.

Membership is a derivation and not a test, so `⋆`-closure (`comp`) and
splitting (`part`) hold by construction rather than having to be checked of a
predicate, and a resource is outside the family when nothing builds it.
`[about ours: the three resource operations `[CONF]` 415:19–24 names, as the
family they generate]` -/
inductive Arises (L : Life → Prop) : WRes → Prop
  /-- `∅` records no borrow. -/
  | empty : Arises L PMap.empty
  /-- `ρ₁ ● ρ₂`. -/
  | comp {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) :
      Arises L ρ₁ → Arises L ρ₂ → Arises L ρ
  /-- …and either part of one. -/
  | part {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) : Arises L ρ → Arises L ρ₁
  /-- `reb_α`, at a lifetime the licence covers. -/
  | reb {α : Life} {src img : WRes} (hr : ResU.Reb α src img) :
      Arises L src → L α → Arises L img

/-! Lemma 6.151 (Fundamental Property), literal reading, continued. -/
/-- **The assembly.**  §8b's closure lemmas are the four steps of this one
induction — `lifeMembers_empty`, `lifeMembers_compS`, `lifeMembers_compS_left`
and `lifeMembers_reb` — and nothing else is used.
`[about ours: §8b's closure lemmas read as the family's recursor]` -/
theorem lifeMembers_of_arises {L : Life → Prop} {ρ : WRes} (h : Arises L ρ) :
    LifeMembers L ρ := by
  induction h with
  | empty => exact lifeMembers_empty
  | comp hc _ _ ih₁ ih₂ => exact lifeMembers_compS hc ih₁ ih₂
  | part hc _ ih => exact lifeMembers_compS_left hc ih
  | reb hr _ hα ih => exact lifeMembers_reb hr ih hα

/-! Lemma 6.151 (Fundamental Property), literal reading, continued. -/
/-- **The induction of `[TR]` Lemma 6.151, with the §6.8 lemmas §6–§8 do not
prove carried as hypotheses.**
`[restricted: 6.161, 6.162, 6.163, 6.165 and 6.172–6.176 are assumed, and the
derivation is one of §12a's `DerivesIn`]`

The Fundamental Property is proved for derivations in the regime: for every
`DerivesIn` derivation, whose `∀I` nodes have a binder fresh for its bound, for
`Δ`'s bounds and for `Γ`'s live types, whose `withbor1`, `withbor2` and
`withbor3` nodes have a binder fresh for `T₁` and `T₂`, and whose `withload`
nodes have that freshness and 6.150's escrow.  What it excludes is a derivation
with a `∀I`, `withbor1`, `withbor2`, `withbor3` or `withload` binder that
captures — which `[TR]`'s named presentation never writes, so that presentation
works in the regime throughout.  Each hypothesis is one `[TR]` §6.8 lemma at the constructor
it discharges; the comment on each names it and its physical page.  Every other
constructor closes from §6–§8 directly, and the `induction` block below is the
proof that the two lists together are all of `DerivesIn`. -/
theorem fundamental_of_open
    /- **[TR] Lemma 6.161 (∀I-compat), p. 42** `[variant: adds the freshness of
       `'a` for `@b`, for `Δ`'s bounds and for `Γ`'s live types, as §9b's
       `allI_compat` does]`.  The premise's `Δ, ('a ⊏ @b)` is `Δ.extend x b`
       together with `hx`, which is what makes the extension a genuine one
       rather than a shadowing; the premise's context gains a slot already dead
       because `Λ.e ≜ λ_.e` (§12.14).  `allI_compat` is a term of this type, and
       the induction reads the three freshnesses off `AllISide` at the node. -/
    (open_allI : ∀ {Δ : LifeCtx} {Γ : Ctx Ty} {x : LifeVar} {b : Lifetime.Life}
      {S : Ty} {e : Expr} {T : Ty}, Δ.find? x = none →
      b.mentions x = false →
      (∀ y u, Δ.find? y = some u → u.mentions x = false) →
      (∀ s ∈ Γ, s.live = true → ¬ LFree x s.ty) →
      Sem (Δ.extend x b) (⟨S, false⟩ :: Γ) e T →
      Sem Δ Γ (.val (.lam e)) (.all x b T))
    /- **[TR] Lemma 6.162 (∀E-compat), p. 42** `[as printed]`.  `e[] ≜ e ()`
       (§12.14) and `T[@a/'a]` is `Ty.instLife`.  §9a's `allE_compat` is a term
       of this type. -/
    (open_allE : ∀ {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {x : LifeVar}
      {b : Lifetime.Life} {T : Ty} {a : Lifetime.Life},
      Sem Δ Γ e (.all x b T) → Δ.EntailsLt a b →
      Sem Δ Γ (.app e (.val .unit)) (Ty.instLife x a T))
    /- **[TR] Lemma 6.163 ([]I-compat), p. 42** `[as printed]`.
       `Δ ⊢ Γ ⊐ @a` is `Ctx.Outlives`, and `□` leaves the term alone (§12.5).
       `boxI_compat` is a term of this type. -/
    (open_boxI : ∀ {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T : Ty}
      {a : Lifetime.Life}, Sem Δ Γ e T → Ctx.Outlives Δ Γ a →
      Sem Δ Γ e (.box a T))
    /- **[TR] Lemma 6.165 (alloc-compat), p. 43** `[as printed]`.  `∅` is
       `Ctx.Dead Γ` (§12.19), and `Ref T` is `Ty.ref`.  `alloc_compat` is a term
       of this type. -/
    (open_alloc : ∀ {Δ : LifeCtx} {Γ : Ctx Ty} {T : Ty}, Ctx.Dead Γ →
      Sem Δ Γ (.val (.prim .alloc)) (.lolli T (.ref T)))
    /- **[TR] Lemma 6.172 (withbor-compat1), p. 45** `[variant: with the two
       freshness hypotheses `withbor1_compat` adds]`.  `⊓Δ` is
       `LifeCtx.meetOfDom` (§12.15); the `∀` binder is schematic on the page, so
       it is a parameter here, fresh for `Δ` by `hx` (§12.44).  Its proof applies
       `ImmFrame`, which — unlike 6.173's `MutFrame` — asks no side condition on
       `T₁`; the third and fourth premises are the binder's freshness for `T₁`
       and `T₂`, which its last step folds by.  `withbor1_compat` is the term to
       supply, and the induction reads the two off `Withbor1Side` at the node. -/
    (open_withbor1 : ∀ {Δ : LifeCtx} {Γ : Ctx Ty} {T₁ T₂ : Ty} (x : LifeVar),
      Ctx.Dead Γ → Δ.find? x = none →
      ¬ LFree x T₁ → ¬ LFree x T₂ →
      Sem Δ Γ withbor (axWithbor1Ty x Δ.meetOfDom T₁ T₂))
    /- **[TR] Lemma 6.173 (withbor-compat2), p. 46** `[variant: with the two
       freshness hypotheses `withbor2_compat` adds]`.  Its "If `Δ ⊢ T₁ ⊐ @b`
       then" binds `@b` nowhere else, so it is read existentially (§12.9);
       `Δ ⊢ T ⊐ @a` presupposes `Δ ⊨ @a` (§C.25), which is the `Defines`
       conjunct.  The fourth and fifth premises are the binder's freshness for
       `T₁` and `T₂`; `withbor2_compat` is the term to supply, and the
       induction reads the two off `Withbor2Side` at the node. -/
    (open_withbor2 : ∀ {Δ : LifeCtx} {Γ : Ctx Ty} {T₁ T₂ : Ty} (x : LifeVar),
      Ctx.Dead Γ → Δ.find? x = none →
      (∃ b, Δ.Defines b ∧ BoCa.Outlives Δ T₁ b) →
      ¬ LFree x T₁ → ¬ LFree x T₂ →
      Sem Δ Γ withbor (axWithbor2Ty x Δ.meetOfDom T₁ T₂))
    /- **[TR] Lemma 6.174 (withbor-compat3), p. 47** `[variant: with the two
       freshness hypotheses `withbor3_compat` adds]`.  The third and fourth
       premises are the binder's freshness for `T₁` and `T₂`, 6.172's
       convention that 6.174 inherits; `withbor3_compat` is the term to
       supply, and the induction reads the two off `Withbor3Side` at the
       node. -/
    (open_withbor3 : ∀ {Δ : LifeCtx} {Γ : Ctx Ty} {a : Lifetime.Life}
      {T₁ T₂ : Ty} (x : LifeVar), Ctx.Dead Γ → Δ.find? x = none →
      ¬ LFree x T₁ → ¬ LFree x T₂ →
      Sem Δ Γ withbor (axWithbor3Ty a x Δ.meetOfDom T₁ T₂))
    /- **[TR] Lemma 6.175 (withload-compat), p. 47** `[variant: with the three
       hypotheses `withload_compat` adds that name the node]`; the callback's
       argument is `Imm̲ 'b T₁`, i.e. `Ty.immReborrow` (§12.11).  The third
       premise is the escrow `[TR]` 6.150 inherits from 6.55, at the `P̂` this
       proof builds, and the fourth and fifth the binder's freshness for `T₁`
       and `T₂` — `↺V₂`'s *"if `'a` not free in `T`"* and the closing
       sentence's *"because `'b` does not occur free in `T₂`"*;
       `withload_compat` is the term to supply, and the induction reads the
       three off `WithloadSide` at the node. -/
    (open_withload : ∀ {Δ : LifeCtx} {Γ : Ctx Ty} {a : Lifetime.Life}
      {T₁ T₂ : Ty} (x : LifeVar), Ctx.Dead Γ → Δ.find? x = none →
      (∀ (δ : LSub) (vℓ : Val), RebEscrow
        (fun β v' => ⌜vℓ = v'⌝ ⋆ vDen (T₁.immReborrow (.var x)) (δ.extend x β) vℓ)) →
      ¬ LFree x T₁ → ¬ LFree x T₂ →
      Sem Δ Γ withload (axWithloadTy a x Δ.meetOfDom T₁ T₂))
    /- **[TR] Lemma 6.176 (withswap-compat), p. 48** `[as printed]`.  The
       callback is a bare `⊸`: no thunk, no fresh lifetime, no modality.
       `withswap_compat` is a term of this type. -/
    (open_withswap : ∀ {Δ : LifeCtx} {Γ : Ctx Ty} {a : Lifetime.Life}
      {T₁ T₂ : Ty}, Ctx.Dead Γ →
      Sem Δ Γ withswap (axWithswapTy a T₁ T₂)) :
    ∀ (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty), DerivesIn Δ Γ e T → Sem Δ Γ e T := by
  intro Δ Γ e T hD
  induction hD with
  | var h                     => exact id_compat h
  | unitI h                   => exact unitI_compat h
  | unitE hs _ _ ih₁ ih₂      => exact unitE_compat hs ih₁ ih₂
  | tensorI hs _ _ ih₁ ih₂    => exact tensorI_compat hs ih₁ ih₂
  | tensorE hs _ _ ih₁ ih₂    => exact tensorE_compat hs ih₁ ih₂
  | sumI₁ _ ih                => exact sumI₁_compat ih
  | sumI₂ _ ih                => exact sumI₂_compat ih
  | sumE hs _ _ _ ih₀ ih₁ ih₂ => exact sumE_compat hs ih₀ ih₁ ih₂
  | lolliI _ ih               => exact lolliI_compat ih
  | lolliE hs _ _ iha ihf     => exact lolliE_compat hs iha ihf
  | allI hx _ hside ih        => exact open_allI hx hside.1 hside.2.1 hside.2.2 ih
  | allE _ hlt ih             => exact open_allE ih hlt
  | boxIctx _ hΓ ih           => exact open_boxI ih hΓ
  | boxE _ ih                 => exact boxE_compat ih
  | immSub _ hle ih           => exact immSub_compat ih hle
  | mutSub _ hle ih           => exact mutSub_compat ih hle
  | allocAx hΓ                => exact open_alloc hΓ
  | freeAx hΓ                 => exact free_compat hΓ
  | swapAx hΓ                 => exact swap_compat hΓ
  | copyAx hΓ                 => exact copy_compat hΓ
  | forgetImmAx hΓ            => exact forgetImm_compat hΓ
  | forgetMutAx hΓ            => exact forgetMut_compat hΓ
  | forgetUnkAx hΓ            => exact forgetUnk_compat hΓ
  | withbor1Ax hΓ x hx hside  => exact open_withbor1 x hΓ hx hside.1 hside.2
  | withbor2Ax hΓ x hx hs hside =>
      exact open_withbor2 x hΓ hx hs hside.1 hside.2
  | withbor3Ax hΓ x hx hside  =>
      exact open_withbor3 x hΓ hx hside.1 hside.2
  | withloadAx hΓ x hx hside  =>
      exact open_withload x hΓ hx hside.1 hside.2.1 hside.2.2
  | withswapAx hΓ             => exact open_withswap hΓ

/-! Lemma 6.151 (Fundamental Property), literal reading, continued. -/
/-- **`[TR]` Lemma 6.151 (Fundamental Property, p. 40) for derivations in the
regime**, with every one of `fundamental_of_open`'s nine slots discharged by
the §6.8 lemma the comment at it names.
`[restricted: to §12a's `DerivesIn`]` -/
theorem fundamental_in :
    ∀ (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty),
      DerivesIn Δ Γ e T → Sem Δ Γ e T :=
  fundamental_of_open
    (fun hx hbx hΔx hΓx h => allI_compat hx hbx hΔx hΓx h)
    (fun h hlt => allE_compat h hlt)
    (fun h hΓ => boxI_compat h hΓ)
    (fun hΓ => alloc_compat hΓ)
    (fun x hΓ hx h₁ h₂ => withbor1_compat x hΓ hx h₁ h₂)
    (fun x hΓ hx hs h₁ h₂ => withbor2_compat x hΓ hx hs h₁ h₂)
    (fun x hΓ hx h₁ h₂ => withbor3_compat x hΓ hx h₁ h₂)
    (fun x hΓ hx hesc h₁ h₂ => withload_compat x hΓ hx hesc h₁ h₂)
    (fun hΓ => withswap_compat hΓ)

/-! Lemma 6.151 (Fundamental Property), literal reading, continued. -/
theorem not_everyDerivationInRegime : ¬ EveryDerivationInRegime := by
  intro hreg
  exact aux (hreg _ _ _ _ witness) rfl (by simp [stripBox])

/-! Lemma 6.151 (Fundamental Property), literal reading, continued. -/
/-- **`[TR]` Lemma 6.151 from the two**, at the antecedent read as the rule
figures alone.  `fundamental_in` run at the derivation
`EveryDerivationInRegime` supplies; the conclusion is
`FundamentalPropertyOverRules` on the nose, over `BoCa.Derives`.
`[restricted: to `EveryDerivationInRegime`]` -/
theorem fundamentalProperty_of
    (hreg : EveryDerivationInRegime) : FundamentalPropertyOverRules :=
  fun Δ Γ e T hD => fundamental_in Δ Γ e T (hreg Δ Γ e T hD)

/-! Lemma 6.151 (Fundamental Property), literal reading, continued. -/
/-- **The bridge is refused at the same node `EveryDerivationInRegime` is.**
`witness` is `∅; • ⊢ λ().() : ∀('a ⊏ 'a). 1`, which `Derives` admits because it
is the printed rules and nothing else; `DerivesWf.allI` reads p. 2's own
`Δ ⊧ @b` beside `'a ∉ dom(Δ)` and refuses it.  So `fundamental` reaches
`FundamentalPropertyOverRules` no more directly than `fundamental_in` does —
what stands between them is the presupposition, at both, and it is the reason
`FundamentalProperty` is stated at the presupposed judgment instead.
`[about ours: `EveryDerivationWf` refused at `witness`]` -/
theorem not_everyDerivationWf : ¬ EveryDerivationWf := by
  intro hwf
  exact auxWf (hwf _ _ _ _ witness) rfl (by simp [stripBox])

end BoCa.Fig16.LogRel

namespace BoCa.TR3
open BoCa.Fig16
open BoCa.BoLo (Heap)
open BoCa.Fig16.BoLo (Entails sep wand all box top ptoOwn ptoMut ptoImm outlives_comp NoOwn noOwn_empty noOwn_compS hash_lower hash_valid hash_valid_comp hash_shift updV_compS_own hash_compS_own lower_compS_own_inv lower_get_own lower_eq_none_iff get_eq_none_of_flat get_eq_none_of_compatS_own compatS_single_of_get_none loc_infinite compS_reassoc compS_reassoc' compS_exch compS_lcomm updV_frame updV_outlives)

/-!
### Lemma 6.154 (1E-compat) — literal reading

The printed statement, the printed proof and the adjudication are in `Paper/S6_8_FundamentalProperty/Lemmas.lean`, under the record of Lemma 6.154 (1E-compat).
-/
/-- `Δ; • ⊢ (free (alloc ())); () : 1`.  `1E` types `e₁; e₂` at *any* `e₁ : 1`,
so §3c's gap is a class of well typed terms and not a corner case.
`[as printed]` (`[TR]` p. 2's `1E`) -/
theorem derives_wSeq (Δ : BoCa.Lifetime.LifeCtx) :
    Derives Δ [] wSeq .unit :=
  .unitE .nil (derives_wFreeAlloc Δ) (.unitI .nil)

end BoCa.TR3

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-! Lemma 6.154 (1E-compat), literal reading, continued. -/
/-- **6.154 (`1E-compat`) is unreachable over §3 read as exact — which is the
measure of §3's elision, not of 6.154.**  Both premises hold at
`Γ₁ = Γ₂ = ∅`, `e₁ = free (alloc ())`, `e₂ = ()`, `T = 1` — a closed instance
`[TR]` p. 2's `1E` types (`TR3.derives_wSeq`) — and the conclusion cannot:
`[TR]` p. 3 prints no `K; e` frame and the printed `1↦` fires only at a literal
`()`, so `(free (alloc ())); ()` is stuck beside its own redex.
`docs/boca-rules.md` §12.42 settles which reading that argues for: §3 is
**elided**, since read as exact it makes `[CONF]` Corollary 3.3 unreachable too.
So this is a fact about the seven productions `BoCa/TR3.lean` transcribes
literally, and 6.154 is not in question.
`[about ours: 6.154's own statement, over `BoCa/TR3.lean`'s literal reading of
an elided figure]` -/
theorem unitE_refuted_on_TR3 (δ : LSub) :
    TR3.wp TR3.wFreeAlloc (vDen .unit δ) PMap.empty
    ∧ TR3.wp (.val .unit) (vDen .unit δ) PMap.empty
    ∧ ¬ TR3.wp TR3.wSeq (vDen .unit δ) PMap.empty :=
  ⟨tr3_eDen_freeAlloc δ,
   TR3.wp_val .unit (vDen .unit δ) PMap.empty ⟨rfl, rfl⟩,
   TR3.wp_seq_false hash_empty _ (by simp [TR3.wFreeAlloc]) _⟩

/-!
### Lemma 6.155 (⊗I-compat) — literal reading

The printed statement, the printed proof and the adjudication are in `Paper/S6_8_FundamentalProperty/Lemmas.lean`, under the record of Lemma 6.155 (⊗I-compat).
-/
/-- **`[TR]` 6.155 (`⊗I-compat`)'s last step goes through on the printed
machine.**  Both premises are `wp-val` at `()`, so no evaluation order is at
issue and the two frames the proof binds with, `(K,e)` and `(v,K)`, are never
reached.  `[TR]`'s own last step — `wp-val` at the *expression* `(v₁,v₂)`, which
`[CONF]` Fig. 1 takes silently because its grammar derives `(v₁,v₂)` both
through `v` and through `(e₁,e₂)` — is `wp-val` at the value, the two being one
term here.  This row used to be refuted over the printed machine, and the
refutation was our encoding's and not the print's.
`[about ours: 6.155's own last step, over `BoCa/TR3.lean`'s printed machine]` -/
theorem tensorI_step_on_TR3 (Q : Val → WProp) {ρ : WRes}
    (h : Q (Val.pair Val.unit Val.unit) ρ) :
    TR3.wp (.pair (.val .unit) (.val .unit)) Q ρ :=
  TR3.wp_val (Val.pair Val.unit Val.unit) Q ρ h

end BoCa.Fig16.LogRel

namespace BoCa.TR3
open BoCa.Fig16
open BoCa.BoLo (Heap)
open BoCa.Fig16.BoLo (Entails sep wand all box top ptoOwn ptoMut ptoImm outlives_comp NoOwn noOwn_empty noOwn_compS hash_lower hash_valid hash_valid_comp hash_shift updV_compS_own hash_compS_own lower_compS_own_inv lower_get_own lower_eq_none_iff get_eq_none_of_flat get_eq_none_of_compatS_own compatS_single_of_get_none loc_infinite compS_reassoc compS_reassoc' compS_exch compS_lcomm updV_frame updV_outlives)

/-!
### Lemma 6.157 (⊕I-compat) — literal reading

The printed statement, the printed proof and the adjudication are in `Paper/S6_8_FundamentalProperty/Lemmas.lean`, under the record of Lemma 6.157 (⊕I-compat).
-/
/-- `Δ; • ⊢ inj₁ (free (alloc ())) : 1 ⊕ T`, closed and at every `Δ` and `T`.
`[as printed]` (`[TR]` p. 2's `⊕I`, as `BoCa/Derives.lean` transcribes it) -/
theorem derives_wInj (Δ : BoCa.Lifetime.LifeCtx) (T : Ty) :
    Derives Δ [] wInj (.sum .unit T) :=
  .sumI₁ (derives_wFreeAlloc Δ)

end BoCa.TR3

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-! Lemma 6.157 (⊕I-compat), literal reading, continued. -/
/-- **6.157 (`⊕I-compat`) is unreachable over §3 read as exact**, for the same
reason as 6.154 above and with the same verdict.  The premise holds at
`Γ = ∅`, `e = free (alloc ())`, `T₁ = T₂ = 1`, and the conclusion cannot:
`[TR]` p. 3 prints no `injᵢ K`, so `inj₁ (free (alloc ()))` — which `[TR]`
p. 2's `⊕I` types (`TR3.derives_wInj`) — is stuck.  `docs/boca-rules.md` §12.42:
§3 is elided, so this measures the elision and not 6.157.
`[about ours: 6.157's own statement, over `BoCa/TR3.lean`'s literal reading of
an elided figure]` -/
theorem sumI₁_refuted_on_TR3 (δ : LSub) :
    TR3.wp TR3.wFreeAlloc (vDen .unit δ) PMap.empty
    ∧ ¬ TR3.wp TR3.wInj (vDen (.sum .unit .unit) δ) PMap.empty :=
  ⟨tr3_eDen_freeAlloc δ,
   TR3.wp_inj₁_false hash_empty TR3.wFreeAlloc
     (fun hv => Prim.noConfusion (Expr.prim.inj hv.app_fun)) _⟩

end BoCa.Fig16.LogRel

namespace BoCa.Fig16.LogRel.MutGapClosed
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
### Lemma 6.162 (∀E-compat) — literal reading

The printed statement, the printed proof and the adjudication are in `Paper/S6_8_FundamentalProperty/Lemmas.lean`, under the record of Lemma 6.162 (∀E-compat).
-/
/-- **…and therefore so do the two `Mut` types.**  On `ResI` this is false
(`LogRel.MutGap.rhs_fails`), which is what forces `LogRel`'s `Ty.MutClosed`; on
the printed carrier it is `vDen_mut_congr` and one page reference.
`[about ours: `LogRel` §9a's counterexample, at the printed cell]` -/
theorem gap_closed (δ : LSub) :
    vDen (Tgap.applyLSub [(0, .top)]) δ = vDen Tgap (δ.extend 0 Life.top) := by
  show vDen (.mut .top (.imm .top .unit)) δ
      = vDen (.mut .top (.imm (.var 0) .unit)) (δ.extend 0 Life.top)
  exact (vDen_mut_congr (δ₁ := δ.extend 0 Life.top) (δ₂ := δ)
    (a₁ := .top) (a₂ := .top) rfl (imm_eq δ)).symm

end BoCa.Fig16.LogRel.MutGapClosed

namespace BoCa.Fig16.LogRel
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-!
### Lemma 6.169 (swap-compat) — literal reading

The printed statement, the printed proof and the adjudication are in `Paper/S6_8_FundamentalProperty/Lemmas.lean`, under the record of Lemma 6.169 (swap-compat).
-/
/-- **6.169 (`swap-compat`) reaches a term the printed machine cannot step.**
`swap`'s type is a `⊸`, so its row is not stateable over the printed machine
without a second `𝒱` (see the section header); what is checked is the step
`[TR]` p. 44's own proof takes.  After `wp-⊸` twice, `wp-bind` at `e K` and
`wp-load`, the goal is a `wp` at `store ℓ v; (ℓ, z)` — `[CONF]` Fig. 3b's body,
and `[TR]` p. 4's own `swap` has the same shape — whose left component is not
`()`, so `1↦` does not fire and there is no `K; e` frame to bind it under.
`[about ours: 6.169's own proof at its `;`, over `BoCa/TR3.lean`'s machine]` -/
theorem swap_step_blocked_on_TR3 (ℓ : BoCa.Loc) (v : Val) (e : Expr)
    (Q : Val → WProp) {ρ ρf : WRes} (hf : ResU.Hash ρf ρ) :
    ¬ TR3.wp (.seq (.app (.app (.val (.prim .store)) (.val (.loc ℓ)))
        (.val v)) e) Q ρ :=
  TR3.wp_seq_false hf e (by simp) Q

/-!
### Lemma 6.170 (copy-compat) — literal reading

The printed statement, the printed proof and the adjudication are in `Paper/S6_8_FundamentalProperty/Lemmas.lean`, under the record of Lemma 6.170 (copy-compat).
-/
/-- **6.170 (`copy-compat`) reaches a term the printed machine handles.**  Same
caveat as `swap`: `copy : Imm @a T ⊸ (Imm @a T ⊗ Imm @a T)` is a `⊸`, so the row
is not stateable over the printed machine.  No evaluation context is reached at
all — `copy ≜ λx.(x,x)` β-reduces straight to `(v,v)`, which IS the value
`(v,v)` — so the step 6.155 needs is `wp-val` and this row is no longer blocked.
`[about ours: 6.170's own proof at its `(v,v)`, over `BoCa/TR3.lean`'s
machine]` -/
theorem copy_step_on_TR3 (v : Val) (Q : Val → WProp) {ρ : WRes}
    (h : Q (Val.pair v v) ρ) :
    TR3.wp (.pair (.val v) (.val v)) Q ρ :=
  TR3.wp_val (Val.pair v v) Q ρ h

end BoCa.Fig16.LogRel

namespace BoCa.Fig16.LogRel.ViewWitness
open BoCa
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-! `[about ours]` — what the Lean of Lemma 6.151 needs; the paper prints nothing here. -/
theorem step_app_inv {μ μ' : Heap} {f a e' : Expr} (h : Step1 μ (.app f a) μ' e') :
    Head μ (.app f a) μ' e' ∨ (∃ a', Step1 μ a μ' a' ∧ e' = .app f a') ∨
      (∃ (v : Val) (f' : Expr), a = v.1 ∧ Step1 μ f μ' f' ∧ e' = .app f' a) := by
  obtain ⟨K, x, x', hE, hE', hh⟩ := h
  cases K with
  | hole => rw [Kont.plug_hole] at hE hE'; subst hE hE'; exact .inl hh
  | appR g K =>
      simp only [Kont.plug] at hE hE'
      obtain ⟨rfl, rfl⟩ := Expr.app.inj hE
      exact .inr (.inl ⟨K.plug x', ⟨K, x, x', rfl, rfl, hh⟩, hE'⟩)
  | appL K v =>
      simp only [Kont.plug] at hE hE'
      obtain ⟨rfl, rfl⟩ := Expr.app.inj hE
      exact .inr (.inr ⟨v, K.plug x', rfl, ⟨K, x, x', rfl, rfl, hh⟩, hE'⟩)
  | pairL => simp [Kont.plug] at hE
  | pairR => simp [Kont.plug] at hE
  | letpair => simp [Kont.plug] at hE
  | case => simp [Kont.plug] at hE
  | seq => simp [Kont.plug] at hE
  | inj₁ => simp [Kont.plug] at hE
  | inj₂ => simp [Kont.plug] at hE

theorem step_seq_inv {μ μ' : Heap} {a b e' : Expr} (h : Step1 μ (.seq a b) μ' e') :
    Head μ (.seq a b) μ' e' ∨ (∃ a', Step1 μ a μ' a' ∧ e' = .seq a' b) := by
  obtain ⟨K, x, x', hE, hE', hh⟩ := h
  cases K with
  | hole => rw [Kont.plug_hole] at hE hE'; subst hE hE'; exact .inl hh
  | seq K e =>
      simp only [Kont.plug] at hE hE'
      obtain ⟨rfl, rfl⟩ := Expr.seq.inj hE
      exact .inr ⟨K.plug x', ⟨K, x, x', rfl, rfl, hh⟩, hE'⟩
  | appR => simp [Kont.plug] at hE
  | appL => simp [Kont.plug] at hE
  | pairL => simp [Kont.plug] at hE
  | pairR => simp [Kont.plug] at hE
  | letpair => simp [Kont.plug] at hE
  | case => simp [Kont.plug] at hE
  | inj₁ => simp [Kont.plug] at hE
  | inj₂ => simp [Kont.plug] at hE

theorem step_letpair_inv {μ μ' : Heap} {a b e' : Expr} (h : Step1 μ (.letpair a b) μ' e') :
    Head μ (.letpair a b) μ' e' ∨ (∃ a', Step1 μ a μ' a' ∧ e' = .letpair a' b) := by
  obtain ⟨K, x, x', hE, hE', hh⟩ := h
  cases K with
  | hole => rw [Kont.plug_hole] at hE hE'; subst hE hE'; exact .inl hh
  | letpair K e =>
      simp only [Kont.plug] at hE hE'
      obtain ⟨rfl, rfl⟩ := Expr.letpair.inj hE
      exact .inr ⟨K.plug x', ⟨K, x, x', rfl, rfl, hh⟩, hE'⟩
  | appR => simp [Kont.plug] at hE
  | appL => simp [Kont.plug] at hE
  | pairL => simp [Kont.plug] at hE
  | pairR => simp [Kont.plug] at hE
  | seq => simp [Kont.plug] at hE
  | case => simp [Kont.plug] at hE
  | inj₁ => simp [Kont.plug] at hE
  | inj₂ => simp [Kont.plug] at hE

/-- A value takes no step (the `Val` form). -/
theorem no_step_isVal {μ μ' : Heap} {e e' : Expr} (hv : IsVal e) : ¬ Step1 μ e μ' e' :=
  fun h => BoCa.BoLo.no_step_val (w := ⟨e, hv⟩) h

/-- Beta at two values is the only step. -/
theorem step_beta_inv {μ μ' : Heap} {b : Expr} {v : Val} {e' : Expr}
    (h : Step1 μ (.app (.lam b) v.1) μ' e') : μ' = μ ∧ e' = b.subst 0 v := by
  rcases step_app_inv h with hh | ⟨a', ha, -⟩ | ⟨w, f', -, hf, -⟩
  · generalize hE : Expr.app (.lam b) v.1 = E at hh
    cases hh with
    | beta b' v' =>
        obtain ⟨h1, h2⟩ := Expr.app.inj hE
        have hb : b = b' := by simpa using h1
        have hv : v = v' := Subtype.ext h2
        subst hb hv; exact ⟨rfl, rfl⟩
    | alloc => simp at hE
    | free => simp at hE
    | load => simp at hE
    | store => simp at hE
    | seq => simp at hE
    | letpair => simp at hE
    | case₁ => simp at hE
    | case₂ => simp at hE
  · exact absurd ha (no_step_isVal v.2)
  · exact absurd hf (no_step_isVal .lam)

/-- `load ℓ` at two values is the only step. -/
theorem step_load_inv {μ μ' : Heap} {ℓ : Loc} {e' : Expr}
    (h : Step1 μ (.app (.prim .load) (.loc ℓ)) μ' e') :
    μ' = μ ∧ ∃ v : Val, μ ℓ = some v ∧ e' = v.1 := by
  rcases step_app_inv h with hh | ⟨a', ha, -⟩ | ⟨w, f', -, hf, -⟩
  · generalize hE : Expr.app (.prim .load) (.loc ℓ) = E at hh
    cases hh with
    | load l v hv =>
        obtain ⟨-, h2⟩ := Expr.app.inj hE
        have : ℓ = l := by simpa using h2
        subst this; exact ⟨rfl, v, hv, rfl⟩
    | beta => simp at hE
    | alloc => simp at hE
    | free => simp at hE
    | store => simp at hE
    | seq => simp at hE
    | letpair => simp at hE
    | case₁ => simp at hE
    | case₂ => simp at hE
  · exact absurd ha (no_step_isVal .loc)
  · exact absurd hf (no_step_isVal .prim)

/-- `store ℓ v` at two values is the only step. -/
theorem step_store_inv {μ μ' : Heap} {ℓ : Loc} {v : Val} {e' : Expr}
    (h : Step1 μ (.app (.app (.prim .store) (.loc ℓ)) v.1) μ' e') :
    μ' = μ.upd ℓ v ∧ e' = .unit := by
  rcases step_app_inv h with hh | ⟨a', ha, -⟩ | ⟨w, f', -, hf, -⟩
  · generalize hE : Expr.app (.app (.prim .store) (.loc ℓ)) v.1 = E at hh
    cases hh with
    | store l v' w hw =>
        obtain ⟨h1, h2⟩ := Expr.app.inj hE
        have hl : ℓ = l := by simpa using h1
        have hv : v = v' := Subtype.ext h2
        subst hl hv; exact ⟨rfl, rfl⟩
    | beta => simp at hE
    | alloc => simp at hE
    | free => simp at hE
    | load => simp at hE
    | seq => simp at hE
    | letpair => simp at hE
    | case₁ => simp at hE
    | case₂ => simp at hE
  · exact absurd ha (no_step_isVal v.2)
  · exact absurd hf (no_step_isVal (.storeV .loc))

/-- A deterministic first step can be peeled off a run to a value. -/
theorem steps_peel {μ μ'' m : Heap} {e e' : Expr} {v : Val}
    (hs : Steps μ e μ'' v.1) (hnv : ¬ IsVal e)
    (hu : ∀ μ₁ e₁, Step1 μ e μ₁ e₁ → μ₁ = m ∧ e₁ = e') : Steps m e' μ'' v.1 := by
  cases hs with
  | refl => exact absurd v.2 hnv
  | more h t => obtain ⟨rfl, rfl⟩ := hu _ _ h; exact t

/-- The payload's value at location `0`: `(1, ())`. -/
def v0 : Val := Val.pair (Val.loc 1) Val.unit

/-- `λr. (store 0 v0); let (_,_) = r in ()`: restores `0` and eliminates `r` as a
pair. -/
def C : Expr :=
  .seq (.app (.app (.prim .store) (.loc 0)) v0.1) (.letpair (.var 0) .unit)

/-- `y ⊢ (store 0 ()); (λr. C) (load y)`. -/
def B : Expr :=
  .seq (.app (.app (.prim .store) (.loc 0)) .unit) (.app (.lam C) (.app (.prim .load) (.var 0)))

/-- The callback `λ_. λy. B`. -/
def vf : Val := Val.lam (Val.lam B).1

theorem C_subst (j : Nat) (s : Val) : C.subst (j + 1) s = C := by
  simp [C, Expr.subst, v0, Val.pair, Val.loc, Val.unit]

theorem B_subst (k : Loc) : B.subst 0 (Val.loc k) =
    .seq (.app (.app (.prim .store) (.loc 0)) .unit) (.app (.lam C) (.app (.prim .load) (.loc k))) := by
  simp only [B, Expr.subst]
  rw [C_subst]
  simp [Val.loc]

theorem C_subst0 (w : Val) : C.subst 0 w =
    .seq (.app (.app (.prim .store) (.loc 0)) v0.1) (.letpair w.1 .unit) := by
  simp [C, Expr.subst, v0, Val.pair, Val.loc, Val.unit]

theorem vf_app : ((Val.lam B).1).subst 0 Val.unit = (Val.lam B).1 := by
  show Expr.lam (B.subst 1 _) = Expr.lam B
  simp only [B, Expr.subst]
  rw [show (1 : Nat) + 1 = 1 + 1 from rfl, C_subst]
  simp

macro "no_head" h:ident : tactic =>
  `(tactic| (generalize hE : _ = E at $h:ident; cases $h:ident <;> simp_all [Val.lam, Val.loc, Val.unit, Val.pair, Val.prim, vf, B, C, v0]))

/-- **The callback's run at a location other than `ℓ₀`.**  At `y = ℓ_k ≠ 0` whose
cell holds a pair, `B` stores `()` at `0`, reads `k`, restores `0` and
eliminates the pair: it returns `()` and leaves the memory as it found it. -/
theorem run_legit (μ : Heap) (k : Loc) (hk : k ≠ 0) (p q : Val)
    (h0 : μ 0 = some v0) (hkv : μ k = some (Val.pair p q)) :
    Steps μ (B.subst 0 (Val.loc k)) μ Val.unit.1 := by
  rw [B_subst]
  have hμ : (μ.upd 0 Val.unit).upd 0 v0 = μ := by
    funext l; by_cases e : l = 0
    · subst e; simp [h0]
    · simp [e]
  refine .more ⟨.seq .hole _, _, _, rfl, rfl, Head.store μ 0 Val.unit v0 h0⟩ ?_
  refine .more (Step1.head (Head.seq _ _)) ?_
  refine .more ⟨.appR (.lam C) .hole, _, _, rfl, rfl,
    Head.load (μ.upd 0 Val.unit) k (Val.pair p q) (by simp [hk, hkv])⟩ ?_
  refine .more (Step1.head (Head.beta _ C (Val.pair p q))) ?_
  rw [C_subst0]
  refine .more ⟨.seq .hole _, _, _, rfl, rfl,
    Head.store (μ.upd 0 Val.unit) 0 v0 Val.unit (by simp)⟩ ?_
  rw [hμ]
  refine .more (Step1.head (Head.seq _ _)) ?_
  refine .more (Step1.head (Head.letpair _ p q Expr.unit)) ?_
  exact .refl _ _

/-- `λf. f () (load ℓ₂)` — `withload` applied to `ℓ₂`. -/
def wlApplied : Expr := .app (.app (.var 0) .unit) (.app (.prim .load) (.loc 2))

/-- `let (_,_) = () in ()` is stuck. -/
theorem stuck_letpair (μ μ' : Heap) (r : Val) :
    ¬ Steps μ (.letpair .unit .unit) μ' r.1 := by
  intro hs
  generalize hR : r.1 = R at hs
  cases hs with
  | refl => exact not_isVal_letpair (hR ▸ r.2)
  | more h _ =>
      rcases step_letpair_inv h with hh | ⟨a', ha, -⟩
      · no_head hh
      · exact no_step_isVal .unit ha

/-- **The callback's run at `ℓ₀`, inside `withload`.**  With `ℓ₂ ↦ ℓ₀` in memory,
`(λf. f () (load ℓ₂)) vf` reaches `let (_,_) = () in ()` and stops. -/
theorem run_stuck (μ μ' : Heap) (r : Val) (h2 : μ 2 = some (Val.loc 0)) :
    ¬ Steps μ (.app (.lam wlApplied) vf.1) μ' r.1 := by
  intro hs
  -- beta
  have s1 := steps_peel hs (by intro h; cases h) (m := μ)
    (e' := .app (.app vf.1 .unit) (.app (.prim .load) (.loc 2)))
    (fun μ₁ e₁ h => by
      obtain ⟨rfl, rfl⟩ := step_beta_inv (v := vf) h
      exact ⟨rfl, by simp [wlApplied, Expr.subst, vf, Val.lam]⟩)
  -- load ℓ₂
  have s2 := steps_peel s1 (by intro h; cases h) (m := μ)
    (e' := .app (.app vf.1 .unit) (.loc 0))
    (fun μ₁ e₁ h => by
      rcases step_app_inv h with hh | ⟨a', ha, rfl⟩ | ⟨w, f', hw, -, -⟩
      · no_head hh
      · obtain ⟨rfl, v, hv, rfl⟩ := step_load_inv ha
        rw [h2] at hv; cases Option.some.inj hv; exact ⟨rfl, rfl⟩
      · exact absurd (hw ▸ w.2) (by intro h; cases h))
  -- `vf ()`
  have s3 := steps_peel s2 (by intro h; cases h) (m := μ)
    (e' := .app (Val.lam B).1 (.loc 0))
    (fun μ₁ e₁ h => by
      rcases step_app_inv h with hh | ⟨a', ha, -⟩ | ⟨w, f', -, hf, rfl⟩
      · no_head hh
      · exact absurd ha (no_step_isVal .loc)
      · obtain ⟨rfl, rfl⟩ := step_beta_inv (v := Val.unit) hf
        exact ⟨rfl, by rw [vf_app]⟩)
  -- beta into `B`
  have s4 := steps_peel s3 (by intro h; cases h) (m := μ) (e' := B.subst 0 (Val.loc 0))
    (fun μ₁ e₁ h => step_beta_inv (v := Val.loc 0) h)
  rw [B_subst] at s4
  -- store ℓ₀ ()
  have s5 := steps_peel s4 (by intro h; cases h) (m := μ.upd 0 Val.unit)
    (e' := .seq .unit (.app (.lam C) (.app (.prim .load) (.loc 0))))
    (fun μ₁ e₁ h => by
      rcases step_seq_inv h with hh | ⟨a', ha, rfl⟩
      · no_head hh
      · obtain ⟨rfl, rfl⟩ := step_store_inv (v := Val.unit) ha; exact ⟨rfl, rfl⟩)
  have s6 := steps_peel s5 (by intro h; cases h) (m := μ.upd 0 Val.unit)
    (e' := .app (.lam C) (.app (.prim .load) (.loc 0)))
    (fun μ₁ e₁ h => by
      rcases step_seq_inv h with hh | ⟨a', ha, -⟩
      · cases hh; exact ⟨rfl, rfl⟩
      · exact absurd ha (no_step_isVal .unit))
  -- load ℓ₀ reads the sentinel
  have s7 := steps_peel s6 (by intro h; cases h) (m := μ.upd 0 Val.unit)
    (e' := .app (.lam C) .unit)
    (fun μ₁ e₁ h => by
      rcases step_app_inv h with hh | ⟨a', ha, rfl⟩ | ⟨w, f', hw, -, -⟩
      · generalize hE : Expr.app (Expr.lam C) (Expr.app (Expr.prim Prim.load) (Expr.loc 0)) = E at hh
        cases hh with
        | beta b v =>
            obtain ⟨-, h2'⟩ := Expr.app.inj hE
            have hv : IsVal (Expr.app (.prim .load) (.loc 0)) := h2' ▸ v.2
            cases hv
        | _ => simp at hE
      · obtain ⟨rfl, v, hv, rfl⟩ := step_load_inv ha
        simp at hv; subst hv; exact ⟨rfl, rfl⟩
      · exact absurd (hw ▸ w.2) (by intro h; cases h))
  have s8 := steps_peel s7 (by intro h; cases h) (m := μ.upd 0 Val.unit)
    (e' := C.subst 0 Val.unit)
    (fun μ₁ e₁ h => step_beta_inv (v := Val.unit) h)
  rw [C_subst0] at s8
  have s9 := steps_peel s8 (by intro h; cases h) (m := (μ.upd 0 Val.unit).upd 0 v0)
    (e' := .seq .unit (.letpair .unit .unit))
    (fun μ₁ e₁ h => by
      rcases step_seq_inv h with hh | ⟨a', ha, rfl⟩
      · no_head hh
      · obtain ⟨rfl, rfl⟩ := step_store_inv (v := v0) ha; exact ⟨rfl, rfl⟩)
  have s10 := steps_peel s9 (by intro h; cases h) (m := (μ.upd 0 Val.unit).upd 0 v0)
    (e' := .letpair .unit .unit)
    (fun μ₁ e₁ h => by
      rcases step_seq_inv h with hh | ⟨a', ha, -⟩
      · cases hh; exact ⟨rfl, rfl⟩
      · exact absurd ha (no_step_isVal .unit))
  exact stuck_letpair _ _ _ s10

end BoCa.Fig16.LogRel.ViewWitness

namespace BoCa.Fig16.LogRel.ViewWitness
open BoCa
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `Δ₀ = ['a ⊏ 'b, 'b ⊏ ⊤]`. -/
def Δ₀ : LifeCtx := ⟨[(0, .var 1), (1, .top)]⟩

/-- `δ₀ = ['a ↦ 2, 'b ↦ 1]`. -/
def δ₀ : LSub := ⟨[(0, 2), (1, 1)]⟩

theorem models : Δ₀.Models δ₀ := by
  intro x u e
  match x with
  | 0 => cases e; exact ⟨2, 1, rfl, rfl, by simp [Lifetime.SLife.Lt]⟩
  | 1 => cases e; exact ⟨1, 0, rfl, rfl, by simp [Lifetime.SLife.Lt]⟩
  | (k+2) => exact absurd e (by simp [Δ₀, LifeCtx.find?, Lifetime.assocFind])

/-- `T₁ = Ref (Ref 1 ⊗ 1)`; its immutable reborrow is `Imm 'x (Ref 1 ⊗ 1)`. -/
def T₁ : Ty := .ref (.tensor (.ref .unit) .unit)

/-- The borrowed argument `ℓ₂ ↦ imm({1}, ℓ₀, ℓ₀↦own((ℓ₁,())) ⊎ ℓ₁↦own(()))`. -/
noncomputable def ρ₁ : WRes := ResU.single 2 (DefectB.cellB 1 v0 Val.unit (Val.loc 0))

/-- The callback's resource: the `imm` view `ℓ₀ ↦ imm({1}, (ℓ₁,()), ∅)`. -/
noncomputable def ρ₂ : WRes := ResU.single 0 (DefectB.cellF 1 v0)

theorem hc₁₂ : ResU.CompS ρ₁ ρ₂ (DefectB.comp 1 1 v0 Val.unit (Val.loc 0)) :=
  DefectB.bcell_frame_comp _ _ _ _ _

theorem hvalid : ResU.Valid (DefectB.comp 1 1 v0 Val.unit (Val.loc 0)) :=
  DefectB.Valid_composite _ _ _ _ _

theorem rho2_comp (v u : Val) :
    ResU.CompS (ResU.single 0 (CellU.ownOf v)) (ResU.single 1 (CellU.ownOf u))
      (DefectB.rho2 v u) := by
  refine ⟨ResU.Compat.of_disjoint (fun l => ?_), fun l => ?_⟩
  · by_cases e0 : l = 0
    · subst e0; exact Or.inr (ResU.single_get_ne _ (by decide))
    · exact Or.inl (ResU.single_get_ne _ e0)
  · by_cases e0 : l = 0
    · subst e0
      rw [ResU.single_get_ne _ (by decide : (0:Nat) ≠ 1), ResU.single_get_self, DefectB.rho2_0]
      exact rfl
    · by_cases e1 : l = 1
      · subst e1
        rw [ResU.single_get_self, ResU.single_get_ne _ (by decide : (1:Nat) ≠ 0),
          DefectB.rho2_1]
        exact rfl
      · rw [ResU.single_get_ne _ e1, ResU.single_get_ne _ e0, DefectB.rho2_ne _ _ e0 e1]
        exact rfl

theorem ref_unit_den (δ : LSub) (l : Loc) :
    vDen (.ref .unit) δ (Val.loc l) (ResU.single l (CellU.ownOf Val.unit)) :=
  ⟨l, Val.unit, pure_sep_mk rfl ⟨_, PMap.empty, ResU.comp_empty_right _, rfl, rfl, rfl⟩⟩

theorem payload_den (δ : LSub) :
    vDen T₁ δ (Val.loc 0) (DefectB.rho2 v0 Val.unit) := by
  refine ⟨0, v0, pure_sep_mk rfl ⟨_, _, rho2_comp v0 Val.unit, rfl, ?_⟩⟩
  refine ⟨Val.loc 1, Val.unit, pure_sep_mk rfl ⟨_, PMap.empty, ResU.comp_empty_right _,
    ref_unit_den δ 1, rfl, rfl⟩⟩

/-- `𝒱⟦Imm 'b T₁⟧δ₀(ℓ₂)` holds of `ρ₁`. -/
theorem arg_den : vDen (.imm (.var 1) T₁) δ₀ (Val.loc 2) ρ₁ :=
  ⟨1, rfl, 2, pure_sep_mk rfl ⟨_, _, _, _, rfl, payload_den δ₀, le_rfl⟩⟩

/-- A resource satisfying `𝒱⟦Ref 1⟧` has a cell. -/
theorem ref_has_cell {δ : LSub} {p : Val} {ρ : WRes} (h : vDen (.ref .unit) δ p ρ) :
    ∃ l ψ, ρ.get l = some ψ := by
  obtain ⟨l, v', h⟩ := h
  obtain ⟨-, ρa, ρb, hc, rfl, -⟩ := pure_sep_iff.mp h
  obtain ⟨ψ, hψ, -⟩ := compS_get_erase hc (ResU.single_get_self l _)
  exact ⟨l, ψ, hψ⟩

theorem pair_den_has_cell {δ : LSub} {pv : Val} {W : WRes}
    (h : vDen (.tensor (.ref .unit) .unit) δ pv W) : ∃ l ψ, W.get l = some ψ := by
  obtain ⟨p, q, h⟩ := h
  obtain ⟨-, ρx, ρy, hc, hx, -⟩ := pure_sep_iff.mp h
  obtain ⟨l, ψ, hψ⟩ := ref_has_cell hx
  obtain ⟨χ, hχ, -⟩ := compS_get_erase hc hψ
  exact ⟨l, χ, hχ⟩

/-- **A run that returns and leaves the memory alone discards its whole resource.**  The
`wp` row at `ρ′ := ∅`, `ρ⁺ := ρ`. -/
theorem wp_run_discard {e : Expr} {Q : Val → WProp} {ρ : WRes} {v : Val}
    (hno : NoOwn ρ) (hQ : Q v PMap.empty)
    (hrun : ∀ ρf fρ μ, ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → ResU.Lower fρ μ →
      Steps μ e μ v.1) : wp e Q ρ := by
  intro ρf hf
  obtain ⟨σ, μ, hσ, -, hμ⟩ := hash_lower hf
  have hvf := (hash_valid hf).1
  exact ⟨PMap.empty, ρ, σ, ρf, σ, ρ, v, μ, μ,
    ResU.hash_symm (ResU.hash_empty_right hvf), ResU.comp_empty_right ρf,
    ResU.hash_symm hf, hσ, hμ, hσ, hμ, hrun ρf σ μ hf hσ hμ,
    compS_empty_left ρ, (ResU.updV_self_iff ρ).mpr (hash_valid hf).2, hno, hQ⟩

/-- The memory reads a cell's value through two composites. -/
theorem lower_read {ρ ρc ρf fρ : WRes} {μ : Heap} {l : Loc} {ψ : CellU Loc Val}
    (e : ρ.get l = some ψ) (h₁ : ∃ ρo, ResU.CompS ρ ρo ρc) (h₂ : ResU.CompS ρf ρc fρ)
    (hμ : ResU.Lower fρ μ) : μ l = some ψ.erase := by
  obtain ⟨ρo, h₁⟩ := h₁
  obtain ⟨χ, hχ, e₁⟩ := compS_get_erase h₁ e
  obtain ⟨χ', hχ', e₂⟩ := compS_get_erase (ResU.CompS.comm h₂) hχ
  rw [lower_get hμ hχ', e₂, e₁]

/-- **The callback is in its type.**  Every argument `𝒱⟦Imm̲ 'x T₁⟧` admits is
`ℓ_k ↦ imm(_, (p,q), W)` with `W` carrying a cell, and one compatible with
`ρ₂`'s view at `ℓ₀` — whose witness is `∅` — has `k ≠ 0`; there `B` returns `()`
and leaves memory unchanged.
`[about ours: the callback at `ρ₂`, against `𝒱⟦∀'x ⊏ ⊓Δ₀. Imm̲ 'x T₁ ⊸ ['x] 1⟧`]` -/
theorem f_den : vDen (.all 2 Δ₀.meetOfDom
      (.lolli (Ty.immReborrow (.var 2) T₁) (.box (.var 2) .unit))) δ₀ vf ρ₂ := by
  intro α ρa ρb hp hc
  obtain ⟨rfl, -⟩ := hp
  have : ρb = ρ₂ := by
    have := ResU.CompS.comm hc
    exact eq_of_compS_empty_left this
  subst this
  refine wp_lolli _ _ _ _ ?_
  rw [vf_app]
  refine wp_val (Val.lam B) _ _ ?_
  intro v' ρa ρc harg hc
  obtain ⟨α', hα', k, hk⟩ := harg
  obtain ⟨rfl, s, pv, W, hs, rfl, hW, -⟩ := pure_sep_iff.mp hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    have hcs := hc.1
    have hW0 : W = PMap.empty :=
      (ResU.compatS_single_imm_inv (ResU.CompatS.symm hcs)).2
    obtain ⟨l, ψ, hψ⟩ := pair_den_has_cell hW
    rw [hW0] at hψ; exact absurd hψ (by simp)
  obtain ⟨p, q, hpq⟩ := hW
  obtain ⟨rfl, -⟩ := pure_sep_iff.mp hpq
  refine wp_lolli _ _ _ _ ?_
  refine wp_run_discard (v := Val.unit)
    (noOwn_compS hc (noOwn_single_imm _ _ _ _ _) (noOwn_single_imm _ _ _ _ _)) ?_ ?_
  · refine ⟨α, by rw [Lifetime.Life.interp_var, find?_extend_self]; rfl, ⟨rfl, rfl⟩, ?_⟩
    intro l ψ e; exact absurd e (by simp)
  · intro ρf fρ μ hf hfc hμ
    have h0 : μ 0 = some v0 :=
      lower_read (ψ := DefectB.cellF 1 v0) (ResU.single_get_self 0 _) ⟨_, hc⟩ hfc hμ
    have hkv : μ k = some (Val.pair p q) :=
      lower_read (ResU.single_get_self k _) ⟨_, ResU.CompS.comm hc⟩ hfc hμ
    exact run_legit μ k hk0 p q h0 hkv

/-- The withload value. -/
def wlVal : Val := Val.lam (Val.lam (.app (.app (.var 0) .unit) (.app (.prim .load) (.var 1)))).1

/-- `Δ₀ ⊨ withload : Imm 'b T₁ ⊸ (∀'x ⊏ ⊓Δ₀. Imm̲ 'x T₁ ⊸ ['x] 1) ⊸ 1` over
our `Sem`, at `T₁ = Ref (Ref 1 ⊗ 1)`.
`[about ours: `[TR]` 6.175's conclusion at one instance, over our `Sem`]` -/
def WithloadSem : Prop :=
  Sem Δ₀ [] withload (axWithloadTy (.var 1) 2 Δ₀.meetOfDom T₁ .unit)

/-- **Our carrier refuses `WithloadSem`.**  The argument is `ρ₁`, the callback
`vf` at `ρ₂`; `ρ₁ ● ρ₂` is `✓` (`DefectB.Valid_composite`), `vf` is in the
callback type (`f_den`), and the run gets stuck (`run_stuck`).
`[about ours: `WithloadSem` at the view-witness configuration]` -/
theorem withloadSem_refused : ¬ WithloadSem := by
  intro hs
  have hw := (sem_iff.mp hs) δ₀ [] PMap.empty models
    (gDen_mk (by simp [Ctx.LiveWithin]) emp_empty)
  -- stage 1: `withload` is a value; frame `ρ₁ ● ρ₂`
  obtain ⟨ρ', ρp, fρ, fρ', fρ'p, π, w₀, μ, μ', hH, -, -, -, -, -, -, hS, -, -, -, hQ⟩ :=
    hw _ (ResU.hash_empty_right hvalid)
  have hw₀ : w₀ = wlVal := by
    have := (BoCa.BoLo.steps_val_inv (w := wlVal) hS).2
    exact Subtype.ext this
  subst hw₀
  obtain ⟨x, hx, hHx⟩ := (hash_shift ρ₂ ρ₁ ρ').mpr
    ⟨_, ResU.CompS.comm hc₁₂, ResU.hash_symm hH⟩
  have hw₂ := hQ (Val.loc 2) ρ₁ x arg_den (ResU.CompS.comm hx)
  -- stage 2: `withload ℓ₂`; frame `ρ₂`
  obtain ⟨ρ'', ρp₂, fρ₂, fρ'₂, fρ'p₂, π₂, w₁, μ₂, μ₂', -, hc₂', hHp₂, hc₂, hμ₂, hc₂'p,
    hμ₂', hS₂, -, -, -, hQ₂⟩ := hw₂ ρ₂ hHx
  have s₂ := steps_peel hS₂ (by intro h; cases h) (m := μ₂) (e' := (Val.lam wlApplied).1)
    (fun μ₁ e₁ h => by
      obtain ⟨rfl, rfl⟩ := step_beta_inv (v := Val.loc 2) h
      exact ⟨rfl, by simp [wlApplied, Expr.subst, Expr.shift, Val.lam, Val.loc]⟩)
  obtain ⟨hμe, hwe⟩ := BoCa.BoLo.steps_val_inv (w := Val.lam wlApplied) s₂
  have hw₁ : w₁ = Val.lam wlApplied := Subtype.ext hwe
  subst hw₁
  rw [hμe] at hμ₂'
  -- the memory holds `ℓ₂ ↦ ℓ₀`
  have h2 : μ₂ 2 = some (Val.loc 0) :=
    lower_read (ψ := DefectB.cellB 1 v0 Val.unit (Val.loc 0)) (ResU.single_get_self 2 _)
      ⟨_, hx⟩ hc₂ hμ₂
  -- stage 3: `(withload ℓ₂) vf`; frame `ρ⁺` of stage 2
  have hw₃ := hQ₂ vf ρ₂ fρ'₂ f_den (ResU.CompS.comm hc₂')
  obtain ⟨-, -, fρ₃, -, -, -, r, μ₃, μ₃', -, -, -, hc₃, hμ₃, -, -, hS₃, -⟩ := hw₃ ρp₂ hHp₂
  have e₃ : fρ₃ = fρ'p₂ := ResU.CompS.functional hc₃ (ResU.CompS.comm hc₂'p)
  subst e₃
  have : μ₃ = μ₂ := ResU.Lower.functional hμ₃ hμ₂'
  rw [this] at hS₃
  exact run_stuck _ _ _ h2 hS₃

theorem derivesWf :
    DerivesWf Δ₀ [] withload (axWithloadTy (.var 1) 2 Δ₀.meetOfDom T₁ .unit) :=
  .withloadAx .nil 2 rfl (by decide)

theorem ok : Δ₀.Ok := by decide

theorem scopedNil : Ctx.ScopedB Δ₀ [] := fun _ hs => absurd hs (List.not_mem_nil)

/-! Lemma 6.151 (Fundamental Property), literal reading, continued. -/
/-- **Our `FundamentalProperty` is refused at the `withloadAx` node above.**
`[about ours: `FundamentalProperty` at the view-witness configuration]` -/
theorem fundamentalProperty_refused : ¬ FundamentalProperty := fun h =>
  withloadSem_refused (h _ _ _ _ derivesWf ok scopedNil)

end BoCa.Fig16.LogRel.ViewWitness

namespace BoCa.Fig16.LogRel.ViewWitness
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Typed
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! `[about ours]` — what the Lean of Lemma 6.151 needs; the paper prints nothing here. -/
/-- `T₁` names no lifetime, so the only type `TyEq` relates it to is itself. -/
theorem tyEq_T₁ {δ δ' : LSub} {S : Ty} (h : TyEq T₁ δ S δ') : S = T₁ := by
  cases S <;> simp [T₁, TyEq] at h ⊢
  rename_i A
  cases A <;> simp [TyEq] at h ⊢
  rename_i B C
  cases B <;> cases C <;> simp [TyEq] at h ⊢
  rename_i D
  cases D <;> simp [TyEq] at h ⊢

/-- `Ref 1 ⊗ 1`'s shape holds of no empty resource: the `Ref` holds a cell. -/
theorem not_vShape_pair_empty (δ : LSub) (u : Val) :
    ¬ vShape (.tensor (.ref .unit) .unit) δ u (PMap.empty : WRes) := by
  intro h
  obtain ⟨p, q, h⟩ := h
  obtain ⟨-, ρx, ρy, hc, hx, -⟩ := pure_sep_iff.mp h
  obtain ⟨l, v', hx⟩ := hx
  obtain ⟨-, ρa, ρb, hc', rfl, -⟩ := pure_sep_iff.mp hx
  obtain ⟨ψ, hψ, -⟩ := compS_get_erase hc' (ResU.single_get_self l _)
  obtain ⟨χ, hχ, -⟩ := compS_get_erase hc hψ
  exact absurd hχ (by simp)

/-- The view at `ℓ₀` and the borrow at `ℓ₂` show in `ag(W)` for every world `W` holding
`ρ₁ ● ρ₂`, over their values and witnesses. -/
theorem ag_cells {W F a : WRes}
    (hc : ResU.CompS (DefectB.comp 1 1 v0 Val.unit (Val.loc 0)) F W) (ha : AgW W a) :
    (∃ ζ : CellU Loc Val, a.get 0 = some ζ ∧ ζ.kind = Kind.imm ∧ ζ.erase = v0 ∧
      ζ.wit = PMap.empty) ∧
    (∃ ζ : CellU Loc Val, a.get 2 = some ζ ∧ ζ.kind = Kind.imm ∧ ζ.erase = Val.loc 0 ∧
      ζ.wit = DefectB.rho2 v0 Val.unit) := by
  obtain ⟨ψ₀, e₀, k₀, w₀, r₀⟩ := compS_get_left' hc (DefectB.comp_0 1 1 v0 Val.unit (Val.loc 0))
  obtain ⟨ψ₂, e₂, k₂, w₂, r₂⟩ := compS_get_left' hc (DefectB.comp_2 1 1 v0 Val.unit (Val.loc 0))
  obtain ⟨ζ₀, f₀, g₀, h₀, i₀, -⟩ := icpAt_agW ha 0 ψ₀ e₀ (k₀.trans (DefectB.cellF_kind 1 v0))
  obtain ⟨ζ₂, f₂, g₂, h₂, i₂, -⟩ := icpAt_agW ha 2 ψ₂ e₂ (k₂.trans (DefectB.cellB_kind 1 v0 Val.unit (Val.loc 0)))
  exact ⟨⟨ζ₀, f₀, g₀, h₀.trans (r₀.trans rfl), i₀.trans (w₀.trans (DefectB.cellF_wit 1 v0))⟩,
    ⟨ζ₂, f₂, g₂, h₂.trans (r₂.trans rfl), i₂.trans (w₂.trans (DefectB.cellB_wit 1 v0 Val.unit (Val.loc 0)))⟩⟩

/-- A record whose chain reaches `ℓ₀` at pointee `Ref 1 ⊗ 1` refuses the view there: its
witness `∅` is not of that shape (`DeepInv`). -/
theorem chain_refuses {W F a : WRes} {ps rs : List FrameRec} (hT : TI W ps rs) {r : FrameRec}
    (hr : r ∈ rs) {p : Option Loc} {u : Val}
    (hch : Chain r.R r.T r.v p 0 (.tensor (.ref .unit) .unit) u)
    (hc : ResU.CompS (DefectB.comp 1 1 v0 Val.unit (Val.loc 0)) F W) (ha : AgW W a) : False := by
  obtain ⟨⟨ζ, e, k, -, w⟩, -⟩ := ag_cells hc ha
  obtain ⟨-, hs, -⟩ := hT.1.1 r hr p 0 _ u hch a ha ζ e (by rw [k]; simp)
  rw [w] at hs
  exact not_vShape_pair_empty _ _ hs

/-! Lemma 6.151 (Fundamental Property), literal reading, continued. -/
/-- **The configuration of `ViewWitness` is excluded by the typed-world judgment.**  No typed
world holding `ρ₁ ● ρ₂` has the argument `ρ₁` in `𝒱X⟦Imm 'b T₁⟧` at its record list, at any
`δ`.  The argument's `CohE` names a record at `ℓ₂` of type `T₁` or a chain position there of
pointee `T₁`; either way the escrow `ℓ₀ ↦ own((ℓ₁,())) ⊎ ℓ₁ ↦ own(())` is a record's, `ℓ₀` is
a chain position of it at pointee `Ref 1 ⊗ 1`, and `DeepInv` asks the view there to be of that
shape — its witness `∅` is not.  So the run `withloadSem_refused` builds needs, at its second
stage, a world `wpTS` does not quantify over.
`[about ours: the view-witness configuration against `TW` and `𝒱X`]` -/
theorem excluded {W F : WRes} {ps : List FrameRec} {ls : List SRec} {δ : LSub}
    (hc : ResU.CompS (DefectB.comp 1 1 v0 Val.unit (Val.loc 0)) F W)
    (hW : TW W ps (rsOf ls)) (harg : vP (.imm (.var 1) T₁) ls δ (Val.loc 2) ρ₁) : False := by
  have hT := hW.inv
  obtain ⟨a, ha⟩ := agW_of_valid hW.valid
  obtain ⟨-, ⟨ζ₂, e₂, k₂, r₂, w₂⟩⟩ := ag_cells hc ha
  obtain ⟨α, -, ℓ, hℓ⟩ := harg
  obtain ⟨⟨hv, hcoh⟩, -⟩ := pure_sep_iff.mp hℓ
  have hℓ2 : ℓ = 2 := by injection hv with h; injection h with h; exact h.symm
  subst hℓ2
  obtain ⟨S₀, δ₀', he, hc₀⟩ := hcoh
  obtain rfl := tyEq_T₁ he
  have hstep : RefPos T₁ (Val.loc 0) 0 (.tensor (.ref .unit) .unit) := RefPos.ref _ 0
  rcases hc₀ with ⟨r, hr, hle, hTy, -⟩ | ⟨r, hr, p, u, hch, -⟩
  · -- a record at `ℓ₂`: its value and escrow are the borrow's
    obtain ⟨ψ, eψ, -, rψ, wψ⟩ := hT.leInvW r hr a ha
    rw [← hle, e₂] at eψ
    have hψ : ζ₂ = ψ := Option.some.inj eψ
    subst hψ
    have hv' : r.v = Val.loc 0 := rψ.symm.trans r₂
    have hR : r.R = DefectB.rho2 v0 Val.unit := wψ.symm.trans w₂
    have hch : Chain r.R r.T r.v none 0 (.tensor (.ref .unit) .unit) v0 := by
      rw [hv', ← hTy, hR]; exact Chain.one hstep (DefectB.rho2_0 _ _)
    exact chain_refuses hT hr hch hc ha
  · -- a chain position at `ℓ₂`: the pointee's next step is `ℓ₀`
    obtain ⟨e, he, hl⟩ := hT.exIn hr a ha
    obtain ⟨ζe, eζe, rζe, -⟩ := exR_cell he hch.own (by simp)
    obtain ⟨ζa, eζa, rζa, -⟩ := hl 2 ζe eζe
    rw [e₂] at eζa
    have hζ : ζ₂ = ζa := Option.some.inj eζa
    subst hζ
    have hu : u = Val.loc 0 := by
      have := rζa.trans rζe
      rw [r₂] at this
      simpa using this.symm
    subst hu
    obtain ⟨-, -, hown, -⟩ := hT.1.1 r hr p 2 T₁ _ hch a ha ζ₂ e₂ (by rw [k₂]; simp)
    have h0 : r.R.get 0 = some (CellU.ownOf v0) :=
      hown 0 v0 (by rw [w₂]; exact DefectB.rho2_0 _ _)
    exact chain_refuses hT hr (hch.snoc hstep h0) hc ha

end BoCa.Fig16.LogRel.ViewWitness

end
