import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S4_LogicalRelation.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Support.Lifetimes.Interpretation
import Support.Lifetimes.Substitution
import Support.LogicalRelation.ClosingSubstitutions
import Support.LogicalRelation.Facts
import Support.Model.Cells
import Support.Model.FlatteningCells
import Support.Model.Prelude
import Support.Model.Propositions
import Support.Model.Singletons
import Support.Model.Update
import Support.Model.Walks
import Support.TypedWorld.Images
import Support.TypedWorld.Records
import Support.TypedWorld.Relation
import Support.TypedWorld.World
import Support.TypedWorld.Wp

/-!
# Support — TypedWorld — RelationFacts

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
the repaired relation `𝒱X` read at substitutions (source `BoCa/TypedRel.lean`): monotonicity, the `imm` cell at the observable view, reading, writing and making a `mut` cell, 6.60 at `𝒱X`, congruence in `δ`, and the choosers' inputs.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

theorem TyEq.trans {S S' S'' : Ty} {δ δ' δ'' : LSub} (h : TyEq S δ S' δ')
    (h' : TyEq S' δ' S'' δ'') : TyEq S δ S'' δ'' := by
  induction S generalizing S' S'' δ δ' δ'' with
  | unit => cases S' <;> cases S'' <;> simp_all [TyEq]
  | unk => cases S' <;> cases S'' <;> simp_all [TyEq]
  | tensor A B ihA ihB =>
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact ⟨ihA h.1 h'.1, ihB h.2 h'.2⟩
  | sum A B ihA ihB =>
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact ⟨ihA h.1 h'.1, ihB h.2 h'.2⟩
  | lolli A B ihA ihB =>
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact ⟨ihA h.1 h'.1, ihB h.2 h'.2⟩
  | ref A ih =>
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact ih h h'
  | box a A ih =>
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact ⟨h.1.trans h'.1, ih h.2 h'.2⟩
  | imm a A ih =>
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact ⟨h.1.trans h'.1, ih h.2 h'.2⟩
  | «mut» a A ih =>
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact ⟨h.1.trans h'.1, ih h.2 h'.2⟩
  | all x b A ih =>
      cases S' <;> simp only [TyEq] at h
      cases S'' <;> simp only [TyEq] at h' ⊢
      exact ⟨h.1.trans h'.1, fun α => ih (h.2 α) (h'.2 α)⟩

theorem TyEq.of_agree : ∀ (T : Ty) {δ₁ δ₂ : LSub},
    (∀ y, LFree y T → δ₁.find? y = δ₂.find? y) → TyEq T δ₁ T δ₂
  | .unit, _, _, _ => trivial
  | .unk, _, _, _ => trivial
  | .tensor A B, _, _, h => ⟨TyEq.of_agree A (fun y hy => h y (Or.inl hy)),
      TyEq.of_agree B (fun y hy => h y (Or.inr hy))⟩
  | .sum A B, _, _, h => ⟨TyEq.of_agree A (fun y hy => h y (Or.inl hy)),
      TyEq.of_agree B (fun y hy => h y (Or.inr hy))⟩
  | .lolli A B, _, _, h => ⟨TyEq.of_agree A (fun y hy => h y (Or.inl hy)),
      TyEq.of_agree B (fun y hy => h y (Or.inr hy))⟩
  | .ref A, _, _, h => TyEq.of_agree A h
  | .box a A, _, _, h => ⟨interp_congr a (fun y hy => h y (Or.inl hy)),
      TyEq.of_agree A (fun y hy => h y (Or.inr hy))⟩
  | .imm a A, _, _, h => ⟨interp_congr a (fun y hy => h y (Or.inl hy)),
      TyEq.of_agree A (fun y hy => h y (Or.inr hy))⟩
  | .mut a A, _, _, h => ⟨interp_congr a (fun y hy => h y (Or.inl hy)),
      TyEq.of_agree A (fun y hy => h y (Or.inr hy))⟩
  | .all x b A, δ₁, δ₂, h => by
      refine ⟨interp_congr b (fun y hy => h y (Or.inl hy)), fun α => ?_⟩
      refine TyEq.of_agree A (fun y hy => ?_)
      by_cases hxy : x = y
      · subst hxy; rw [find?_extend_self, find?_extend_self]
      · rw [find?_extend_ne _ _ hxy, find?_extend_ne _ _ hxy]
        exact h y (Or.inr ⟨Ne.symm hxy, hy⟩)

theorem TyEq.refl (T : Ty) (δ : LSub) : TyEq T δ T δ := TyEq.of_agree T (fun _ _ => rfl)

theorem cohE_of_coh {rs : List FrameRec} {m : Loc} {S : Ty} {δ : LSub} (h : Coh rs m S δ) :
    CohE rs m S δ := ⟨S, δ, TyEq.refl S δ, h⟩

theorem CohE.tyEq {rs : List FrameRec} {m : Loc} {S S' : Ty} {δ δ' : LSub}
    (he : TyEq S δ S' δ') (h : CohE rs m S' δ') : CohE rs m S δ := by
  obtain ⟨S₀, δ₀, he₀, hc⟩ := h
  exact ⟨S₀, δ₀, he.trans he₀, hc⟩

theorem cohE_keeps {rs rs' : List FrameRec} {l : Loc} {S : Ty} {δ : LSub} {ψ : CellU Loc Val}
    (hk : Keeps rs rs' (ResU.single l ψ)) (hψ : ψ.kind = Kind.imm) (h : CohE rs l S δ) :
    CohE rs' l S δ := by
  obtain ⟨S₀, δ₀, he, hc⟩ := h
  exact ⟨S₀, δ₀, he, coh_keeps hk hψ hc⟩

end BoCa.Fig16.LogRel.Typed

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
variable {wpX : WpOp}

/-- **`𝒱X` is stable along `Ext`**, in both modes: at a `mut` cell the stored list is kept, so
the predicate stays equal; the `⊸`/`∀` clauses are Kripke in the list, and those of the
observable view are `True`. -/
theorem vX_local : ∀ (b : Bool) (T : Ty) {ls ls' : List SRec} {δ : LSub} {v : Val} {ρ : WRes},
    Ext ls ls' ρ → vX wpX b T ls δ v ρ → vX wpX b T ls' δ v ρ
  | _, .unit, _, _, _, _, _, _, h => h
  | b, .tensor T₁ T₂, _, _, _, _, _, hk, h => by
      obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ := h
      have hk' := hk.right hc
      exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc',
        vX_local b T₁ (hk'.left hc') h₁, vX_local b T₂ (hk'.right hc') h₂⟩
  | b, .sum T₁ T₂, _, _, _, _, _, hk, h => by
      rcases h with ⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩
      · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, vX_local b T₁ (hk.right hc) h₁⟩
      · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, vX_local b T₂ (hk.right hc) h₂⟩
  | true, .lolli T₁ T₂, _, _, _, _, _, hk, h => fun ls'' hk' => h ls'' (hk.trans hk')
  | false, .lolli _ _, _, _, _, _, _, _, h => h
  | true, .all x c T, _, _, _, _, _, hk, h => fun ls'' hk' => h ls'' (hk.trans hk')
  | false, .all _ _ _, _, _, _, _, _, _, h => h
  | b, .box a T, _, _, _, _, _, hk, h => by
      obtain ⟨α, hα, hb, ho⟩ := h
      exact ⟨α, hα, vX_local b T hk hb, ho⟩
  | b, .ref T, _, _, _, _, _, hk, h => by
      obtain ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩ := h
      exact ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho,
        vX_local b T ((hk.right hc).right hc') h₂⟩
  | _, .imm a T, ls, ls', _, _, _, hk, h => by
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv, hcoh⟩, s, u, σ, hs, ls₀, hρ₁, hP, hαs, hls₀⟩ := h
      subst hρ₀
      have hρ₁' := eq_of_compS_empty_left hc
      subst hρ₁'
      subst hρ₁
      have hk₁ : Keeps (rsOf _) (rsOf _) _ := hk.1
      have hcell : CellIn (ResU.single ℓ (CellU.immOf s u σ hs)) s.meet :=
        CellIn.single (by simp)
      refine ⟨α, hα, ℓ, _, _, hc, ⟨rfl, hv, cohE_keeps hk₁ (CellU.kind_immOf _ _ _ _) hcoh⟩,
        s, u, σ, hs, ls₀, rfl, hP, hαs, fun x => ?_⟩
      rw [hls₀ x]
      exact ⟨fun ⟨hx, hb⟩ => ⟨(hk.2 _ hcell x hb).mp hx, hb⟩,
             fun ⟨hx, hb⟩ => ⟨(hk.2 _ hcell x hb).mpr hx, hb⟩⟩
  | _, .mut a T, ls, ls', _, _, _, hk, h => by
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv⟩, b, u, σ, hσ, Q, hw, ls₀, hab, hρ₁, hQ, hls₀,
        hunif⟩ := h
      subst hρ₀
      have hk₁ := hk.right hc
      have hmut : CellIn ρ₁ b :=
        ⟨ℓ, _, by rw [hρ₁]; exact ResU.single_get_self _ _, by simp, le_rfl⟩
      refine ⟨α, hα, ℓ, _, _, hc, ⟨rfl, hv⟩, b, u, σ, hσ, Q, hw, ls₀, hab, hρ₁, hQ, ?_, hunif⟩
      intro x
      rw [hls₀ x]
      exact ⟨fun ⟨hx, hb⟩ => ⟨(hk₁.2 b hmut x hb).mp hx, hb⟩,
             fun ⟨hx, hb⟩ => ⟨(hk₁.2 b hmut x hb).mpr hx, hb⟩⟩
  | _, .unk, _, _, _, _, _, _, h => h

/-- **The program's relation implies the observable view** — the relaxation is a
weakening. -/
theorem vO_obs : ∀ (T : Ty) {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes},
    vX wpX true T ls δ v ρ → vX wpX false T ls δ v ρ
  | .unit, _, _, _, _, h => h
  | .tensor T₁ T₂, _, _, _, _, h => by
      obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ := h
      exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', vO_obs T₁ h₁, vO_obs T₂ h₂⟩
  | .sum T₁ T₂, _, _, _, _, h => by
      rcases h with ⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩
      · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, vO_obs T₁ h₁⟩
      · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, vO_obs T₂ h₂⟩
  | .lolli _ _, _, _, _, _, _ => trivial
  | .all _ _ _, _, _, _, _, _ => trivial
  | .box a T, _, _, _, _, h => by
      obtain ⟨α, hα, hb, ho⟩ := h
      exact ⟨α, hα, vO_obs T hb, ho⟩
  | .ref T, _, _, _, _, h => by
      obtain ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩ := h
      exact ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, vO_obs T h₂⟩
  | .imm _ _, _, _, _, _, h => h
  | .mut _ _, _, _, _, _, h => h
  | .unk, _, _, _, _, h => h

/-- **`𝒱X ⊆ vShape`**, both modes. -/
theorem vX_vShape : ∀ (b : Bool) (T : Ty) {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes},
    vX wpX b T ls δ v ρ → vShape T δ v ρ
  | _, .unit, _, _, _, _, h => h
  | b, .tensor T₁ T₂, _, _, _, _, h => by
      obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ := h
      exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', vX_vShape b T₁ h₁, vX_vShape b T₂ h₂⟩
  | b, .sum T₁ T₂, _, _, _, _, h => by
      rcases h with ⟨v₁, ρ₀, ρ₁, hc, hp, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hp, h₂⟩
      · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hp, vX_vShape b T₁ h₁⟩
      · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hp, vX_vShape b T₂ h₂⟩
  | true, .lolli _ _, _, _, _, _, _ => trivial
  | false, .lolli _ _, _, _, _, _, _ => trivial
  | true, .all _ _ _, _, _, _, _, _ => trivial
  | false, .all _ _ _, _, _, _, _, _ => trivial
  | b, .box a T, _, _, _, _, h => by
      obtain ⟨α, hα, hb, ho⟩ := h
      exact ⟨α, hα, vX_vShape b T hb, ho⟩
  | b, .ref T, _, _, _, _, h => by
      obtain ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩ := h
      exact ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, vX_vShape b T h₂⟩
  | _, .imm a T, _, _, _, _, h => by
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv, -⟩, s, u, σ, hs, _ls₀, hρ, hP, hle, -⟩ := h
      exact ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv⟩, s, u, σ, hs, hρ, vX_vShape false T hP, hle⟩
  | _, .mut a T, _, _, _, _, h => by
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, b, u, σ, hσ, Q, hw, ls₀, hab, hρ, hQ, -, -⟩ := h
      refine ⟨α, hα, ℓ, ρ₀, ρ₁, hc, hp, ofS Q, ⟨b, u, σ, hσ, Q, hw, hab, hρ, rfl⟩, ?_⟩
      intro u' σ' h'
      rw [hQ] at h'
      exact vX_vShape true T h'
  | _, .unk, _, _, _, _, h => h

end BoCa.Fig16.LogRel.Typed

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-!
### Lemma 6.113 (I-mono) — typed-world version

The printed statement, the printed proof and the adjudication are in `Paper/S6_5_NonStandardEntailments/Lemmas.lean`, under the record of Lemma 6.113 (I-mono).
-/
/-- **`ptoImmS` is monotone in its payload.**  6.172 (`withbor1`) frames a payload at the
program's relation (6.64 at `𝒱X true`); the relation's `Imm` clause asks it at the
observable view. -/
theorem ptoImmS_mono {l : Loc} {α : Life} {ls : List SRec} {P P' : List SRec → Val → WProp}
    (h : ∀ ls₀ u σ, P ls₀ u σ → P' ls₀ u σ) {ρ : WRes} (hp : ptoImmS l α ls P ρ) :
    ptoImmS l α ls P' ρ := by
  obtain ⟨s, u, σ, hs, ls₀, hρ, hP, hα, hls₀⟩ := hp
  exact ⟨s, u, σ, hs, ls₀, hρ, h _ _ _ hP, hα, hls₀⟩

end BoCa.Fig16.LogRel.Typed

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
variable {wpX : WpOp}

/-- **Reading an `imm` cell at the observable view**: the payload is observable-valid at
the current list. -/
theorem ptoImmO_read {l : Loc} {α : Life} {ls : List SRec} {S : Ty} {δ : LSub} {ρ : WRes}
    (h : ptoImmS l α ls (fun ls₀ => vX wpX false S ls₀ δ) ρ) :
    ∃ (s : LSet) (u : Val) (σ : WRes) (hs : σ.InStratum s.join),
      ρ = ResU.single l (CellU.immOf s u σ hs) ∧ α ⊑ s.meet ∧ vX wpX false S ls δ u σ := by
  obtain ⟨s, u, σ, hs, ls₀, hρ, hP, hαs, hls₀⟩ := h
  exact ⟨s, u, σ, hs, hρ, hαs,
    vX_local false S (ext_stored_current hs s.meet_le_join hls₀) hP⟩

/-- **Making an `imm` cell at the observable view.** -/
theorem ptoImmO_make {l : Loc} {α : Life} {ls : List SRec} {S : Ty} {δ : LSub} {s : LSet}
    {u : Val} {σ : WRes} (hs : σ.InStratum s.join) (hαs : α ⊑ s.meet)
    (hv : vX wpX false S ls δ u σ) (hlb : LifeBound ls σ s.meet) :
    ptoImmS l α ls (fun ls₀ => vX wpX false S ls₀ δ) (ResU.single l (CellU.immOf s u σ hs)) := by
  refine ⟨s, u, σ, hs, ls.filter (fun x => decide (x.2 ⊐ s.meet)), rfl, ?_, hαs,
    fun x => by simp⟩
  refine vX_local false S ⟨fun r hr hrel => ?_, fun b' hb' x hx => ?_⟩ hv
  · obtain ⟨t, ht⟩ := mem_rsOf.mp hr
    exact mem_rsOf.mpr ⟨t, by simp [ht, hlb _ ht hrel]⟩
  · have hxb : x.2 ⊐ s.meet :=
      lt_trans (lt_of_le_of_lt s.meet_le_join (hb'.of_stratum hs)) hx
    simp [hxb]

theorem ptoMutX_read {l : Loc} {α : Life} {ls : List SRec} {S : Ty} {δ : LSub} {ρ : WRes}
    (h : ptoMutS l α ls (fun ls₀ => vX wpX true S ls₀ δ) ρ) :
    ∃ (b : Life) (u : Val) (σ : WRes) (hσ : σ.InStratum b) (Q : Val → SPropS Loc Val b)
      (hw : Q u ⟨σ, hσ⟩), ρ = ResU.single l (CellU.mutOf b u σ hσ Q hw) ∧
        vX wpX true S ls δ u σ := by
  obtain ⟨b, u, σ, hσ, Q, hw, ls₀, -, hρ, hQ, hls₀, -⟩ := h
  refine ⟨b, u, σ, hσ, Q, hw, hρ, ?_⟩
  have h₀ : vX wpX true S ls₀ δ u σ := by
    have : ofS Q u σ := ⟨hσ, hw⟩
    rw [hQ] at this; exact this
  exact vX_local true S (ext_stored_current hσ le_rfl hls₀) h₀

theorem ptoMutX_write {l : Loc} {α b : Life} {ls ls₀ : List SRec} {S : Ty} {δ : LSub}
    {Q : Val → SPropS Loc Val b} (hab : α ⊑ b) (hQ : ofS Q = fun v => vX wpX true S ls₀ δ v)
    (hls₀ : ∀ x, x ∈ ls₀ ↔ (x ∈ ls ∧ x.2 ⊐ b))
    (hunif : ∀ ls' u' σ', vX wpX true S ls' δ u' σ' → σ'.InStratum b)
    {u : Val} {σ : WRes} (hσ : σ.InStratum b) (hv : vX wpX true S ls δ u σ)
    (hlb : LifeBound ls σ b) :
    ∃ hw : Q u ⟨σ, hσ⟩, ptoMutS l α ls (fun ls₀ => vX wpX true S ls₀ δ)
      (ResU.single l (CellU.mutOf b u σ hσ Q hw)) := by
  have hext : Ext ls ls₀ σ := by
    refine ⟨fun r hr hrel => ?_, fun b' hb' x hx => ?_⟩
    · obtain ⟨t, ht⟩ := mem_rsOf.mp hr
      exact mem_rsOf.mpr ⟨t, (hls₀ _).mpr ⟨ht, hlb _ ht hrel⟩⟩
    · have hxb : x.2 ⊐ b := lt_trans (hb'.of_stratum hσ) hx
      exact ⟨fun h => (hls₀ x).mpr ⟨h, hxb⟩, fun h => ((hls₀ x).mp h).1⟩
  have h₀ : vX wpX true S ls₀ δ u σ := vX_local true S hext hv
  have hw : Q u ⟨σ, hσ⟩ := by
    have : ofS Q u σ := by rw [hQ]; exact h₀
    exact this.2
  exact ⟨hw, b, u, σ, hσ, Q, hw, ls₀, hab, rfl, hQ, hls₀, hunif⟩

theorem ptoMutX_create {l : Loc} {α b : Life} {ls : List SRec} {S : Ty} {δ : LSub}
    {Q : Val → SPropS Loc Val b} (hab : α ⊑ b) (hQ : ofS Q = fun v => vX wpX true S ls δ v)
    (hfresh : ∀ x ∈ ls, x.2 ⊐ b)
    (hunif : ∀ ls' u' σ', vX wpX true S ls' δ u' σ' → σ'.InStratum b)
    {u : Val} {σ : WRes} (hσ : σ.InStratum b) (hv : vX wpX true S ls δ u σ) :
    ∃ hw : Q u ⟨σ, hσ⟩, ptoMutS l α ls (fun ls₀ => vX wpX true S ls₀ δ)
      (ResU.single l (CellU.mutOf b u σ hσ Q hw)) := by
  have hw : Q u ⟨σ, hσ⟩ := by
    have : ofS Q u σ := by rw [hQ]; exact hv
    exact this.2
  exact ⟨hw, b, u, σ, hσ, Q, hw, ls, hab, rfl, hQ, strat_fresh hfresh, hunif⟩

end BoCa.Fig16.LogRel.Typed

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

theorem atLife_congr' {δ₁ δ₂ : LSub} {a : Lifetime.Life} {F : Life → WProp}
    (h : a.interp δ₁ = a.interp δ₂) : atLife δ₁ a F = atLife δ₂ a F := by
  unfold atLife; rw [h]

end BoCa.Fig16.LogRel.Typed

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
variable {wpX : WpOp}

/-- **`𝒱X⟦T⟧δ` depends on `δ` only at the variables free in `T`.** -/
theorem vX_congr : ∀ (T : Ty) {δ₁ δ₂ : LSub}, (∀ y, LFree y T → δ₁.find? y = δ₂.find? y) →
    ∀ (b : Bool) (ls : List SRec), vX wpX b T ls δ₁ = vX wpX b T ls δ₂
  | .unit, _, _, _, b, _ => by cases b <;> rfl
  | .unk, _, _, _, b, _ => by cases b <;> rfl
  | .tensor T₁ T₂, _, _, h, b, _ => by
      have h₁ := vX_congr T₁ (fun y hy => h y (Or.inl hy))
      have h₂ := vX_congr T₂ (fun y hy => h y (Or.inr hy))
      funext v; cases b <;> simp only [vX, h₁, h₂]
  | .sum T₁ T₂, _, _, h, b, _ => by
      have h₁ := vX_congr T₁ (fun y hy => h y (Or.inl hy))
      have h₂ := vX_congr T₂ (fun y hy => h y (Or.inr hy))
      funext v; cases b <;> simp only [vX, h₁, h₂]
  | .lolli T₁ T₂, _, _, h, b, _ => by
      have h₁ := vX_congr T₁ (fun y hy => h y (Or.inl hy))
      have h₂ := vX_congr T₂ (fun y hy => h y (Or.inr hy))
      funext v; cases b
      · rfl
      · simp only [vX, h₁, h₂]
  | .all x c T, δ₁, δ₂, h, b, _ => by
      have hc : c.interp δ₁ = c.interp δ₂ := interp_congr c (fun y hy => h y (Or.inl hy))
      have hT : ∀ (α : Life) (ls : List SRec),
          vX wpX true T ls (δ₁.extend x α) = vX wpX true T ls (δ₂.extend x α) := by
        intro α ls
        refine vX_congr T (fun y hy => ?_) true ls
        by_cases hxy : x = y
        · subst hxy; rw [find?_extend_self, find?_extend_self]
        · rw [find?_extend_ne _ _ hxy, find?_extend_ne _ _ hxy]
          exact h y (Or.inr ⟨Ne.symm hxy, hy⟩)
      have hL : ∀ α : Life, LtLife δ₁ c α = LtLife δ₂ c α := by intro α; unfold LtLife; rw [hc]
      funext v; cases b
      · rfl
      · simp only [vX, hT, hL]
  | .box a T, δ₁, δ₂, h, b, _ => by
      have ha : a.interp δ₁ = a.interp δ₂ := interp_congr a (fun y hy => h y (Or.inl hy))
      have ih := vX_congr T (fun y hy => h y (Or.inr hy))
      funext v; cases b <;> simp only [vX, ih, atLife_congr' ha]
  | .ref T, _, _, h, b, _ => by
      have ih := vX_congr T h
      funext v; cases b <;> simp only [vX, ih]
  | .imm a T, δ₁, δ₂, h, b, _ => by
      have ha : a.interp δ₁ = a.interp δ₂ := interp_congr a (fun y hy => h y (Or.inl hy))
      have ih := vX_congr T (fun y hy => h y (Or.inr hy))
      have hcoh : ∀ rs m, CohE rs m T δ₁ = CohE rs m T δ₂ := fun rs m => propext
        ⟨fun hc => hc.tyEq (TyEq.of_agree T (fun y hy => (h y (Or.inr hy)).symm)),
         fun hc => hc.tyEq (TyEq.of_agree T (fun y hy => h y (Or.inr hy)))⟩
      funext v; cases b <;> simp only [vX, ih, hcoh, atLife_congr' ha]
  | .mut a T, δ₁, δ₂, h, b, _ => by
      have ha : a.interp δ₁ = a.interp δ₂ := interp_congr a (fun y hy => h y (Or.inl hy))
      have ih := vX_congr T (fun y hy => h y (Or.inr hy))
      funext v; cases b <;> simp only [vX, ih, atLife_congr' ha]

theorem vX_extend_of_not_free {x : LifeVar} {T : Ty} (h : ¬ LFree x T) (b : Bool)
    (ls : List SRec) (δ : LSub) (α : Life) : vX wpX b T ls (δ.extend x α) = vX wpX b T ls δ :=
  vX_congr T (fun y hy => find?_extend_ne δ α (fun e => by subst e; exact h hy)) b ls

/-- At `Imm` the two modes are one clause. -/
theorem vX_imm_mode (a : Lifetime.Life) (S : Ty) (b b' : Bool) :
    vX wpX b (.imm a S) = vX wpX b' (.imm a S) := by
  cases b <;> cases b' <;> rfl

end BoCa.Fig16.LogRel.Typed

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **`B`'s cells are `R`'s**: same kind, witness and value, and a non-`imm` cell equal
(an `imm` cell may carry fewer lifetimes).  `[about ours]` -/
def CellMatch (R B : WRes) : Prop :=
  ∀ m ψ, B.get m = some ψ → ∃ ζ, R.get m = some ζ ∧ ζ.kind = ψ.kind ∧ ζ.wit = ψ.wit ∧
    ζ.erase = ψ.erase ∧ (ψ.kind ≠ Kind.imm → ζ = ψ)

theorem CellMatch.left {R B₁ B₂ B : WRes} (hc : ResU.CompS B₁ B₂ B) (h : CellMatch R B) :
    CellMatch R B₁ := by
  intro m ψ e
  obtain ⟨ψ', e', k', w', r'⟩ := compS_get_left' hc e
  obtain ⟨ζ, eζ, kζ, wζ, rζ, hζ⟩ := h m ψ' e'
  refine ⟨ζ, eζ, kζ.trans k', wζ.trans w', rζ.trans r', fun hk => ?_⟩
  have e'' := compS_get_left_nonImm hc e hk
  rw [e'] at e''; cases Option.some.inj e''
  exact hζ hk

theorem CellMatch.right {R B₁ B₂ B : WRes} (hc : ResU.CompS B₁ B₂ B) (h : CellMatch R B) :
    CellMatch R B₂ := CellMatch.left (ResU.CompS.comm hc) h

theorem CellMatch.of_le {R B : WRes} (h : ResU.Le B R) : CellMatch R B := by
  obtain ⟨τ, hτ⟩ := h
  intro m ψ e
  obtain ⟨ζ, eζ, kζ, wζ, rζ⟩ := compS_get_left' hτ e
  exact ⟨ζ, eζ, kζ, wζ, rζ, fun hk => by
    have e' := compS_get_left_nonImm hτ e hk
    rw [eζ] at e'; exact Option.some.inj e'⟩

theorem CellMatch.del {R B : WRes} (h : CellMatch R B) (l : Loc) : CellMatch R (B.del l) := by
  intro m ψ e
  by_cases hm : m = l
  · subst hm; rw [ResU.del_get_self] at e; cases e
  · rw [ResU.del_get_ne _ hm] at e; exact h m ψ e

/-- **Every witness of an `imm` cell of `R` is relevant only to records tagged longer-lived
than any lifetime it lies in.**  `[about ours: `lifeBound_of_tagged` at the witnesses
of an escrow's `imm` cells; the input the transfer consumes]` -/
def WitLB (ls : List SRec) (R : WRes) : Prop :=
  ∀ m ζ, R.get m = some ζ → ζ.kind = Kind.imm → ∀ b, ζ.wit.InStratum b → LifeBound ls ζ.wit b

theorem LifeBound.mono {ls : List SRec} {σ : WRes} {b b' : Life} (h : LifeBound ls σ b)
    (hb : b' ⊑ b) : LifeBound ls σ b' :=
  fun x hx hr => lt_of_le_of_lt hb (h x hx hr)

end BoCa.Fig16.LogRel.Typed

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
variable {wpX : WpOp}

/-- **The observable view transfers between two pieces of one escrow**: `A` observable at
`T`, `B` shaped at `T`, both cell-matching `R`, gives `B` observable at `T`.  At a `⊸`/`∀`
position both sides are `True` — the relaxation is exactly what makes this go through; at an
`Imm` or `Mut` position the cell is `R`'s, and its clause is read off the cell. -/
theorem obs_transfer {R : WRes} {ls : List SRec} (hLB : WitLB ls R) :
    ∀ (T : Ty) {δ : LSub} {v : Val} {A B : WRes}, CellMatch R A → CellMatch R B →
      vX wpX false T ls δ v A → vShape T δ v B → vX wpX false T ls δ v B
  | .unit, _, _, _, _, _, _, _, hB => hB
  | .unk, _, _, _, _, _, _, _, hB => hB
  | .lolli _ _, _, _, _, _, _, _, _, _ => trivial
  | .all _ _ _, _, _, _, _, _, _, _, _ => trivial
  | .tensor T₁ T₂, _, _, _, _, hA, hB', h, hs => by
      obtain ⟨v₁, v₂, hk⟩ := h
      obtain ⟨he, A₁, A₂, hcA, h₁, h₂⟩ := pure_sep_iff.mp hk
      obtain ⟨w₁, w₂, hk'⟩ := hs
      obtain ⟨he', B₁, B₂, hcB, g₁, g₂⟩ := pure_sep_iff.mp hk'
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' (he.symm.trans he')
      exact ⟨v₁, v₂, pure_sep_mk he ⟨B₁, B₂, hcB,
        obs_transfer hLB T₁ (hA.left hcA) (hB'.left hcB) h₁ g₁,
        obs_transfer hLB T₂ (hA.right hcA) (hB'.right hcB) h₂ g₂⟩⟩
  | .sum T₁ T₂, _, _, _, _, hA, hB', h, hs => by
      rcases h with ⟨a, hk₁⟩ | ⟨a, hk₁⟩ <;> rcases hs with ⟨b, hk₂⟩ | ⟨b, hk₂⟩
      · obtain ⟨he, h₁⟩ := pure_sep_iff.mp hk₁
        obtain ⟨he', h₁'⟩ := pure_sep_iff.mp hk₂
        cases Val.inj₁_inj' (he.symm.trans he')
        exact Or.inl ⟨a, pure_sep_mk he (obs_transfer hLB T₁ hA hB' h₁ h₁')⟩
      · obtain ⟨he, -⟩ := pure_sep_iff.mp hk₁
        obtain ⟨he', -⟩ := pure_sep_iff.mp hk₂
        exact (Val.inj₁_ne_inj₂ (he.symm.trans he')).elim
      · obtain ⟨he, -⟩ := pure_sep_iff.mp hk₁
        obtain ⟨he', -⟩ := pure_sep_iff.mp hk₂
        exact (Val.inj₁_ne_inj₂ (he'.symm.trans he)).elim
      · obtain ⟨he, h₂⟩ := pure_sep_iff.mp hk₁
        obtain ⟨he', h₂'⟩ := pure_sep_iff.mp hk₂
        cases Val.inj₂_inj' (he.symm.trans he')
        exact Or.inr ⟨a, pure_sep_mk he (obs_transfer hLB T₂ hA hB' h₂ h₂')⟩
  | .box a T, _, _, _, _, hA, hB', h, hs => by
      obtain ⟨α, hα, hb, -⟩ := h
      obtain ⟨α', hα', hb', ho'⟩ := hs
      exact ⟨α', hα', obs_transfer hLB T hA hB' hb hb', ho'⟩
  | .ref S, _, _, _, _, hA, hB', h, hs => by
      obtain ⟨ℓ, u, hk⟩ := h
      obtain ⟨hl, ρa, ρb, hab, hown, hRb⟩ := pure_sep_iff.mp hk
      obtain ⟨ℓ', u', hk'⟩ := hs
      obtain ⟨hl', σa, σb, hab', hown', hSb⟩ := pure_sep_iff.mp hk'
      have e₀ : ℓ' = ℓ := by
        have := congrArg Subtype.val (hl'.symm.trans hl); simpa using this
      subst e₀
      have hown₁ : ρa = ResU.single ℓ' (CellU.ownOf u) := hown
      have hown₂ : σa = ResU.single ℓ' (CellU.ownOf u') := hown'
      subst hown₁; subst hown₂
      have eA := compS_get_left_nonImm hab (ResU.single_get_self _ _) (by simp)
      have eB := compS_get_left_nonImm hab' (ResU.single_get_self _ _) (by simp)
      obtain ⟨ζ, eζ, -, -, -, hζ⟩ := hA ℓ' _ eA
      obtain ⟨ζ', eζ', -, -, -, hζ'⟩ := hB' ℓ' _ eB
      rw [eζ] at eζ'; cases Option.some.inj eζ'
      have huu : u = u' := by
        have := (hζ (by simp)).symm.trans (hζ' (by simp))
        have := congrArg CellU.erase this
        simpa using this
      subst huu
      exact ⟨ℓ', u, pure_sep_mk hl' ⟨_, σb, hab', rfl,
        obs_transfer hLB S (hA.right hab) (hB'.right hab') hRb hSb⟩⟩
  | .imm a S, δ, v, A, B, hA, hB', h, hs => by
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv, hcoh⟩, hpto⟩ := h
      subst hρ₀
      have e₁ := eq_of_compS_empty_left hc
      subst e₁
      obtain ⟨s, u, σ, hσ, hρ₁, hαs, hP⟩ := ptoImmO_read hpto
      subst hρ₁
      obtain ⟨α', hα', ℓ', σ₀, σ₁, hc', ⟨hσ₀, hv'⟩, t, u', σ', ht, hσ₁, -, hαt⟩ := hs
      subst hσ₀
      have e₂ := eq_of_compS_empty_left hc'
      subst e₂
      subst hσ₁
      have e₀ : ℓ' = ℓ := by
        have := congrArg Subtype.val (hv'.symm.trans hv); simpa using this
      subst e₀
      rw [hα] at hα'; cases Option.some.inj hα'
      obtain ⟨ζ, eζ, kζ, wζ, rζ, -⟩ := hA ℓ' _ (ResU.single_get_self _ _)
      obtain ⟨ζ', eζ', -, wζ', rζ', -⟩ := hB' ℓ' _ (ResU.single_get_self _ _)
      rw [eζ] at eζ'; cases Option.some.inj eζ'
      simp only [CellU.wit_immOf, CellU.erase_immOf] at wζ rζ wζ' rζ'
      have hσσ : σ' = σ := wζ'.symm.trans wζ
      have huu : u' = u := rζ'.symm.trans rζ
      subst hσσ; subst huu
      have hlb : LifeBound ls σ' t.meet := by
        have := hLB ℓ' ζ eζ (by rw [kζ]; simp) t.join (by rw [wζ]; exact ht)
        rw [wζ] at this
        exact this.mono t.meet_le_join
      exact ⟨α, hα, ℓ', PMap.empty, _, hc', ⟨rfl, hv', hcoh⟩, ptoImmO_make ht hαt hP hlb⟩
  | .mut a S, δ, v, A, B, hA, hB', h, hs => by
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv⟩, hmut⟩ := h
      subst hρ₀
      have e₁ := eq_of_compS_empty_left hc
      subst e₁
      obtain ⟨α', hα', ℓ', σ₀, σ₁, hc', ⟨hσ₀, hv'⟩, P, hpto, -⟩ := hs
      subst hσ₀
      have e₂ := eq_of_compS_empty_left hc'
      subst e₂
      have e₀ : ℓ' = ℓ := by
        have := congrArg Subtype.val (hv'.symm.trans hv); simpa using this
      subst e₀
      rw [hα] at hα'; cases Option.some.inj hα'
      obtain ⟨b, u, σ, hσ, Q, hw, ls₀, hab, hρ₁, hQ, hls₀, hunif⟩ := hmut
      obtain ⟨b', u', σ', hσ', Q', hw', -, hσ₁, -⟩ := hpto
      subst hρ₁; subst hσ₁
      obtain ⟨ζ, eζ, -, -, -, hζ⟩ := hA ℓ' _ (ResU.single_get_self _ _)
      obtain ⟨ζ', eζ', -, -, -, hζ'⟩ := hB' ℓ' _ (ResU.single_get_self _ _)
      rw [eζ] at eζ'; cases Option.some.inj eζ'
      have hcell := (hζ (by simp)).symm.trans (hζ' (by simp))
      refine ⟨α, hα, ℓ', PMap.empty, _, hc', ⟨rfl, hv'⟩, ?_⟩
      rw [← hcell]
      exact ⟨b, u, σ, hσ, Q, hw, ls₀, hab, rfl, hQ, hls₀, hunif⟩

end BoCa.Fig16.LogRel.Typed

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **A cell of `c ∈ reb_β(σ)` against `σ`'s cell**: same value; a `mut`/`imm` cell keeps
its witness; an `own` cell's witness is a piece of `σ` (`[TR]` p. 5's three clauses). -/
theorem reb_cell_match {β : Life} {σ c : WRes} (hr : ResU.Reb β σ c) {m : Loc}
    {ψ : CellU Loc Val} (e : c.get m = some ψ) :
    ∃ ζ, σ.get m = some ζ ∧ ψ.erase = ζ.erase ∧ (ζ.kind ≠ Kind.own → ψ.wit = ζ.wit) ∧
      (ζ.kind = Kind.own → CellMatch σ ψ.wit) := by
  obtain ⟨-, π, b, hdom, hbig, hle, hbody⟩ := hr
  obtain ⟨⟨l₀, q⟩, hpm, hpl⟩ := List.mem_map.mp ((hdom.2 m).mpr ⟨_, e⟩)
  simp only at hpl
  subst hpl
  have hq := hbody l₀ q hpm
  have hmem : q ∈ π.map Prod.snd := List.mem_map.mpr ⟨_, hpm, rfl⟩
  obtain ⟨b', hb', hle'⟩ := BigComp.leS_of_sublist (List.singleton_sublist.mpr hmem) hbig
  rw [(BigComp.singleton_iff ResU.compLawsS).mp hb'] at hle'
  have hqσ : ResU.Le q σ := hle'.trans hle
  obtain ⟨ζq, hζq⟩ := hq.1
  obtain ⟨τ, hτ⟩ := hqσ
  obtain ⟨ζ, hζ⟩ := comp_some hτ hζq
  rcases CellU.rep ζ with ⟨u, rfl⟩ | ⟨s, v, χ, hs, rfl⟩ | ⟨b₀, v, χ, hb₀, P, hw, rfl⟩
  · obtain ⟨hh, he⟩ := hq.2.1 u hζ
    rw [e] at he; cases Option.some.inj he
    refine ⟨_, hζ, by simp, fun h => (h (by simp)).elim, fun _ => ?_⟩
    rw [CellU.wit_immOf]
    exact (CellMatch.of_le ⟨τ, hτ⟩).del l₀
  · obtain ⟨⟨t, ht, -, he⟩, -⟩ := hq.2.2.2 s v χ hs hζ
    rw [e] at he; cases Option.some.inj he
    exact ⟨_, hζ, by simp, fun _ => by simp, fun h => absurd h (by simp)⟩
  · obtain ⟨⟨hh, he⟩, -⟩ := hq.2.2.1 b₀ v χ hb₀ P hw hζ
    rw [e] at he; cases Option.some.inj he
    exact ⟨_, hζ, by simp, fun _ => by simp, fun h => absurd h (by simp)⟩

/-- The `reb`-match hypothesis passes to a part. -/
theorem rebMatch_left {R c₁ c₂ c : WRes} (hcc : ResU.CompS c₁ c₂ c)
    (h : ∀ m ψ, c.get m = some ψ → ∃ ζ, R.get m = some ζ ∧ ψ.erase = ζ.erase ∧
      (ζ.kind ≠ Kind.own → ψ.wit = ζ.wit) ∧ (ζ.kind = Kind.own → CellMatch R ψ.wit)) :
    ∀ m ψ, c₁.get m = some ψ → ∃ ζ, R.get m = some ζ ∧ ψ.erase = ζ.erase ∧
      (ζ.kind ≠ Kind.own → ψ.wit = ζ.wit) ∧ (ζ.kind = Kind.own → CellMatch R ψ.wit) := by
  intro m ψ e
  obtain ⟨ψ', e', -, w', r'⟩ := compS_get_left' hcc e
  obtain ⟨ζ, eζ, h₁, h₂, h₃⟩ := h m ψ' e'
  exact ⟨ζ, eζ, r'.symm.trans h₁, fun k => w'.symm.trans (h₂ k),
    fun k => by rw [← w']; exact h₃ k⟩

theorem strat_left {R c₁ c₂ c : WRes} {β : Life} (hcc : ResU.CompS c₁ c₂ c)
    (hs : ∀ m ψ, c.get m = some ψ → (∃ ζ, R.get m = some ζ ∧ ζ.kind ≠ Kind.imm) →
      ψ.wit.InStratum (LSet.singleton β).join) :
    ∀ m ψ, c₁.get m = some ψ → (∃ ζ, R.get m = some ζ ∧ ζ.kind ≠ Kind.imm) →
      ψ.wit.InStratum (LSet.singleton β).join := by
  intro m ψ e hz
  obtain ⟨ψ', e', -, w', -⟩ := compS_get_left' hcc e
  rw [← w']; exact hs m ψ' e' hz

end BoCa.Fig16.LogRel.Typed

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
variable {wpX : WpOp}

/-- **6.131's image re-taken at `β`, at the program's relation**: `relRes` (`relabel_reb`)
typed at `𝒱X true⟦Imm̲ 'x T⟧`.  The inputs: the old image's shape (the
world's `JointAt`), the escrow's **observable** validity (the payload the program holds),
and coherence at the `Ref` and `Mut` positions.  At a `Ref`/`Mut` position the new cell's
payload is observable because the old image's witness is a piece of the escrow
(`obs_transfer`) or the `mut` cell's content (its stored predicate); at an `Imm` position
the kept cell is the escrow's (`obs_transfer` at the cell). -/
theorem relabel_obs {R : WRes} {ls : List SRec} {β β₀ : Life} {δ : LSub} {x x₀ : LifeVar}
    (hLB : WitLB ls R) (hβls : ∀ y ∈ ls, y.2 ⊐ β) :
    ∀ (T : Ty), ¬ LFree x T → ¬ LFree x₀ T → ∀ {v : Val} {c Rl : WRes},
      vShape (T.immReborrow (.var x₀)) (δ.extend x₀ β₀) v c →
      vX wpX false T ls δ v Rl → CellMatch R Rl →
      (∀ m ψ, c.get m = some ψ → ∃ ζ, R.get m = some ζ ∧ ψ.erase = ζ.erase ∧
          (ζ.kind ≠ Kind.own → ψ.wit = ζ.wit) ∧ (ζ.kind = Kind.own → CellMatch R ψ.wit)) →
      (∀ m ψ, c.get m = some ψ → (∃ ζ, R.get m = some ζ ∧ ζ.kind ≠ Kind.imm) →
        ψ.wit.InStratum (LSet.singleton β).join) →
      (∀ m S u, RefPos T v m S → R.get m = some (CellU.ownOf u) →
        Coh (rsOf ls) m S (δ.extend x β)) →
      (∀ m S, MutPos T v m S → Coh (rsOf ls) m S (δ.extend x β)) →
      vX wpX true (T.immReborrow (.var x)) ls (δ.extend x β) v (relRes R β c) := by
  intro T
  induction T with
  | unit =>
      intro _ _ v c Rl hc _ _ _ _ _ _
      obtain ⟨hce, hv⟩ := hc
      subst hce; rw [relRes_empty]; exact ⟨rfl, hv⟩
  | lolli _ _ _ _ =>
      intro _ _ v c Rl hc _ _ _ _ _ _
      obtain ⟨hce, -⟩ := hc
      subst hce; rw [relRes_empty]; exact ⟨rfl, trivial⟩
  | all _ _ _ _ =>
      intro _ _ v c Rl hc _ _ _ _ _ _
      obtain ⟨hce, -⟩ := hc
      subst hce; rw [relRes_empty]; exact ⟨rfl, trivial⟩
  | unk =>
      intro _ _ v c Rl hc _ _ _ _ _ _
      obtain ⟨hce, -⟩ := hc
      subst hce; rw [relRes_empty]; exact ⟨rfl, trivial⟩
  | sum T₁ T₂ ih₁ ih₂ =>
      intro hx hx₀ v c Rl hc hR hRl hcR hs hcr hcm
      rcases hc with ⟨a, hk₁⟩ | ⟨a, hk₁⟩ <;> rcases hR with ⟨b, hk₂⟩ | ⟨b, hk₂⟩
      · obtain ⟨he, h₁⟩ := pure_sep_iff.mp hk₁
        obtain ⟨he', h₁'⟩ := pure_sep_iff.mp hk₂
        subst he; cases Val.inj₁_inj' he'
        exact Or.inl ⟨a, pure_sep_mk rfl (ih₁ (fun h => hx (Or.inl h)) (fun h => hx₀ (Or.inl h))
          h₁ h₁' hRl hcR hs (fun m S u h => hcr m S u (RefPos.sumL h))
          (fun m S h => hcm m S (MutPos.sumL h)))⟩
      · obtain ⟨he, -⟩ := pure_sep_iff.mp hk₁
        obtain ⟨he', -⟩ := pure_sep_iff.mp hk₂
        subst he; exact (Val.inj₁_ne_inj₂ he').elim
      · obtain ⟨he, -⟩ := pure_sep_iff.mp hk₁
        obtain ⟨he', -⟩ := pure_sep_iff.mp hk₂
        subst he; exact (Val.inj₁_ne_inj₂ he'.symm).elim
      · obtain ⟨he, h₂⟩ := pure_sep_iff.mp hk₁
        obtain ⟨he', h₂'⟩ := pure_sep_iff.mp hk₂
        subst he; cases Val.inj₂_inj' he'
        exact Or.inr ⟨a, pure_sep_mk rfl (ih₂ (fun h => hx (Or.inr h)) (fun h => hx₀ (Or.inr h))
          h₂ h₂' hRl hcR hs (fun m S u h => hcr m S u (RefPos.sumR h))
          (fun m S h => hcm m S (MutPos.sumR h)))⟩
  | tensor T₁ T₂ ih₁ ih₂ =>
      intro hx hx₀ v c Rl hc hR hRl hcR hs hcr hcm
      obtain ⟨a, b, hk₁⟩ := hc
      obtain ⟨he, c₁, c₂, hcc, h₁, h₂⟩ := pure_sep_iff.mp hk₁
      obtain ⟨a', b', hk₂⟩ := hR
      obtain ⟨he', R₁, R₂, hRR, h₁', h₂'⟩ := pure_sep_iff.mp hk₂
      subst he
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' he'
      exact ⟨a, b, pure_sep_mk rfl ⟨_, _, relRes_compS hcc,
        ih₁ (fun h => hx (Or.inl h)) (fun h => hx₀ (Or.inl h)) h₁ h₁' (hRl.left hRR)
          (rebMatch_left hcc hcR) (strat_left hcc hs)
          (fun m S u h => hcr m S u (RefPos.tensorL h)) (fun m S h => hcm m S (MutPos.tensorL h)),
        ih₂ (fun h => hx (Or.inr h)) (fun h => hx₀ (Or.inr h)) h₂ h₂' (hRl.right hRR)
          (rebMatch_left hcc.comm hcR) (strat_left hcc.comm hs)
          (fun m S u h => hcr m S u (RefPos.tensorR h)) (fun m S h => hcm m S (MutPos.tensorR h))⟩⟩
  | box a T ih =>
      intro hx hx₀ v c Rl hc hR hRl hcR hs hcr hcm
      obtain ⟨α, -, hb, -⟩ := hR
      exact ih (fun h => hx (Or.inr h)) (fun h => hx₀ (Or.inr h)) hc hb hRl hcR hs
        (fun m S u h => hcr m S u (RefPos.box h)) (fun m S h => hcm m S (MutPos.box h))
  | ref S _ =>
      intro hx hx₀ v c Rl hc hR hRl hcR hs hcr _
      obtain ⟨α, -, l', hk₁⟩ := hc
      obtain ⟨hl, s', w, W, hW, rfl, hWd, -⟩ := pure_sep_iff.mp hk₁
      obtain ⟨l'', u, hk₂⟩ := hR
      obtain ⟨hl', ρa, ρb, hab, hown, hRb⟩ := pure_sep_iff.mp hk₂
      have e₀ : l' = l'' := by
        have := congrArg Subtype.val (hl.symm.trans hl'); simpa using this
      subst e₀
      subst hl
      rw [show ρa = ResU.single l' (CellU.ownOf u) from hown] at hab
      have eRl := compS_get_left_nonImm hab (ResU.single_get_self _ _) (by simp)
      obtain ⟨ζ, eζ, -, -, -, hζ⟩ := hRl l' _ eRl
      have hζ' : ζ = CellU.ownOf u := hζ (by simp)
      subst hζ'
      obtain ⟨ζ₂, eζ₂, her, -, hcw⟩ := hcR l' _ (ResU.single_get_self _ _)
      rw [eζ] at eζ₂; cases Option.some.inj eζ₂
      simp only [CellU.erase_immOf, CellU.erase_ownOf] at her
      subst her
      have hWm : CellMatch R W := by
        have := hcw (by simp); rwa [CellU.wit_immOf] at this
      have kne : (CellU.ownOf (Loc := Loc) w).kind ≠ Kind.imm := by simp
      have hβ := hs l' _ (ResU.single_get_self _ _) ⟨_, eζ, kne⟩
      rw [CellU.wit_immOf] at hβ
      rw [relRes_single, relCell_fire eζ kne hβ]
      rw [vShape_extend_of_not_free (T := S) hx₀] at hWd
      have hobs : vX wpX false S ls δ w W := obs_transfer hLB S (hRl.right hab) hWm hRb hWd
      have hobs' : vX wpX false S ls (δ.extend x β) w W := by
        rw [vX_extend_of_not_free (T := S) hx]; exact hobs
      exact ⟨β, interp_ext_self δ x β, l', pure_sep_mk ⟨rfl, cohE_of_coh (hcr l' S w (RefPos.ref S l') eζ)⟩
        (ptoImmO_make hβ le_rfl hobs' (fun y hy _ => hβls y hy))⟩
  | imm a S _ =>
      intro hx hx₀ v c Rl hc hR hRl hcR _ _ _
      have hc' : vShape (.imm a S) (δ.extend x₀ β₀) v c := hc
      have hc'' := hc'
      obtain ⟨α, -, l', hk₁⟩ := hc''
      obtain ⟨hl, s', w, W, hW, rfl, -, -⟩ := pure_sep_iff.mp hk₁
      have hR' := hR
      obtain ⟨α', -, l'', ρ₀, ρ₁, hc₀, ⟨hρ₀, hv, -⟩, s₁, u₁, σ₁, hs₁, ls₁, hρ₁, -⟩ := hR'
      subst hρ₀
      have e₁ := eq_of_compS_empty_left hc₀
      subst e₁; subst hρ₁
      have e₀ : l'' = l' := by
        have := congrArg Subtype.val (hv.symm.trans hl); simpa using this
      subst e₀
      obtain ⟨ζ, eζ, kζ, -, -, -⟩ := hRl l'' _ (ResU.single_get_self _ _)
      have kζ' : ζ.kind = Kind.imm := by rw [kζ]; simp
      rw [relRes_single, relCell_keep eζ kζ']
      show vX wpX true (.imm a S) ls (δ.extend x β) v _
      rw [vX_extend_of_not_free hx, vX_imm_mode a S true false]
      rw [vShape_extend_of_not_free hx₀] at hc'
      refine obs_transfer hLB (.imm a S) hRl ?_ hR hc'
      intro m ψ e
      obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some e
      obtain ⟨ζ₂, eζ₂, her, hwit, -⟩ := hcR m _ (ResU.single_get_self _ _)
      rw [eζ] at eζ₂; cases Option.some.inj eζ₂
      exact ⟨ζ, eζ, by rw [kζ']; simp, (hwit (by rw [kζ']; simp)).symm, her.symm,
        fun hk => absurd (by simp) hk⟩
  | «mut» a S _ =>
      intro hx hx₀ v c Rl hc hR hRl hcR hs _ hcm
      obtain ⟨α, -, l', hk₁⟩ := hc
      obtain ⟨hl, s', w, W, hW, rfl, -, -⟩ := pure_sep_iff.mp hk₁
      obtain ⟨α', -, l'', ρ₀, ρ₁, hc₀, ⟨hρ₀, hv⟩, hmut⟩ := hR
      subst hρ₀
      have e₁ := eq_of_compS_empty_left hc₀
      subst e₁
      obtain ⟨b, u, σ, hσ, Q, hw, hρ₁, hvS⟩ := ptoMutX_read hmut
      subst hρ₁
      have e₀ : l'' = l' := by
        have := congrArg Subtype.val (hv.symm.trans hl); simpa using this
      subst e₀
      subst hl
      obtain ⟨ζ, eζ, -, -, -, hζ⟩ := hRl l'' _ (ResU.single_get_self _ _)
      have hζ' := hζ (by simp)
      subst hζ'
      obtain ⟨ζ₂, eζ₂, her, hwit, -⟩ := hcR l'' _ (ResU.single_get_self _ _)
      rw [eζ] at eζ₂; cases Option.some.inj eζ₂
      have hw' := hwit (by simp)
      simp only [CellU.erase_immOf, CellU.erase_mutOf, CellU.wit_immOf,
        CellU.wit_mutOf] at her hw'
      subst her; subst hw'
      have kne : (CellU.mutOf b w W hσ Q hw).kind ≠ Kind.imm := by simp
      have hβ := hs l'' _ (ResU.single_get_self _ _) ⟨_, eζ, kne⟩
      rw [CellU.wit_immOf] at hβ
      rw [relRes_single, relCell_fire eζ kne hβ]
      have hS : ¬ LFree x S := fun h => hx (Or.inr h)
      have hobs' : vX wpX false S ls (δ.extend x β) w W := by
        rw [vX_extend_of_not_free hS]; exact vO_obs S hvS
      exact ⟨β, interp_ext_self δ x β, l'', pure_sep_mk ⟨rfl, cohE_of_coh (hcm l'' S (MutPos.mut a S l''))⟩
        (ptoImmO_make hβ le_rfl hobs' (fun y hy _ => hβls y hy))⟩

end BoCa.Fig16.LogRel.Typed

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **Re-taking an image at its own lifetime changes nothing**: `relRes R β c = c` for
`c ∈ reb_β(R)`. -/
theorem relRes_self {β : Life} {R c : WRes} (hr : ResU.Reb β R c) : relRes R β c = c := by
  refine PMap.ext fun m => ?_
  rw [relRes_get]
  cases e : c.get m with
  | none => rfl
  | some ψ =>
    simp only [Option.map_some]
    congr 1
    unfold relCell
    split
    · rename_i h
      obtain ⟨hk, ⟨ζ, eζ, kζ⟩, hβ⟩ := h
      obtain ⟨-, π, b, hdom, hbig, hle, hbody⟩ := hr
      obtain ⟨⟨l₀, q⟩, hpm, hpl⟩ := List.mem_map.mp ((hdom.2 m).mpr ⟨_, e⟩)
      simp only at hpl
      subst hpl
      have hq := hbody l₀ q hpm
      rcases CellU.rep ζ with ⟨u, rfl⟩ | ⟨s, v, χ, hs, rfl⟩ | ⟨b₀, v, χ, hb₀, P, hw, rfl⟩
      · obtain ⟨hh, he⟩ := hq.2.1 u eζ
        rw [e] at he; cases Option.some.inj he
        exact CellU.immOf_congr rfl (by simp) (by simp) _ _
      · exact absurd (CellU.kind_immOf _ _ _ _) kζ
      · obtain ⟨⟨hh, he⟩, -⟩ := hq.2.2.1 b₀ v χ hb₀ P hw eζ
        rw [e] at he; cases Option.some.inj he
        exact CellU.immOf_congr rfl (by simp) (by simp) _ _
    · rfl

end BoCa.Fig16.LogRel.Typed

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
variable {wpX : WpOp}

/-!
### Lemma 6.131 (↺V₁) — typed-world version

The printed statement, the printed proof and the adjudication are in `Paper/S6_6_ReborrowingEntailments/Lemmas.lean`, under the record of Lemma 6.131 (↺V₁).
-/
/-- **6.131's conclusion at the program's relation, from a shaped image**: an image
`c ∈ reb_β(R)` shaped at `Imm̲ 'x T`, over an escrow observable at `T`, is `𝒱X true`-typed at
`Imm̲ 'x T` — `relabel_obs` at `β₀ = β`, with `relRes_self`.  So `[TR]` 6.131 at `𝒱X` is
6.131 at the shape relation plus coherence at the roots and `Mut` positions. -/
theorem image_vX_of_shape {R c : WRes} {ls : List SRec} {β : Life} {δ : LSub} {x : LifeVar}
    (hLB : WitLB ls R) (hβls : ∀ y ∈ ls, y.2 ⊐ β) (T : Ty) (hx : ¬ LFree x T) {v : Val}
    (hr : ResU.Reb β R c) (hc : vShape (T.immReborrow (.var x)) (δ.extend x β) v c)
    (hR : vX wpX false T ls δ v R)
    (hcr : ∀ m S u, RefPos T v m S → R.get m = some (CellU.ownOf u) →
      Coh (rsOf ls) m S (δ.extend x β))
    (hcm : ∀ m S, MutPos T v m S → Coh (rsOf ls) m S (δ.extend x β)) :
    vX wpX true (T.immReborrow (.var x)) ls (δ.extend x β) v c := by
  have := relabel_obs (wpX := wpX) hLB hβls T hx hx hc hR
    (CellMatch.of_le ⟨_, ResU.comp_empty_right _⟩) (fun m ψ e => reb_cell_match hr e)
    (reb_wit_stratum hr.1 hr) hcr hcm
  rwa [relRes_self hr] at this

end BoCa.Fig16.LogRel.Typed

end
