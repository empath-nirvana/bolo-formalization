import Purity.Frozen
import Purity.Read
import Paper.S6_8_FundamentalProperty.Lemmas
import Paper.CONF.Results
import Support.TypedWorld.Relation

/-!
# Purity — the pure fragment

**The fragment, by types.**  A program `Δ; Γ ⊢ e : T` (`DerivesWf`) is in the pure fragment
(`PureTyping`) when its interface holds no exclusive resource:

* every live slot of `Γ` has a type built from `1`, `⊕`, `⊗` and `Imm @a S` (`PureArgTy`),
  with `S` any type — a value there is plain data and immutable borrows;
* the result type `T` is built from `1`, `⊕` and `⊗` (`PlainTy`) — plain data, no resource.

At such a type the relation's resources are simple.  A value at `PlainTy T` holds the empty
resource and mentions no location (`vP_plain`); a value at `PureArgTy T` holds a resource of
`imm` cells only (`vP_pureArg`), and so does a context of them (`gDenX_pure`).

**What is proved**, for `γ` closing values in the relation at `ρ` and a tagged typed world
`ρf ● ρ` with heap `μ`:

1. *The heap is given back* (`pure_heap`).  The run the Fundamental Property exhibits ends at
   exactly `μ`, and every fresh run ends at `μ` up to an injective renaming of the locations
   (`fresh_run_image`).  Temporaries are freed; nothing reachable changes (`heap_restored`,
   `Frozen.lean`).
2. *The result is a function of the arguments and what they reach* (`pure_result`).  Every
   fresh run from `μ` and every run from any heap `μ₂` that agrees with `μ` on the locations
   reachable from `γ` return the same value, which is plain data.  The two heaps may differ
   anywhere else.
3. *Closed programs are pure outright* (`closed_pure`).  With no arguments, every fresh run from
   every heap whatsoever returns the value of the run adequacy exhibits from the empty memory.

`[about ours]`: an extension, not a transcription.
-/

noncomputable section

namespace BoCa.Purity
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps)
open BoCa.Fig16.LogRel.Typed
open BoCa.Lifetime (LifeCtx LSub)

/-! ### The fragment -/

/-- Plain data: `1`, `⊕` and `⊗` of plain data. -/
inductive PlainTy : Ty → Prop where
  | unit : PlainTy .unit
  | sum {T₁ T₂ : Ty} : PlainTy T₁ → PlainTy T₂ → PlainTy (.sum T₁ T₂)
  | tensor {T₁ T₂ : Ty} : PlainTy T₁ → PlainTy T₂ → PlainTy (.tensor T₁ T₂)

/-- An argument type of the pure fragment: `1`, `⊕`, `⊗` and immutable borrows `Imm @a S`. -/
inductive PureArgTy : Ty → Prop where
  | unit : PureArgTy .unit
  | sum {T₁ T₂ : Ty} : PureArgTy T₁ → PureArgTy T₂ → PureArgTy (.sum T₁ T₂)
  | tensor {T₁ T₂ : Ty} : PureArgTy T₁ → PureArgTy T₂ → PureArgTy (.tensor T₁ T₂)
  | imm (a : Lifetime.Life) (S : Ty) : PureArgTy (.imm a S)

theorem PlainTy.pureArg {T : Ty} (h : PlainTy T) : PureArgTy T := by
  induction h with
  | unit => exact .unit
  | sum _ _ ih₁ ih₂ => exact .sum ih₁ ih₂
  | tensor _ _ ih₁ ih₂ => exact .tensor ih₁ ih₂

/-- Every live slot of `Γ` has an argument type of the pure fragment. -/
def PureCtx (Γ : Ctx Ty) : Prop := ∀ s ∈ Γ, s.live = true → PureArgTy s.ty

/-- **The pure fragment**: a `DerivesWf` derivation with an interface of plain data and
immutable borrows, and a plain-data result; with the Fundamental Property's hypotheses
`⊧ Δ` (as `Δ.Ok`) and `Δ ⊢ Γ`. -/
structure PureTyping (Δ : LifeCtx) (Γ : Ctx Ty) (e : Expr) (T : Ty) : Prop where
  derives : DerivesWf Δ Γ e T
  ok : Δ.Ok
  wfCtx : Ctx.ScopedB Δ Γ
  args : PureCtx Γ
  result : PlainTy T

/-! ### The relation at the fragment's types -/

theorem immTop_empty : ImmTop (PMap.empty : WRes) := fun l ψ h => by
  rw [PMap.empty_get] at h; cases h

theorem immTop_compS {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) (h₁ : ImmTop ρ₁)
    (h₂ : ImmTop ρ₂) : ImmTop ρ := by
  intro l ψ hψ
  rcases ResU.Comp.get hc l with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
      ⟨χ₁, χ₂, χ, -, -, f, hC⟩
  · rw [f] at hψ; cases hψ
  · rw [f] at hψ; cases hψ; exact h₁ l _ f₁
  · rw [f] at hψ; cases hψ; exact h₂ l _ f₂
  · rw [f] at hψ; cases hψ; exact CellU.CompS.kind hC

theorem immTop_single_imm (l : Loc) {s : LSet} {u : Val} {σ : WRes} (h : σ.InStratum s.join) :
    ImmTop (ResU.single l (CellU.immOf s u σ h)) := by
  intro l' ψ hψ
  by_cases e : l' = l
  · subst e; rw [ResU.single_get_self] at hψ; cases hψ; rfl
  · rw [ResU.single_get_ne _ e] at hψ; cases hψ

/-- `ρ₁ ● ρ₂` with both empty is empty. -/
theorem compS_empty_empty {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) (h₁ : ρ₁ = PMap.empty)
    (h₂ : ρ₂ = PMap.empty) : ρ = PMap.empty := by
  subst h₁; subst h₂
  exact (ResU.eq_of_comp_empty_left hc).symm

/-- **A plain-data value holds no resource and mentions no location.** -/
theorem vP_plain {RR : RunRel} {T : Ty} (hT : PlainTy T) :
    ∀ {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}, vPR RR T ls δ v ρ →
      ρ = PMap.empty ∧ LocFree v.1 := by
  induction hT with
  | unit =>
      intro ls δ v ρ h
      obtain ⟨hρ, rfl⟩ := h
      exact ⟨hρ, fun ℓ o => by simp [Expr.Occ, Val.unit] at o⟩
  | tensor _ _ ih₁ ih₂ =>
      intro ls δ v ρ h
      obtain ⟨v₁, v₂, ρa, ρb, hc, ⟨hρa, rfl⟩, ρ₁, ρ₂, hc₂, h₁, h₂⟩ := h
      obtain ⟨e₁, f₁⟩ := ih₁ h₁
      obtain ⟨e₂, f₂⟩ := ih₂ h₂
      refine ⟨compS_empty_empty hc hρa (compS_empty_empty hc₂ e₁ e₂), fun ℓ o => ?_⟩
      rcases o with o | o
      · exact f₁ ℓ o
      · exact f₂ ℓ o
  | sum _ _ ih₁ ih₂ =>
      intro ls δ v ρ h
      rcases h with ⟨v₁, ρa, ρb, hc, ⟨hρa, rfl⟩, h₁⟩ | ⟨v₂, ρa, ρb, hc, ⟨hρa, rfl⟩, h₂⟩
      · obtain ⟨e₁, f₁⟩ := ih₁ h₁
        exact ⟨compS_empty_empty hc hρa e₁, fun ℓ o => f₁ ℓ o⟩
      · obtain ⟨e₂, f₂⟩ := ih₂ h₂
        exact ⟨compS_empty_empty hc hρa e₂, fun ℓ o => f₂ ℓ o⟩

/-- **A value at an argument type of the fragment holds only `imm` cells.** -/
theorem vP_pureArg {RR : RunRel} {T : Ty} (hT : PureArgTy T) :
    ∀ {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}, vPR RR T ls δ v ρ → ImmTop ρ := by
  induction hT with
  | unit =>
      intro ls δ v ρ h
      obtain ⟨rfl, -⟩ := h
      exact immTop_empty
  | tensor _ _ ih₁ ih₂ =>
      intro ls δ v ρ h
      obtain ⟨v₁, v₂, ρa, ρb, hc, ⟨rfl, -⟩, ρ₁, ρ₂, hc₂, h₁, h₂⟩ := h
      exact immTop_compS hc immTop_empty (immTop_compS hc₂ (ih₁ h₁) (ih₂ h₂))
  | sum _ _ ih₁ ih₂ =>
      intro ls δ v ρ h
      rcases h with ⟨v₁, ρa, ρb, hc, ⟨rfl, -⟩, h₁⟩ | ⟨v₂, ρa, ρb, hc, ⟨rfl, -⟩, h₂⟩
      · exact immTop_compS hc immTop_empty (ih₁ h₁)
      · exact immTop_compS hc immTop_empty (ih₂ h₂)
  | imm a S =>
      intro ls δ v ρ h
      obtain ⟨α, -, ℓ, ρa, ρb, hc, ⟨rfl, -⟩, s, u, σ, hσ, ls₀, rfl, -⟩ := h
      exact immTop_compS hc immTop_empty (immTop_single_imm ℓ hσ)

theorem gSepX_pure {RR : RunRel} {ls : List SRec} {δ : LSub} :
    ∀ {Γ : Ctx Ty} {γ : List Val} {ρ : WRes}, PureCtx Γ → gSepXR RR ls δ Γ γ ρ → ImmTop ρ
  | [], _, ρ, _, h => by obtain ⟨rfl, -⟩ := h; exact immTop_empty
  | _ :: _, [], ρ, _, h => by obtain ⟨rfl, -⟩ := h; exact immTop_empty
  | s :: Γ, v :: γ, ρ, hΓ, h => by
      have hΓ' : PureCtx Γ := fun s' hs' => hΓ s' (List.mem_cons_of_mem _ hs')
      simp only [gSepXR] at h
      split at h
      · rename_i hl
        obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := h
        exact immTop_compS hc (vP_pureArg (hΓ s (List.mem_cons_self ..) hl) h₁)
          (gSepX_pure hΓ' h₂)
      · exact gSepX_pure hΓ' h

/-- **A context of the fragment holds only `imm` cells.** -/
theorem gDenX_pure {RR : RunRel} {ls : List SRec} {δ : LSub} {Γ : Ctx Ty} {γ : List Val}
    {ρ : WRes} (hΓ : PureCtx Γ) (h : gDenXR RR ls δ Γ γ ρ) : ImmTop ρ := by
  obtain ⟨ρ₁, ρ₂, hc, ⟨rfl, -⟩, h₂⟩ := h
  exact immTop_compS hc immTop_empty (gSepX_pure hΓ h₂)

/-! ### Level 1: pure relative to the borrowed data -/

/-- The run the Fundamental Property exhibits for a program of the fragment. -/
theorem pure_exhibited {RR : RunRel} {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T : Ty} (hP : PureTyping Δ Γ e T)
    {δ : LSub} {γ : List Val} {ls : List SRec} {ρ : WRes} (hδ : Δ.Models δ)
    (hγ : gDenXR RR ls δ Γ γ ρ) {ρf fρ : WRes} {ps : List FrameRec} (hf : ResU.Hash ρf ρ)
    (hc : ResU.CompS ρf ρ fρ) (hT : TW fρ ps (rsOf ls)) (htg : Tagged fρ ps ls) {μ : Heap}
    (hμ : ResU.Lower fρ μ) :
    ∃ v : Val, RR.R μ (LogRel.substAll γ e) μ (.val v) ∧ LocFree v.1 ∧
      ∃ ls', vPR RR T ls' δ v PMap.empty := by
  have hw := fundamentalR RR Δ Γ e T hP.derives hP.ok hP.wfCtx δ γ ls ρ hδ hγ
  obtain ⟨ρ', ρp, π, fπ, μ', v, ls', hrun, hQ, h9, hA, hno, hfπ, hμ'⟩ :=
    wpTS_exhibited hw hf hc hT htg hμ
  obtain ⟨rfl, hlf⟩ := vP_plain hP.result hQ
  obtain rfl : ρp = π := ResU.eq_of_comp_empty_left h9
  obtain rfl := heap_restored hc hμ hfπ hμ' hA (gDenX_pure hP.args hγ) hno
  exact ⟨v, hrun, hlf, ls', hQ⟩

/-- **The heap is given back.**  From a tagged typed world completing the arguments' resource,
the exhibited run of a program of the fragment ends at exactly the heap it started from, with
a plain-data value.  Every fresh run returns the same value, and ends at that heap up to an
injective renaming of its locations. -/
theorem pure_heap {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T : Ty} (hP : PureTyping Δ Γ e T)
    {δ : LSub} {γ : List Val} {ls : List SRec} {ρ : WRes} (hδ : Δ.Models δ)
    (hγ : gDenX ls δ Γ γ ρ) {ρf fρ : WRes} {ps : List FrameRec} (hf : ResU.Hash ρf ρ)
    (hc : ResU.CompS ρf ρ fρ) (hT : TW fρ ps (rsOf ls)) (htg : Tagged fρ ps ls) {μ : Heap}
    (hμ : ResU.Lower fρ μ) :
    ∃ v : Val, Steps μ (LogRel.substAll γ e) μ (.val v) ∧ LocFree v.1 ∧
      (∃ ls', vP T ls' δ v PMap.empty) ∧
      ∀ (μR : Heap) (w : Val), FreshRun μ (LogRel.substAll γ e) μR w.1 →
        w = v ∧ ∃ g : Loc → Loc, Set.InjOn g {x | μR x ≠ none} ∧ μ = Heap.push g μR := by
  obtain ⟨v, hrun, hlf, hQ⟩ := pure_exhibited hP hδ hγ hf hc hT htg hμ
  refine ⟨v, hrun, hlf, hQ, fun μR w hR => ?_⟩
  obtain ⟨g, hinj, hpush, hv⟩ := fresh_run_image hR hrun
  have hw : LocFree w.1 := locFree_of_rename (e := w.1) (g := g) (by rw [← Val.rename_val, ← hv]; exact hlf)
  exact ⟨by rw [hv, Val.rename_locFree hw], g, hinj, hpush⟩

/-- **The result is a function of the arguments and what they reach.**  Let `μ` be the heap of a
tagged typed world completing the arguments' resource.  Every fresh run of `γ(e)` from `μ`, and
every run of `γ(e)` from any heap `μ₂` that agrees with `μ` on the allocated locations
reachable from `γ`, return the value of the exhibited run.  `μ₂` is otherwise arbitrary. -/
theorem pure_result {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T : Ty} (hP : PureTyping Δ Γ e T)
    {δ : LSub} {γ : List Val} {ls : List SRec} {ρ : WRes} (hδ : Δ.Models δ)
    (hγ : gDenX ls δ Γ γ ρ) {ρf fρ : WRes} {ps : List FrameRec} (hf : ResU.Hash ρf ρ)
    (hc : ResU.CompS ρf ρ fρ) (hT : TW fρ ps (rsOf ls)) (htg : Tagged fρ ps ls) {μ : Heap}
    (hμ : ResU.Lower fρ μ) :
    ∃ v : Val, LocFree v.1 ∧ (∃ ls', vP T ls' δ v PMap.empty) ∧
      Steps μ (LogRel.substAll γ e) μ (.val v) ∧
      ∀ (μ₁ μ₂ μ₂' : Heap) (w₁ w₂ : Val),
        FreshRun μ (LogRel.substAll γ e) μ₁ w₁.1 →
        (∀ x, Reach μ (ArgLocs γ) x → μ x ≠ none → μ₂ x = μ x) →
        Steps μ₂ (LogRel.substAll γ e) μ₂' w₂.1 → w₁ = v ∧ w₂ = v := by
  obtain ⟨v, hrun, hlf, hQ, hfresh⟩ := pure_heap hP hδ hγ hf hc hT htg hμ
  refine ⟨v, hlf, hQ, hrun, fun μ₁ μ₂ μ₂' w₁ w₂ h₁ hag h₂ => ?_⟩
  obtain ⟨rfl, -⟩ := hfresh μ₁ w₁ h₁
  have hag' : ∀ x, Reach μ (fun ℓ => (LogRel.substAll γ e).Occ ℓ) x → μ x ≠ none →
      μ₂ x = μ x := fun x hx =>
    hag x (Reach.mono (fun _ o => occ_substAll_of_locFree (derivesWf_locFree hP.derives) o) hx)
  exact ⟨rfl, fresh_run_local_eq hag' h₁ h₂ hlf⟩

/-! ### Level 2: closed programs are pure outright -/

/-- **A closed program of plain-data type is pure.**  `e` typed at `∅; ∅ ⊢ e : T` with `T` plain
data.  Adequacy's run from the empty memory returns a plain-data value `v`, freeing everything
it allocates; every fresh run from every heap whatsoever returns `v`; and from the heap of every
tagged typed world there is a run that ends at the heap it started from, with a plain-data
value. -/
theorem closed_pure {e : Expr} {T : Ty} (hD : DerivesWf LifeCtx.empty [] e T) (hT : PlainTy T) :
    ∃ v : Val, LocFree v.1 ∧ Steps Adequacy.emptyMem e Adequacy.emptyMem (.val v) ∧
      (∀ (μ μ' : Heap) (w : Val), FreshRun μ e μ' w.1 → w = v) ∧
      ∀ (ρf fρ : WRes) (ps : List FrameRec) (ls : List SRec) (μ : Heap),
        ResU.Hash ρf PMap.empty → ResU.CompS ρf PMap.empty fρ → TW fρ ps (rsOf ls) →
        Tagged fρ ps ls → ResU.Lower fρ μ → ∃ v' : Val, LocFree v'.1 ∧ Steps μ e μ (.val v') := by
  have hP : PureTyping LifeCtx.empty [] e T :=
    ⟨hD, ok_empty, fun s hs => absurd hs (by simp), fun s hs => absurd hs (by simp), hT⟩
  have hsub : LogRel.substAll [] e = e := by rw [LogRel.substAll, Adequacy.psub_nil]
  have hworld := fun (ρf fρ : WRes) (ps : List FrameRec) (ls : List SRec) (μ : Heap)
      (hf : ResU.Hash ρf PMap.empty) (hc : ResU.CompS ρf PMap.empty fρ)
      (hTW : TW fρ ps (rsOf ls)) (htg : Tagged fρ ps ls) (hμ : ResU.Lower fρ μ) =>
    pure_exhibited (RR := stepsRel) hP Adequacy.models_empty (gDenX_nil ls LSub.empty) hf hc hTW htg hμ
  -- the empty world
  have htg0 : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  obtain ⟨v, hrun, hlf, -⟩ := hworld PMap.empty PMap.empty [] [] Adequacy.emptyMem
    Fig16.LogRel.hash_empty (ResU.comp_empty_right _) TW.empty htg0 Fig16.BoLo.lower_empty
  rw [hsub] at hrun
  refine ⟨v, hlf, hrun, fun μ μ' w hR => ?_, fun ρf fρ ps ls μ hf hc hTW htg hμ => ?_⟩
  · -- nothing is reachable from `e`'s locations: there are none
    have hag : ∀ x, Reach μ (fun ℓ => e.Occ ℓ) x → μ x ≠ none → Adequacy.emptyMem x = μ x := by
      intro x hx
      exact absurd (reach_sub (S := fun _ => False)
        ⟨fun ℓ o => derivesWf_locFree hD ℓ o, fun _ _ h => h.elim⟩ hx) id
    obtain ⟨g, hg⟩ := fresh_run_local hag hR hrun
    have hw : LocFree w.1 := locFree_of_rename (e := w.1) (g := g)
      (by rw [← Val.rename_val, ← hg]; exact hlf)
    rw [hg, Val.rename_locFree hw]
  · obtain ⟨v', hrun', hlf', -⟩ := hworld ρf fρ ps ls μ hf hc hTW htg hμ
    rw [hsub] at hrun'
    exact ⟨v', hlf', hrun'⟩

end BoCa.Purity

end
