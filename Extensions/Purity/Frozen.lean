import Purity.Footprint
import Support.Model.Ancestors
import Support.Model.RelaxedWalks
import Support.Model.Surgery
import Support.Model.Update
import Support.Model.Walks
import Support.Model.WalkSplitting

/-!
# Purity — deep immutability, and a resource of `imm` cells is given back whole

`[CONF]` §5 describes the model's `imm` cells as enforcing *deep* immutability of the data an
immutable borrow points to.  At the level of the machine this reads: if `⦇ρ⦈` carries
`imm(ᾱ, u, χ)` at `m`, every location of `⦇χ⦈_○` (`FlatR χ p`) keeps its value on the run a
`wpTS` exhibits (`frozen_keeps`, `wpTS_frozen`).  The step is `[TR]` 6.48's "by the update
hypothesis, we also have `ag(ρ₃)(ℓ′) = ag(ρ₂)(ℓ′)`", carried by
`ResU.flat_imm_wit_factor`: `↭` keeps the `imm` cell with its witness, and the witness's
flattening is a factor of both worlds' aliasable walks.  `Footprint`'s second clause is the
cell itself; this is everything beneath it.

A resource whose top-level cells are all `imm` (`ImmTop`) holds every location of its
flattening either at one of those cells or beneath one (`flat_immTop_cov`).  If such a `ρ` is
updated to a `π` that owns no cell, `π` has no `mut` cell either and `⦇π⦈`'s domain lies in
`⦇ρ⦈`'s (`upd_immTop_dom`).  So a run from `⟦ρf ● ρ⟧` to `⟦ρf ● π⟧` ends at exactly the heap it
started from (`heap_restored`): nothing is changed, and nothing is left allocated.

`[about ours]`: an extension, not a transcription.
-/

noncomputable section

namespace BoCa.Purity
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps)
open BoCa.Fig16.LogRel.Typed

/-! ### Frozen locations -/

/-- Every top-level cell of `ρ` is an `imm` cell. -/
def ImmTop (ρ : WRes) : Prop := ∀ l ψ, ρ.get l = some ψ → ψ.kind = Kind.imm

/-- `⦇χ⦈_○ = p`: `ex(χ)_○ ○ ag(χ)`, the walk `ag` takes beneath an `imm` cell with witness `χ`
(`[TR]` p. 5, operation row 12). -/
def FlatR (χ p : WRes) : Prop := ∃ ev av, ExR χ ev ∧ AgW χ av ∧ ResU.CompR ev av p

theorem FlatR.functional {χ p p' : WRes} (h : FlatR χ p) (h' : FlatR χ p') : p = p' := by
  obtain ⟨e, a, he, ha, hc⟩ := h
  obtain ⟨e', a', he', ha', hc'⟩ := h'
  cases ExR.functional he he'
  cases AgW.functional ha ha'
  exact ResU.CompR.functional hc hc'

/-- `ℓ` lies beneath an `imm` cell of `⦇ρ⦈`: in `⦇χ⦈_○` for a cell `imm(ᾱ, u, χ)` of `⦇ρ⦈`. -/
def Frozen (ρ : WRes) (ℓ : Loc) : Prop :=
  ∃ (m : Loc) (s : LSet) (u : Val) (χ : WRes) (h : χ.InStratum s.join) (p : WRes),
    ρ.FlatAt m (CellU.immOf s u χ h) ∧ FlatR χ p ∧ p.get ℓ ≠ none

/-- A cell beneath an `imm` cell of `⦇ρ⦈` is a cell of `⦇ρ⦈`, with the same value. -/
theorem flat_of_frozen_cell {ρ σ : WRes} (hσ : ResU.Flat ρ σ) {m : Loc} {s : LSet} {u : Val}
    {χ : WRes} {h : χ.InStratum s.join} {p : WRes} (hm : ρ.FlatAt m (CellU.immOf s u χ h))
    (hp : FlatR χ p) {ℓ : Loc} {ψ : CellU Loc Val} (hℓ : p.get ℓ = some ψ) :
    ∃ χ', σ.get ℓ = some χ' ∧ χ'.erase = ψ.erase := by
  obtain ⟨e, a, he, ha, hc⟩ := hσ
  have hg : σ.get m = some (CellU.immOf s u χ h) :=
    (ResU.flatAt_iff ⟨e, a, he, ha, hc⟩ m _).mp hm
  obtain ⟨ev, av, p', z, hev, hav, hcc, hz⟩ := ResU.flat_imm_wit_factor he ha hc hg
  obtain rfl := FlatR.functional hp ⟨ev, av, hev, hav, hcc⟩
  obtain ⟨χa, ea, xa⟩ := comp_get_left_erase compR_erase hz hℓ
  obtain ⟨χσ, eσ, xσ⟩ := comp_get_right_erase compS_erase hc ea
  exact ⟨χσ, eσ, xσ.trans xa⟩

/-- **Deep immutability.**  If the initial heap lowers `ρf ● ρ`, the final heap lowers
`ρf ● π` and `ρ ↭ π`, every location beneath an `imm` cell of `⦇ρ⦈` is allocated and keeps its
value. -/
theorem frozen_keeps {ρf ρ π fρ fπ : WRes} {μ μ' : Heap} (hc : ResU.CompS ρf ρ fρ)
    (hμ : ResU.Lower fρ μ) (hfπ : ResU.CompS ρf π fπ) (hμ' : ResU.Lower fπ μ')
    (hA : ResU.UpdV ρ π) {ℓ : Loc} (hℓ : Frozen ρ ℓ) : μ' ℓ = μ ℓ ∧ μ ℓ ≠ none := by
  obtain ⟨m, s, u, χ, h, p, hm, hp, hpℓ⟩ := hℓ
  obtain ⟨ψ, eψ⟩ := Option.ne_none_iff_exists'.mp hpℓ
  obtain ⟨σρ, hσρ⟩ := hA.2.1
  obtain ⟨σπ, hσπ⟩ := hA.2.2
  obtain ⟨χ₁, e₁, x₁⟩ := flat_of_frozen_cell hσρ hm hp eψ
  obtain ⟨χ₂, e₂, x₂⟩ := flat_of_frozen_cell hσπ ((hA.1.1 m s u χ h).mp hm) hp eψ
  rw [lower_of_flat_factor (ResU.CompS.comm hc) hμ hσρ e₁,
    lower_of_flat_factor (ResU.CompS.comm hfπ) hμ' hσπ e₂, x₁, x₂]
  exact ⟨rfl, by simp⟩

/-- **Deep immutability, on the run a `wpTS` exhibits.**  From the tagged typed world `ρf ● ρ`,
every location beneath an `imm` cell of `⦇ρ⦈` keeps its value; with `Footprint`. -/
theorem wpTS_frozen {ls : List SRec} {e : Expr} {Q : List SRec → Val → WProp} {ρ : WRes}
    (hw : wpTS ls e Q ρ) {ρf fρ : WRes} {ps : List FrameRec} (hf : ResU.Hash ρf ρ)
    (hc : ResU.CompS ρf ρ fρ) (hT : TW fρ ps (rsOf ls)) (htg : Tagged fρ ps ls) {μ : Heap}
    (hμ : ResU.Lower fρ μ) :
    ∃ (μ' : Heap) (v : Val), Steps μ e μ' (.val v) ∧ (∃ ls' ρ', Q ls' v ρ') ∧
      Footprint ρf ρ μ μ' ∧ ∀ ℓ, Frozen ρ ℓ → μ' ℓ = μ ℓ := by
  obtain ⟨ρ', -, π, fπ, μ', v, ls', hrun, hQ, -, hA, -, hfπ, hμ'⟩ :=
    wpTS_exhibited hw hf hc hT htg hμ
  exact ⟨μ', v, hrun, ⟨ls', ρ', hQ⟩, footprint_of_upd hc hμ hfπ hμ' hA,
    fun ℓ h => (frozen_keeps hc hμ hfπ hμ' hA h).1⟩

/-! ### The flattening of a resource of `imm` cells -/

theorem sites_nil_of_immTop {ρ : WRes} (hρ : ImmTop ρ) {k : Kind} (hk : k ≠ Kind.imm)
    {d : List Loc} (hs : ResU.Sites ρ k d) : d = [] := by
  cases d with
  | nil => rfl
  | cons l d =>
      obtain ⟨ψ, e, hψk⟩ := (hs.2 l).mp (List.mem_cons_self ..)
      exact absurd (hψk.symm.trans (hρ l ψ e)) hk

theorem restrict_immTop_none {ρ : WRes} (hρ : ImmTop ρ) {k : Kind} (hk : k ≠ Kind.imm)
    (l : Loc) : (ρ.restrict k).get l = none := by
  cases e : (ρ.restrict k).get l with
  | none => rfl
  | some ψ =>
      obtain ⟨e', hψk⟩ := ResU.restrict_eq_some.mp e
      exact absurd (hψk.symm.trans (hρ l ψ e')) hk

/-- `ex(ρ)_●` is empty at a resource of `imm` cells. -/
theorem exS_immTop_none {ρ e : WRes} (he : ExS ρ e) (hρ : ImmTop ρ) (l : Loc) :
    e.get l = none := by
  rcases he with ⟨hs, _, hb, hnm, hσ⟩
  have hw := sites_nil_of_immTop hρ (by decide) hs
  rw [List.map_eq_nil_iff] at hw
  subst hw
  cases hb
  refine (ResU.Comp.eq_none_iff hσ l).mpr ⟨(ResU.Comp.eq_none_iff hnm l).mpr
    ⟨restrict_immTop_none hρ (by decide) l, restrict_immTop_none hρ (by decide) l⟩,
    PMap.empty_get l⟩

/-- A location of an iterated composition is a location of one of its members. -/
theorem bigComp_get_ne_none {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} {L : List WRes} {b : WRes}
    (h : BigComp R C L b) {l : Loc} (hl : b.get l ≠ none) : ∃ x ∈ L, x.get l ≠ none := by
  induction h with
  | nil => exact absurd (PMap.empty_get l) hl
  | @cons σ τ ρ σs _ hc ih =>
      by_cases h₁ : σ.get l = none
      · have h₂ : τ.get l ≠ none := fun h₂ => hl ((ResU.Comp.eq_none_iff hc l).mpr ⟨h₁, h₂⟩)
        obtain ⟨x, hx, hxl⟩ := ih h₂
        exact ⟨x, List.mem_cons_of_mem _ hx, hxl⟩
      · exact ⟨σ, List.mem_cons_self .., h₁⟩

/-- A location of `ag(ρ)`, at a resource of `imm` cells, is a cell of `ρ` or lies in
`⦇χ⦈_○` for the witness `χ` of one. -/
theorem agW_immTop_cov {ρ a : WRes} (ha : AgW ρ a) (hρ : ImmTop ρ) {l : Loc}
    (hl : a.get l ≠ none) :
    ρ.get l ≠ none ∨ ∃ m ψ p, ρ.get m = some ψ ∧ FlatR ψ.wit p ∧ p.get l ≠ none := by
  rcases ha with ⟨hsm, _, _, hwi, hbm, hbi, ha', hσ⟩
  have hw := sites_nil_of_immTop hρ (by decide) hsm
  rw [List.map_eq_nil_iff] at hw
  subst hw
  cases hbm
  have key := ResU.Comp.eq_none_iff hσ l
  have key' := ResU.Comp.eq_none_iff ha' l
  by_cases h₂ : ρ.get l = none
  · have ha'l := key'.mpr ⟨ResU.restrict_get_none h₂, PMap.empty_get l⟩
    obtain ⟨x, hx, hxl⟩ := bigComp_get_ne_none hbi (fun h0 => hl (key.mpr ⟨ha'l, h0⟩))
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    obtain ⟨ψ, e, a, hψ, he, ha, hc⟩ := AgWitsI.mem hwi q hq
    exact Or.inr ⟨q.1, ψ, q.2, hψ, ⟨e, a, he, ha, hc⟩, hxl⟩
  · exact Or.inl h₂

/-- **Every location of `⦇ρ⦈`, at a resource of `imm` cells, is a cell of `ρ` or frozen.** -/
theorem flat_immTop_cov {ρ σ : WRes} (hσ : ResU.Flat ρ σ) (hρ : ImmTop ρ) {l : Loc}
    (hl : σ.get l ≠ none) : ρ.get l ≠ none ∨ Frozen ρ l := by
  obtain ⟨e, a, he, ha, hc⟩ := id hσ
  have hal : a.get l ≠ none := fun h0 =>
    hl ((ResU.Comp.eq_none_iff hc l).mpr ⟨exS_immTop_none he hρ l, h0⟩)
  rcases agW_immTop_cov ha hρ hal with h | ⟨m, ψ, p, hψ, hp, hpl⟩
  · exact Or.inl h
  · obtain ⟨χ', e', k', x', w'⟩ := ResU.Flat.get hσ hψ
    obtain ⟨s', hs', eχ⟩ := CellU.imm_eta (k'.trans (hρ m ψ hψ))
    refine Or.inr ⟨m, s', χ'.erase, χ'.wit, hs', p, ⟨σ, hσ, ?_⟩, w' ▸ hp, hpl⟩
    rw [e', ← eχ]

/-- A resource updated from one of `imm` cells has no `mut` cell. -/
theorem upd_immTop_noMut {ρ π : WRes} (hρ : ImmTop ρ) (hA : ResU.UpdV ρ π) {m : Loc}
    {ψ : CellU Loc Val} (hm : π.get m = some ψ) : ψ.kind ≠ Kind.mut := by
  intro hk
  obtain ⟨σρ, hσρ⟩ := hA.2.1
  obtain ⟨σπ, hσπ⟩ := hA.2.2
  obtain ⟨χ'', e'', k'', -, -⟩ := ResU.Flat.get hσπ hm
  rcases CellU.rep χ'' with ⟨w, rfl⟩ | ⟨s, w, ξ, hξ, rfl⟩ | ⟨b, w, ξ, hξ, P, hP, rfl⟩
  · rw [hk] at k''; exact absurd k'' (by simp)
  · rw [hk] at k''; exact absurd k'' (by simp)
  · obtain ⟨w', ξ', hξ', hP', hfa⟩ := (hA.1.2 m b P).mpr ⟨w, ξ, hξ, hP, ⟨σπ, hσπ, e''⟩⟩
    have hgρ := (ResU.flatAt_iff hσρ m _).mp hfa
    rcases flat_immTop_cov hσρ hρ (by rw [hgρ]; simp) with htop | hfr
    · obtain ⟨ψρ, eρ⟩ := Option.ne_none_iff_exists'.mp htop
      obtain ⟨χρ, eχρ, kχρ, -, -⟩ := ResU.Flat.get hσρ eρ
      rw [hgρ] at eχρ
      cases Option.some.inj eχρ
      have := kχρ.trans (hρ m ψρ eρ)
      simp at this
    · obtain ⟨m₀, s, u, χ, h, p, hm₀, hp, hpm⟩ := hfr
      obtain ⟨eπ, aπ, heπ, haπ, hcπ⟩ := id hσπ
      have hg₀ : σπ.get m₀ = some (CellU.immOf s u χ h) :=
        (ResU.flatAt_iff hσπ m₀ _).mp ((hA.1.1 m₀ s u χ h).mp hm₀)
      obtain ⟨ev, av, p', z, hev, hav, hcc, hz⟩ := ResU.flat_imm_wit_factor heπ haπ hcπ hg₀
      obtain rfl := FlatR.functional hp ⟨ev, av, hev, hav, hcc⟩
      have ham : aπ.get m ≠ none := fun h0 => hpm ((ResU.Comp.eq_none_iff hz m).mp h0).1
      obtain ⟨ζ, eζ⟩ := Option.ne_none_iff_exists'.mp ham
      have hem := ExS.get_of_ne_imm heπ hm (by rw [hk]; decide)
      have := (CellU.CompatS.kinds (hcπ.1 m ψ ζ hem eζ)).1
      rw [hk] at this
      exact absurd this (by decide)

/-- A resource updated from one of `imm` cells, owning no cell, is one of `imm` cells. -/
theorem upd_immTop {ρ π : WRes} (hρ : ImmTop ρ) (hA : ResU.UpdV ρ π) (hno : NoOwn π) :
    ImmTop π := by
  intro l ψ hψ
  cases hk : ψ.kind with
  | imm => rfl
  | «mut» => exact absurd hk (upd_immTop_noMut hρ hA hψ)
  | own =>
      have : (π.restrict Kind.own).get l = some ψ := ResU.restrict_eq_some.mpr ⟨hψ, hk⟩
      rw [hno, PMap.empty_get] at this
      cases this

/-- **`⦇π⦈`'s locations are `⦇ρ⦈`'s**, for `ρ` of `imm` cells and `ρ ↭ π` with `π` owning no
cell. -/
theorem upd_immTop_dom {ρ π σρ σπ : WRes} (hρ : ImmTop ρ) (hA : ResU.UpdV ρ π) (hno : NoOwn π)
    (hσρ : ResU.Flat ρ σρ) (hσπ : ResU.Flat π σπ) {l : Loc} (hl : σπ.get l ≠ none) :
    σρ.get l ≠ none := by
  rcases flat_immTop_cov hσπ (upd_immTop hρ hA hno) hl with htop | hfr
  · obtain ⟨ψ, eψ⟩ := Option.ne_none_iff_exists'.mp htop
    obtain ⟨χ', e', k', -, -⟩ := ResU.Flat.get hσπ eψ
    obtain ⟨s', hs', eχ⟩ := CellU.imm_eta (k'.trans (upd_immTop hρ hA hno l ψ eψ))
    have hfa : π.FlatAt l (CellU.immOf s' χ'.erase χ'.wit hs') := ⟨σπ, hσπ, by rw [e', ← eχ]⟩
    rw [(ResU.flatAt_iff hσρ l _).mp ((hA.1.1 l s' _ _ hs').mpr hfa)]
    simp
  · obtain ⟨m, s, u, χ, h, p, hm, hp, hpl⟩ := hfr
    obtain ⟨ψ, eψ⟩ := Option.ne_none_iff_exists'.mp hpl
    obtain ⟨χ₁, e₁, -⟩ := flat_of_frozen_cell hσρ ((hA.1.1 m s u χ h).mpr hm) hp eψ
    rw [e₁]; simp

/-- **A resource of `imm` cells is given back whole.**  If the initial heap lowers `ρf ● ρ` with
`ρ` of `imm` cells, the final heap lowers `ρf ● π`, `ρ ↭ π`, and `π` owns no cell, then the final
heap is the initial heap. -/
theorem heap_restored {ρf ρ π fρ fπ : WRes} {μ μ' : Heap} (hc : ResU.CompS ρf ρ fρ)
    (hμ : ResU.Lower fρ μ) (hfπ : ResU.CompS ρf π fπ) (hμ' : ResU.Lower fπ μ')
    (hA : ResU.UpdV ρ π) (hρ : ImmTop ρ) (hno : NoOwn π) : μ' = μ := by
  have hfp := footprint_of_upd hc hμ hfπ hμ' hA
  funext l
  by_cases hl : μ l = none
  · rw [hl]
    by_contra hl'
    obtain ⟨σX, σY, hX, hY, hdom⟩ := lower_dom_factor hfπ hμ' hl'
    rcases hdom with hx | hy
    · obtain ⟨ψ, eψ⟩ := Option.ne_none_iff_exists'.mp hx
      rw [lower_of_flat_factor hc hμ hX eψ] at hl
      cases hl
    · obtain ⟨σρ, hσρ⟩ := hA.2.1
      obtain ⟨ψ, eψ⟩ := Option.ne_none_iff_exists'.mp (upd_immTop_dom hρ hA hno hσρ hY hy)
      rw [lower_of_flat_factor (ResU.CompS.comm hc) hμ hσρ eψ] at hl
      cases hl
  · obtain ⟨σX, σY, hX, hY, hdom⟩ := lower_dom_factor hc hμ hl
    rcases hdom with hx | hy
    · obtain ⟨ψ, eψ⟩ := Option.ne_none_iff_exists'.mp hx
      exact hfp.1 l ψ ⟨σX, hX, eψ⟩
    · rcases flat_immTop_cov hY hρ hy with htop | hfr
      · obtain ⟨ψ, eψ⟩ := Option.ne_none_iff_exists'.mp htop
        exact hfp.2.1 l hl (immOnly_of_get eψ (hρ l ψ eψ))
      · exact (frozen_keeps hc hμ hfπ hμ' hA hfr).1

end BoCa.Purity

end
