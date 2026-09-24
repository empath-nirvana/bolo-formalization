import Paper.S5_Model.Definitions
import Paper.S6_2_NonStandardLemmas.Definitions
import Support.Model.CellFacts
import Support.Model.Cells
import Support.Model.Composition
import Support.Model.Prelude
import Support.Model.Update
import Support.Model.Walks

/-!
# [TR] §6.2 — remarks on Definition 6.2

`ψ ∼ ψ′` (row 5.65): transitivity, and `upd_iff_sim`, the theorem that `[CONF]`
Fig. 18b's two clauses of `↭` and `[TR]` §6's "same domain, `∼` pointwise" form are
the same relation.  Lemmas 6.39 and 6.59 read `↭` through it.

These are theorems about printed definitions — rows of the source's
`docs/definition-inventory.md` whose Lean is a theorem — whose proofs use results
of `[TR]` §6, so they cannot sit with the definitions.  Each carries the row's
number, printed form, page, tag and note.  A row's theorem that a §6 result's Lean
needs is declared in that result's file, and the row here says where.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### 5.65 · `ψ ∼ ψ′ ≔ (ψ = mut(α,_,_,P̂) ∧ ψ′ = mut(α,_,_,P̂)) ∨ (ψ = ψ′ = imm(ᾱ,v,ρ))` — [TR] Definition 6.2, not a p. 5 row · [TR] p. 13 · `[as printed]`

[TR] p. 13 prints it and then unfolds `↭` through it at Lemmas 6.39, 6.40, 6.44 and 6.59, always as "dom(⦇ρ₁⦈∣imm,mut) = dom(⦇ρ₂⦈∣imm,mut) and for every ℓ in that domain, ⦇ρ₁⦈(ℓ) ∼ ⦇ρ₂⦈(ℓ)". Read at 1200 dpi: α and P̂ are bound outside the `mut` conjunction and the two `_`s — value and witness — inside each conjunct, while the `imm` disjunct asks for equality outright, which is `BoCa.Fig16.ResU.UpdImm`/`UpdMut`'s asymmetry printed as one relation. `upd_iff_sim` is the bridge and it is a theorem: [CONF] Fig. 18b's two clauses and [TR] §6's `dom + ∼` form are the same relation, both flattenings named (G4). `ResU.borrowPart` is `ρ∣imm,mut`, the same printed coverage gap row 5.51 closes for `ρ∣own,mut`. [TR] Lemma 6.44's proof asserts `∼` is transitive "since imms are required to be equal and muts are required to have" the same lifetime and invariant; `CellU.Sim.trans` is that. **This definition had no row and no Lean declaration before this entry**, which is why [TR] §6's proofs had no printed route to follow
-/
/-- **`∼` is transitive** — `[TR]` Lemma 6.44's proof says so and why: *"imms
are required to be equal and muts are required to have"* the same lifetime and
invariant.  The middle cell cannot be both an `imm` and a `mut`, so the two
disjuncts cannot be crossed.
`[about ours: the transitivity of `∼` that `[TR]` Lemma 6.44's proof asserts]` -/
theorem CellU.Sim.trans {ψ₁ ψ₂ ψ₃ : CellU Loc Val} (h₁ : CellU.Sim ψ₁ ψ₂)
    (h₂ : CellU.Sim ψ₂ ψ₃) : CellU.Sim ψ₁ ψ₃ := by
  rcases h₁ with ⟨a, P, hA, ⟨v₂, χ₂, h₂', hw₂, e₂⟩⟩ | ⟨s, v, χ, hh, e₁, e₂⟩
  · rcases h₂ with ⟨a', P', ⟨v₃, χ₃, h₃', hw₃, e₃⟩, hC⟩ | ⟨s', v', χ', hh', e₃, e₄⟩
    · rw [e₂] at e₃
      obtain rfl : a = a' := CellU.mutOf_at e₃
      obtain ⟨-, -, rfl⟩ := CellU.mutOf_inj e₃
      exact Or.inl ⟨a, P, hA, hC⟩
    · exact absurd (e₃.symm.trans e₂) CellU.immOf_ne_mutOf
  · rcases h₂ with ⟨a', P', ⟨v₃, χ₃, h₃', hw₃, e₃⟩, -⟩ | ⟨s', v', χ', hh', e₃, e₄⟩
    · exact absurd (e₂.symm.trans e₃) CellU.immOf_ne_mutOf
    · rw [e₂] at e₃
      obtain ⟨rfl, rfl, rfl⟩ := CellU.immOf_inj e₃
      exact Or.inr ⟨s, v, χ, hh, e₁, e₄⟩

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {R : CellU Loc Val → CellU Loc Val → Prop}
variable {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}

/-!
### Row 5.56's theorem `BoCa.Fig16.BigComp.perm`, ahead of its file

A remark on a printed definition of `[TR]` §5; its proof uses results of §6, and the Lean of row 5.65's theorem in this file uses it, so it is declared here.  The row is recorded in `Paper/S5_Model/Remarks.lean`.
-/
/-- **The fold list may be reordered.**  This is what §16 owes: "`⨀` folds a
list, and that the value does not depend on the fold needs `[TR]` Lemmas 6.1,
6.2 and 6.3".  6.1 enters through `ResU.Comp.comm_of_laws`, 6.2 and 6.3 through
`BigComp.swap`.
`[about ours: `BigComp` is §16's fold shape; the printed `⨀` is the order-free
operator this makes it]` -/
theorem BigComp.perm (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) (hC : ResU.CompLaws C)
    {l l' : List (ResU Loc Val)} (hp : l.Perm l') {b b' : ResU Loc Val}
    (h : BigComp R C l b) (h' : BigComp R C l' b') : b = b' :=
  BigComp.functional hC (BigComp.of_perm hR hC hp h) h'

/-! `[about ours]` — what the Lean of row 5.65's theorem needs; the paper prints nothing here. -/
/-- `BigComp.perm` in the form the walks use: two families indexed by the same
`ResU.Sites` set, agreeing location by location, fold to one value.
`[about ours: `ResU.Sites` is convention G6's index set]` -/
theorem BigComp.sites (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) (hC : ResU.CompLaws C)
    {ρ : ResU Loc Val} {k : Kind} {w w' : List (Loc × ResU Loc Val)}
    (hs : ResU.Sites ρ k (w.map Prod.fst)) (hs' : ResU.Sites ρ k (w'.map Prod.fst))
    (hval : ∀ p ∈ w, ∀ q ∈ w', p.1 = q.1 → p.2 = q.2)
    {b b' : ResU Loc Val}
    (h : BigComp R C (w.map Prod.snd) b) (h' : BigComp R C (w'.map Prod.snd) b') :
    b = b' :=
  BigComp.perm hR hC ((List.perm_of_keys hs.1 (hs.perm hs') hval).map Prod.snd) h h'

/-- **`ex(ρ)_◐` is single-valued**, so `[TR]` p. 5's `ex(ρ)_◐` and `[CONF]`
Fig. 18a's `E⦇ρ⦈_◐` — both printed as terms — name `ExW` unambiguously.

The two derivations enumerate `ρ`'s `mut` locations in possibly different
orders, and the values they pair with those locations agree only by the
induction hypothesis.  So the family motive is pointwise: at each location the
paired value is the only walk of that cell's witness.  Spending it at every
shared location makes the two lists permutations (`BigComp.sites`), `⨀` then
has one value, and `ResU.Comp.functional` closes the two outer `◐`s.
`[about ours: the print's `ex(ρ)_◐` is a term and `ExW` is its graph (G4); this
is the proof that the graph is a function — the debt §16 and §22 record]` -/
theorem ExW.functional (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) (hC : ResU.CompLaws C)
    {ρ σ σ' : ResU Loc Val} (h : ExW R C ρ σ) (h' : ExW R C ρ σ') : σ = σ' := by
  refine ExW.rec (motive_1 := fun ρ σ _ => ∀ τ, ExW R C ρ τ → σ = τ)
    (motive_2 := fun ρ w _ => ∀ p ∈ w,
      ∃ ψ, ρ.get p.1 = some ψ ∧ ∀ e, ExW R C ψ.wit e → p.2 = e)
    ?mk ?nil ?cons h σ' h'
  -- The walk itself; `ih` is the family hypothesis of the same induction.
  case mk =>
    intro ρ₀ σ₀ nm b w hs _ hb hnm hσ ih τ hτ
    cases hτ with
    | mk hs' hw' hb' hnm' hσ' =>
        have hnn : nm = _ := ResU.Comp.functional hC.functional hnm hnm'
        have hbb : b = _ :=
          BigComp.sites hR hC hs hs'
            (fun p hp q hq hpq => by
              obtain ⟨ψ, hψ, hfun⟩ := ih p hp
              obtain ⟨ψ', hψ', he'⟩ := ExWits.mem hw' q hq
              rw [hpq, hψ'] at hψ
              cases Option.some.inj hψ
              exact hfun q.2 he') hb hb'
        exact ResU.Comp.functional hC.functional hσ (hnn ▸ hbb ▸ hσ')
  -- The empty family has no entry to disagree at.
  case nil => intro _ p hp; exact absurd hp (by simp)
  -- With a head, either the entry asked about is it — and the walk induction
  -- hypothesis fixes its value — or it is in the tail.
  case cons =>
    intro _ _ _ _ ψ hψ _ _ _ ihe ihw p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨ψ, hψ, fun e' he' => ihe e' he'⟩
    · exact ihw p hp

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- `ex(ρ)_●` is a term.  `[about ours: `ExS` is the graph of `[TR]` p. 5's
`ex(ρ)_●`; this is the proof that the graph is a function]` -/
theorem ExS.functional {ρ σ σ' : ResU Loc Val} (h : ExS ρ σ) (h' : ExS ρ σ') :
    σ = σ' :=
  ExW.functional (fun _ _ _ hc => CellU.CompS.compat hc) ResU.compLawsS h h'

/-- `ex(ρ)_○` is a term — the one `ag`'s third piece calls.
`[about ours: `ExR` is the graph of `[TR]` p. 5's `ex(ρ)_○`; this is the proof
that the graph is a function]` -/
theorem ExR.functional {ρ σ σ' : ResU Loc Val} (h : ExR ρ σ) (h' : ExR ρ σ') :
    σ = σ' :=
  ExW.functional (fun _ _ ψ hc => ⟨ψ, hc⟩) ResU.compLawsR h h'

/-- **`ag(ρ)` is single-valued**, so `[TR]` p. 5's `ag(ρ)` and `[CONF]`
Fig. 18a's `A⦇ρ⦈` name `AgW` unambiguously.  Both comprehensions are families
over `ResU.Sites` lists, so both are pinned up to order and `BigComp.permR`
closes each `◯`; the two outer `○`s are `ResU.CompR.functional`.  `ag` is
always at `○`, so the schema hypotheses are discharged here rather than taken.
`[about ours: the print's `ag(ρ)` is a term and `AgW` is its graph (G4); this is
the proof that the graph is a function — the debt §16 and §22 record]` -/
theorem AgW.functional {ρ σ σ' : ResU Loc Val} (h : AgW ρ σ) (h' : AgW ρ σ') :
    σ = σ' := by
  refine AgW.rec (motive_1 := fun ρ σ _ => ∀ τ, AgW ρ τ → σ = τ)
    (motive_2 := fun ρ w _ => ∀ p ∈ w,
      ∃ ψ, ρ.get p.1 = some ψ ∧ ∀ e, AgW ψ.wit e → p.2 = e)
    (motive_3 := fun ρ w _ => ∀ p ∈ w,
      ∃ ψ, ρ.get p.1 = some ψ ∧ ∀ e a q, ExR ψ.wit e → AgW ψ.wit a →
        ResU.CompR e a q → p.2 = q)
    ?mk ?nilM ?consM ?nilI ?consI h σ' h'
  case mk =>
    intro ρ₀ σ₀ a bm bi wm wi hsm hsi _ _ hbm hbi ha hσ ihm ihi τ hτ
    cases hτ with
    | mk hsm' hsi' hwm' hwi' hbm' hbi' ha' hσ' =>
        have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
          fun _ _ ψ hc => ⟨ψ, hc⟩
        have hbm₀ : bm = _ :=
          BigComp.sites hR ResU.compLawsR hsm hsm'
            (fun p hp q hq hpq => by
              obtain ⟨ψ, hψ, hfun⟩ := ihm p hp
              obtain ⟨ψ', hψ', hag'⟩ := AgWitsM.mem hwm' q hq
              rw [hpq, hψ'] at hψ
              cases Option.some.inj hψ
              exact hfun q.2 hag') hbm hbm'
        have hbi₀ : bi = _ :=
          BigComp.sites hR ResU.compLawsR hsi hsi'
            (fun p hp q hq hpq => by
              obtain ⟨ψ, hψ, hfun⟩ := ihi p hp
              obtain ⟨ψ', e', a', hψ', hex', hag', hc'⟩ := AgWitsI.mem hwi' q hq
              rw [hpq, hψ'] at hψ
              cases Option.some.inj hψ
              exact hfun e' a' q.2 hex' hag' hc') hbi hbi'
        have haa : a = _ := ResU.CompR.functional ha (hbm₀ ▸ ha')
        exact ResU.CompR.functional hσ (haa ▸ hbi₀ ▸ hσ')
  case nilM => intro _ p hp; exact absurd hp (by simp)
  case consM =>
    intro _ _ _ _ ψ hψ _ _ _ ihe ihw p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨ψ, hψ, fun e' hag => ihe e' hag⟩
    · exact ihw p hp
  case nilI => intro _ p hp; exact absurd hp (by simp)
  -- The `imm` entry is `ex(ρ′)_○ ○ ag(ρ′)`: the first factor is pinned by
  -- `ExR.functional`, the second by the induction hypothesis.
  case consI =>
    intro _ _ _ _ ψ hψ _ e a hex _ hc _ iha ihw p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · refine ⟨ψ, hψ, fun e' a' q hex' hag' hc' => ?_⟩
      have hee : e = e' := ExR.functional hex hex'
      have haa : a = a' := iha a' hag'
      exact ResU.CompR.functional hc (hee ▸ haa ▸ hc')
    · exact ihw p hp

/-- **`⦇ρ⦈` is a term** — `⦇ρ⦈ ≜ ex(ρ)_● ● ag(ρ)` (`[TR]` p. 5).
`[about ours: `ResU.Flat` is the graph of the printed `⦇ρ⦈` (G4); this is the
proof that the graph is a function]` -/
theorem ResU.Flat.functional {ρ σ σ' : ResU Loc Val}
    (h : ρ.Flat σ) (h' : ρ.Flat σ') : σ = σ' := by
  obtain ⟨e, a, hex, hag, hc⟩ := h
  obtain ⟨e', a', hex', hag', hc'⟩ := h'
  have he : e = e' := ExS.functional hex hex'
  have ha : a = a' := AgW.functional hag hag'
  subst he; subst ha
  exact ResU.CompS.functional hc hc'

/-- Once a flattening is in hand, the lookup is a lookup in it. -/
theorem ResU.flatAt_iff {ρ σ : ResU Loc Val} (h : ρ.Flat σ) (l : Loc)
    (ψ : CellU Loc Val) : ρ.FlatAt l ψ ↔ σ.get l = some ψ :=
  ⟨fun ⟨_, hf, hg⟩ => by cases ResU.Flat.functional hf h; exact hg, fun hg => ⟨σ, h, hg⟩⟩

/-- One direction, at one location: `↭` sends a borrow cell of `⦇ρ₁⦈` to a
`∼`-related cell of `⦇ρ₂⦈`. -/
theorem ResU.sim_of_upd {ρ₁ ρ₂ σ₁ σ₂ : ResU Loc Val} (h : ResU.Upd ρ₁ ρ₂)
    (h₁ : ResU.Flat ρ₁ σ₁) (h₂ : ResU.Flat ρ₂ σ₂)
    {l : Loc} {ψ : CellU Loc Val} (hg : σ₁.get l = some ψ)
    (hk : ψ.kind ≠ Kind.own) : ∃ ψ', σ₂.get l = some ψ' ∧ CellU.Sim ψ ψ' := by
  rcases CellU.rep ψ with ⟨v, rfl⟩ | ⟨s, v, χ, hh, rfl⟩ | ⟨b, v, χ, hh, P, hw, rfl⟩
  · exact absurd (by simp : (CellU.ownOf (Loc := Loc) v).kind = Kind.own) hk
  · refine ⟨CellU.immOf s v χ hh, ?_, Or.inr ⟨s, v, χ, hh, rfl, rfl⟩⟩
    exact (ResU.flatAt_iff h₂ l _).mp ((h.1 l s v χ hh).mp ⟨σ₁, h₁, hg⟩)
  · obtain ⟨v', χ', h', hw', hfa⟩ := (h.2 l b P).mp ⟨v, χ, hh, hw, ⟨σ₁, h₁, hg⟩⟩
    exact ⟨CellU.mutOf b v' χ' h' P hw', (ResU.flatAt_iff h₂ l _).mp hfa,
      Or.inl ⟨b, P, ⟨v, χ, hh, hw, rfl⟩, ⟨v', χ', h', hw', rfl⟩⟩⟩

/-!
Row 5.65, continued.
-/
/-- **`↭` is the form `[TR]` §6's proofs unfold it to.**  `[CONF]` Fig. 18b's
two clauses and `[TR]`'s *"`dom(⦇ρ₁⦈|imm,mut) = dom(⦇ρ₂⦈|imm,mut)` and pointwise
`∼`"* are the same relation, with both flattenings named (G4).
`[about ours: `[CONF]` Fig. 18b's `↭` against the form `[TR]` §6's proofs use]` -/
theorem ResU.upd_iff_sim {ρ₁ ρ₂ σ₁ σ₂ : ResU Loc Val}
    (h₁ : ResU.Flat ρ₁ σ₁) (h₂ : ResU.Flat ρ₂ σ₂) :
    ResU.Upd ρ₁ ρ₂ ↔ ResU.SimForm σ₁ σ₂ := by
  constructor
  · intro h
    refine ⟨fun l => ⟨?_, ?_⟩, fun l ψ hb => ?_⟩
    · rintro ⟨ψ, hb⟩
      obtain ⟨hg, hk⟩ := ResU.borrowPart_eq_some.mp hb
      obtain ⟨ψ', hg', hsim⟩ := ResU.sim_of_upd h h₁ h₂ hg hk
      refine ⟨ψ', ResU.borrowPart_eq_some.mpr ⟨hg', ?_⟩⟩
      rcases hsim with ⟨a, P, -, ⟨v, χ, hh, hw, rfl⟩⟩ | ⟨s, v, χ, hh, -, rfl⟩
      · simp
      · simp
    · rintro ⟨ψ, hb⟩
      obtain ⟨hg, hk⟩ := ResU.borrowPart_eq_some.mp hb
      obtain ⟨ψ', hg', hsim⟩ := ResU.sim_of_upd h.symm h₂ h₁ hg hk
      refine ⟨ψ', ResU.borrowPart_eq_some.mpr ⟨hg', ?_⟩⟩
      rcases hsim with ⟨a, P, -, ⟨v, χ, hh, hw, rfl⟩⟩ | ⟨s, v, χ, hh, -, rfl⟩
      · simp
      · simp
    · obtain ⟨hg, hk⟩ := ResU.borrowPart_eq_some.mp hb
      exact ResU.sim_of_upd h h₁ h₂ hg hk
  · rintro ⟨hd, hs⟩
    have hback : ∀ (l : Loc) (ψ₂ : CellU Loc Val), σ₂.borrowPart.get l = some ψ₂ →
        ∃ ψ₁, σ₁.get l = some ψ₁ ∧ CellU.Sim ψ₂ ψ₁ := by
      intro l ψ₂ hb₂
      obtain ⟨ψ₁, hb₁⟩ := (hd l).mpr ⟨ψ₂, hb₂⟩
      obtain ⟨ψ₂', hg₂', hsim⟩ := hs l ψ₁ hb₁
      obtain ⟨hg₂, -⟩ := ResU.borrowPart_eq_some.mp hb₂
      rw [hg₂] at hg₂'
      cases Option.some.inj hg₂'
      exact ⟨ψ₁, (ResU.borrowPart_eq_some.mp hb₁).1, hsim.symm⟩
    refine ⟨fun l s v χ hh => ?_, fun l b P => ?_⟩
    · rw [ResU.flatAt_iff h₁, ResU.flatAt_iff h₂]
      constructor
      · intro hg
        obtain ⟨ψ', hg', hsim⟩ :=
          hs l _ (ResU.borrowPart_eq_some.mpr ⟨hg, by simp⟩)
        rcases hsim with ⟨a, P, ⟨v₁, χ₁, h₁', hw₁, e₁⟩, -⟩ | ⟨s', v', χ', h', e₁, e₂⟩
        · exact absurd e₁ CellU.immOf_ne_mutOf
        · obtain ⟨hs2, hv2, hχ2⟩ := CellU.immOf_inj e₁
          subst hs2; subst hv2; subst hχ2
          rw [hg']; exact congrArg some e₂
      · intro hg
        obtain ⟨ψ', hg', hsim⟩ :=
          hback l _ (ResU.borrowPart_eq_some.mpr ⟨hg, by simp⟩)
        rcases hsim with ⟨a, P, ⟨v₁, χ₁, h₁', hw₁, e₁⟩, -⟩ | ⟨s', v', χ', h', e₁, e₂⟩
        · exact absurd e₁ CellU.immOf_ne_mutOf
        · obtain ⟨hs2, hv2, hχ2⟩ := CellU.immOf_inj e₁
          subst hs2; subst hv2; subst hχ2
          rw [hg']; exact congrArg some e₂
    · constructor
      · rintro ⟨v, χ, hh, hw, hfa⟩
        rw [ResU.flatAt_iff h₁] at hfa
        obtain ⟨ψ', hg', hsim⟩ :=
          hs l _ (ResU.borrowPart_eq_some.mpr ⟨hfa, by simp⟩)
        rcases hsim with ⟨a, P', ⟨v₁, χ₁, h₁', hw₁, e₁⟩, ⟨v₂, χ₂, h₂', hw₂, e₂⟩⟩ |
            ⟨s', v', χ', h', e₁, e₂⟩
        · obtain rfl : b = a := CellU.mutOf_at e₁
          obtain ⟨-, -, hPP⟩ := CellU.mutOf_inj e₁
          subst hPP
          exact ⟨v₂, χ₂, h₂', hw₂, (ResU.flatAt_iff h₂ l _).mpr (e₂ ▸ hg')⟩
        · exact absurd e₁.symm CellU.immOf_ne_mutOf
      · rintro ⟨v, χ, hh, hw, hfa⟩
        rw [ResU.flatAt_iff h₂] at hfa
        obtain ⟨ψ', hg', hsim⟩ :=
          hback l _ (ResU.borrowPart_eq_some.mpr ⟨hfa, by simp⟩)
        rcases hsim with ⟨a, P', ⟨v₁, χ₁, h₁', hw₁, e₁⟩, ⟨v₂, χ₂, h₂', hw₂, e₂⟩⟩ |
            ⟨s', v', χ', h', e₁, e₂⟩
        · obtain rfl : b = a := CellU.mutOf_at e₁
          obtain ⟨-, -, hPP⟩ := CellU.mutOf_inj e₁
          subst hPP
          exact ⟨v₂, χ₂, h₂', hw₂, (ResU.flatAt_iff h₁ l _).mpr (e₂ ▸ hg')⟩
        · exact absurd e₁.symm CellU.immOf_ne_mutOf

end BoCa.Fig16

end
