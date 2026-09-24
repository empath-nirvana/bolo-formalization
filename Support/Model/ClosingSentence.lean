import Paper.S1_Syntax.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Paper.S6_2_NonStandardLemmas.Definitions
import Support.Model.Algebra
import Support.Model.AlgebraInstances
import Support.Model.Ancestors
import Support.Model.CellFacts
import Support.Model.Cells
import Support.Model.Composition
import Support.Model.FlatteningCells
import Support.Model.Lifetimes
import Support.Model.Prelude
import Support.Model.Reborrow
import Support.Model.ReborrowFrame
import Support.Model.ReborrowLowering
import Support.Model.Restriction
import Support.Model.Singletons
import Support.Model.Subtraction
import Support.Model.Surgery
import Support.Model.Update
import Support.Model.WalkSplitting
import Support.Model.Walks

/-!
# Support — Model — ClosingSentence

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
Lemma 6.59's closing sentence, clause by clause: the reborrowed location, the attribution of cells to `ρᵢ`, and the case off `dom(ρ_reb)`.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- **The exclusive walk at `○` splits along a `●`.**  The hypothesis is the `●`
that `[CONF]` p. 415:24 fn. 1's `≤` supplies (`ResU.Le`); only the walk and the
conclusion are at `○`.

This is **not** `[TR]` 6.18 at `○`, whose hypothesis would be `▷◁`: the `●` is
what makes the `own` and `mut` sites disjoint between the two operands, and that
disjointness is what `ResU.Sites.split_pairs` needs.  Every step of 6.18's
printed proof survives the change of mode — `ResU.CompS.restrict` then
`ResU.CompS.toCompR` for the printed second line, and `ResU.CompR.exchange₄`
for the third and the fourth.
`[about ours: `[TR]` 6.18's proof at a `●` hypothesis and an `○` walk]` -/
theorem ExR.split_of_compS {ρ₁ ρ₂ ρ₁₂ w : ResU Loc Val}
    (h₁₂ : ResU.CompS ρ₁ ρ₂ ρ₁₂) :
    ExR ρ₁₂ w ↔ ∃ σ₁ σ₂, ExR ρ₁ σ₁ ∧ ExR ρ₂ σ₂ ∧ ResU.CompR σ₁ σ₂ w := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  have hown : ResU.CompR (ρ₁.restrict Kind.own) (ρ₂.restrict Kind.own)
      (ρ₁₂.restrict Kind.own) :=
    ResU.CompS.toCompR (ResU.CompS.restrict h₁₂ Kind.own)
  have hmut : ResU.CompR (ρ₁.restrict Kind.mut) (ρ₂.restrict Kind.mut)
      (ρ₁₂.restrict Kind.mut) :=
    ResU.CompS.toCompR (ResU.CompS.restrict h₁₂ Kind.mut)
  constructor
  · intro h
    cases h with
    | mk hs hw hb hnm hσ =>
        rename_i u
        obtain ⟨u₁, u₂, hperm, hs₁, hs₂, hsub₁, hsub₂⟩ :=
          ResU.Sites.split_pairs h₁₂ Kind.mut_ne_imm hs
        have hperm' : (u.map Prod.snd).Perm (u₁.map Prod.snd ++ u₂.map Prod.snd) := by
          rw [← List.map_append]
          exact hperm.map Prod.snd
        obtain ⟨b₁, b₂, hb₁, hb₂, hbc⟩ :=
          (BigComp.append hR ResU.compLawsR).mp
            (BigComp.of_perm hR ResU.compLawsR hperm' hb)
        obtain ⟨nm₁, nm₂, hnm₁, hnm₂, hnmc⟩ :=
          (ResU.CompR.exchange₄ _ _ _ _ _).mp ⟨_, _, hown, hmut, hnm⟩
        obtain ⟨σ₁, σ₂, hσ₁, hσ₂, hσc⟩ :=
          (ResU.CompR.exchange₄ nm₁ nm₂ b₁ b₂ w).mp ⟨_, _, hnmc, hbc, hσ⟩
        exact ⟨σ₁, σ₂,
          ExW.mk hs₁ (ExWits.to_compS_left h₁₂ hw hsub₁ hs₁) hb₁ hnm₁ hσ₁,
          ExW.mk hs₂ (ExWits.to_compS_right h₁₂ hw hsub₂ hs₂) hb₂ hnm₂ hσ₂,
          hσc⟩
  · rintro ⟨σ₁, σ₂, h₁, h₂, hc⟩
    cases h₁ with
    | mk hs₁ hw₁ hb₁ hnm₁ hσ₁ =>
        rename_i u₁
        cases h₂ with
        | mk hs₂ hw₂ hb₂ hnm₂ hσ₂ =>
            rename_i u₂
            obtain ⟨nm, b, hnmc, hbc, hσ⟩ :=
              (ResU.CompR.exchange₄ _ _ _ _ w).mpr ⟨σ₁, σ₂, hσ₁, hσ₂, hc⟩
            obtain ⟨O, M, hO, hM, hOM⟩ :=
              (ResU.CompR.exchange₄ _ _ _ _ nm).mpr ⟨_, _, hnm₁, hnm₂, hnmc⟩
            obtain rfl : O = ρ₁₂.restrict Kind.own := ResU.CompR.functional hO hown
            obtain rfl : M = ρ₁₂.restrict Kind.mut := ResU.CompR.functional hM hmut
            refine ExW.mk (w := u₁ ++ u₂) ?_
              (ExWits.append (ExWits.of_compS_left h₁₂ hw₁)
                (ExWits.of_compS_right h₁₂ hw₂)) ?_ hOM hσ
            · rw [List.map_append]
              exact ResU.Sites.append_of_compS h₁₂ Kind.mut_ne_imm hs₁ hs₂
            · rw [List.map_append]
              exact (BigComp.append hR ResU.compLawsR).mpr ⟨_, _, hb₁, hb₂, hbc⟩

/-- **The witness `reb_α` fabricates at an `own` cell is a `●`-factor of the
source.**  `[TR]` p. 5 sets it to `π(ℓ)/ℓ`; `π(ℓ)` is one piece of the family the
filled `⨀` folds, `ρ ≥ ⨀_{ℓ} π(ℓ)` puts the fold below `ρ`, and `ρ/ℓ ≤ ρ`
(`ResU.del_compS`) takes the last step.  With `ResU.flatR_le_of_compS` this puts
`⦇π(ℓ)/ℓ⦈_○` inside `⦇ρ⦈_○`, which is what the `mut` clause gets for free from
`ExW.wit_le` and `AgW.mut_wit_le`.
`[about ours: `[TR]` p. 5's `π(ℓ)/ℓ` against `ρ ≥ ⨀_{ℓ} π(ℓ)`]` -/
theorem ResU.reb_own_wit_le {α : Life} {ρ ρ' : ResU Loc Val} (h : ResU.Reb α ρ ρ')
    {l : Loc} {v : Val} {χ : ResU Loc Val}
    {hχ : χ.InStratum (LSet.singleton α).join}
    (hl : ρ'.get l = some (CellU.immOf (LSet.singleton α) v χ hχ))
    (hown : ρ.get l = some (CellU.ownOf v)) : ResU.Le χ ρ := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompS ψ₁ ψ₂ ψ → CellU.CompatS ψ₁ ψ₂ :=
    fun _ _ _ hc => CellU.CompS.compat hc
  obtain ⟨-, π, b, hdom, hbig, hle, hat⟩ := h
  obtain ⟨⟨l', p⟩, hpm, hl'⟩ := List.mem_map.mp ((hdom.2 l).mpr ⟨_, hl⟩)
  rw [show l' = l from hl'] at hpm
  obtain ⟨⟨ζ, hζ⟩, hownc, -, -⟩ := hat l p hpm
  obtain ⟨h', he⟩ := hownc v hown
  rw [hl] at he
  obtain ⟨-, -, hχe⟩ := CellU.immOf_inj (Option.some.inj he)
  obtain ⟨z, hz⟩ :=
    BigComp.mem_factor hR ResU.compLawsS hbig p (List.mem_map.mpr ⟨(l, p), hpm, rfl⟩)
  obtain ⟨τ, hτ⟩ := hle
  obtain ⟨z₁, hz₁⟩ := ResU.Comp.factor_trans hR ResU.compLawsS (ResU.del_compS hζ) hz
  obtain ⟨z₂, hz₂⟩ := ResU.Comp.factor_trans hR ResU.compLawsS hz₁ hτ
  exact ⟨z₂, by rw [hχe]; exact hz₂⟩

/-- **Anything `⦇ρ′ᵢ⦈_○` already raises is absorbed by `ag(ρᵢ)`.**  `ag(ρᵢ)` is
`ρᵢ ○ ⦇ρ′ᵢ⦈_○` (`AgW.single_imm_inv`), so a `○`-factor of `⦇ρ′ᵢ⦈_○` composes
onto it and changes nothing.

This is the chain step `ResU.reb_flatR_absorb` runs on, stated on its own.  That
lemma's `iff` form places a factor inside `ag(ρ_reb) ○ ag(ρᵢ)`, where at a
reborrowed `ℓ` the `imm({β}, …)` absorbs it and nothing about the factor
survives; this form keeps the factor.  `[TR]` 6.59's *"both get the borrow from
`ρᵢ`"* is spent through it at the ancestor's raised subtree.
`[about ours: `ResU.reb_flatR_absorb`'s chain step, exposed as a factor]` -/
theorem ResU.absorbed_of_factor_flatR {ρ'i a₂ : ResU Loc Val}
    {l₀ : Loc} {s : LSet} {v : Val} {hs : ρ'i.InStratum s.join}
    (ha₂ : AgW (ResU.single l₀ (CellU.immOf s v ρ'i hs)) a₂)
    {es as pS : ResU Loc Val} (hexS : ExR ρ'i es) (hagS : AgW ρ'i as)
    (hfS : ResU.CompR es as pS)
    {Y : ResU Loc Val} (hY : ResU.LeR Y pS) : ResU.LeR Y a₂ := by
  classical
  obtain ⟨es', as', pS', hexS', hagS', hfS', hagi⟩ := AgW.single_imm_inv ha₂
  cases ExR.functional hexS' hexS
  cases AgW.functional hagS' hagS
  cases ResU.CompR.functional hfS' hfS
  obtain ⟨z, hz⟩ := hY
  exact ResU.Comp.factor_trans (fun _ _ ψ hc => ⟨ψ, hc⟩) ResU.compLawsR hz
    (ResU.CompR.comm hagi)

/-- **A `ρ_reb` cell's raised witness is absorbed by `ag(ρᵢ)`.**  This is the
second attribution branch of `[TR]` 6.59's closing step: where the `imm` cell
that `↭` pins at the ancestor belongs to `ag(ρ_reb)` rather than to `ag(R)`,
the subtree it raises is `ρ′ᵢ`'s own and so stands in `ag(ρᵢ)`, which is on
**both** sides of the goal.  So the attribution does not have to choose.

`reb_α` pins each half: at a `mut` source cell the witness is the cell's own
payload (`ExW.wit_le`, `AgW.mut_wit_le`), and at an `own` source cell it is
`π(ℓ)/ℓ`, a `●`-factor of the source (`ResU.reb_own_wit_le`), which
`ExR.split_of_compS` and `AgW.split` carry into the two walks.  Each half is
then a `○`-factor of `⦇ρ′ᵢ⦈_○`, and `ResU.absorbed_of_factor_flatR` closes it.
`[about ours: `ResU.reb_flatR_absorb`'s `imm`-family step, at one cell]` -/
theorem ResU.reb_wit_absorbs {β : Life} {ρ'i ρ a₂ : ResU Loc Val}
    {l₀ : Loc} {s : LSet} {v : Val} {hs : ρ'i.InStratum s.join}
    (hreb : ResU.Reb β ρ'i ρ)
    (ha₂ : AgW (ResU.single l₀ (CellU.immOf s v ρ'i hs)) a₂)
    {es as pS : ResU Loc Val} (hexS : ExR ρ'i es) (hagS : AgW ρ'i as)
    (hfS : ResU.CompR es as pS)
    {q : Loc} {ψq : CellU Loc Val}
    (hψq : (ρ.restrictDom ρ'i.exclPart).get q = some ψq)
    {evq avq p : ResU Loc Val}
    (hexq : ExR ψq.wit evq) (hagq : AgW ψq.wit avq)
    (hcq : ResU.CompR evq avq p) :
    ResU.LeR p a₂ := by
  classical
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  have hfacEx : ∀ Y : ResU Loc Val, ResU.LeR Y es → ResU.LeR Y a₂ := fun Y hY =>
    ResU.absorbed_of_factor_flatR ha₂ hexS hagS hfS (hY.trans (ResU.LeR.left hfS))
  have hfacAg : ∀ Y : ResU Loc Val, ResU.LeR Y as → ResU.LeR Y a₂ := fun Y hY =>
    ResU.absorbed_of_factor_flatR ha₂ hexS hagS hfS (hY.trans (ResU.LeR.right hfS))
  have hρq : ρ.get q = some ψq := ResU.restrictDom_get_inv hψq
  obtain ⟨φ', hφ'⟩ := ResU.restrictDom_dom hψq
  obtain ⟨hφ'g, hφ'k⟩ := ResU.exclPart_eq_some.mp hφ'
  obtain ⟨vv, χw, hχs, hψeq, hev, hor⟩ := ResU.reb_src hreb hρq hφ'g hφ'k
  have hwit : ψq.wit = χw := by rw [hψeq]; exact CellU.wit_immOf _ _ _ _
  rw [hwit] at hexq hagq
  have hEx : ∃ z, ResU.CompR evq z es := by
    by_cases hk : φ'.kind = Kind.own
    · rcases CellU.rep φ' with ⟨w, hw⟩ | ⟨s', w, ξ, hξ, hw⟩ | ⟨b', w, ξ, hξ, P, hP, hw⟩
      · obtain ⟨z, hz⟩ := ResU.reb_own_wit_le hreb (hψeq ▸ hρq)
          (by rw [hφ'g, hw, show w = vv from by rw [← hev, hw]; rfl])
        obtain ⟨e₁, e₂, he₁, he₂, hec⟩ := (ExR.split_of_compS hz).mp hexS
        rw [show e₁ = evq from ExR.functional he₁ hexq] at hec
        exact ⟨e₂, hec⟩
      · exact absurd (by rw [hw]; rfl) hφ'k
      · exact absurd (by rw [hw]; rfl : φ'.kind = Kind.mut)
          (by rw [hk]; exact fun e => Kind.noConfusion e)
    · have hkm : φ'.kind = Kind.mut := by
        rcases CellU.rep φ' with ⟨w, hw⟩ | ⟨s', w, ξ, hξ, hw⟩ | ⟨b', w, ξ, hξ, P, hP, hw⟩
        · exact absurd (by rw [hw]; rfl) hk
        · exact absurd (by rw [hw]; rfl) hφ'k
        · rw [hw]; rfl
      have hwφ : φ'.wit = χw := hor.resolve_left hk
      obtain ⟨ev, z, hev', hz⟩ := ExW.wit_le hR ResU.compLawsR hexS hφ'g hkm
      rw [hwφ] at hev'
      rw [show ev = evq from ExR.functional hev' hexq] at hz
      exact ⟨z, hz⟩
  have hAg : ∃ z, ResU.CompR avq z as := by
    by_cases hk : φ'.kind = Kind.own
    · rcases CellU.rep φ' with ⟨w, hw⟩ | ⟨s', w, ξ, hξ, hw⟩ | ⟨b', w, ξ, hξ, P, hP, hw⟩
      · obtain ⟨z, hz⟩ := ResU.reb_own_wit_le hreb (hψeq ▸ hρq)
          (by rw [hφ'g, hw, show w = vv from by rw [← hev, hw]; rfl])
        obtain ⟨a', a'', ha', ha'', hac⟩ := (AgW.split hz).mp hagS
        rw [show a' = avq from AgW.functional ha' hagq] at hac
        exact ⟨a'', hac⟩
      · exact absurd (by rw [hw]; rfl) hφ'k
      · exact absurd (by rw [hw]; rfl : φ'.kind = Kind.mut)
          (by rw [hk]; exact fun e => Kind.noConfusion e)
    · have hkm : φ'.kind = Kind.mut := by
        rcases CellU.rep φ' with ⟨w, hw⟩ | ⟨s', w, ξ, hξ, hw⟩ | ⟨b', w, ξ, hξ, P, hP, hw⟩
        · exact absurd (by rw [hw]; rfl) hk
        · exact absurd (by rw [hw]; rfl) hφ'k
        · rw [hw]; rfl
      have hwφ : φ'.wit = χw := hor.resolve_left hk
      obtain ⟨av, z, hav', hz⟩ := AgW.mut_wit_le hagS hφ'g hkm
      rw [hwφ] at hav'
      rw [show av = avq from AgW.functional hav' hagq] at hz
      exact ⟨z, hz⟩
  exact ⟨a₂, ResU.CompR.absorb_comp hcq (hfacEx evq hEx).absorb (hfacAg avq hAg).absorb⟩

/-- **`ag(ρ_reb)` splits as `ρ_reb ○ (something `ag(ρᵢ)` absorbs)`.**  `ρ_reb`
carries `imm` cells only, so its `mut` family is empty and its walk is its own
cells composed with the `imm` family; every entry of that family is a witness
`reb_α` read off `ρ′ᵢ`, so `ResU.reb_wit_absorbs` absorbs each, and
`BigComp.absorb` absorbs the fold.

This is what an ancestor in the **walk** needs that `ResU.reb_wit_absorbs` does
not give on its own: an `imm` cell of `ag(ρ_reb)` need not be one of `ρ_reb`'s
own cells — it can be raised — and this splits the walk so that either case is
covered.
`[about ours: `ResU.reb_flatR_absorb`'s decomposition of `ag(ρ_reb)`]` -/
theorem ResU.reb_ag_split {β : Life} {ρ'i ρ areb a₂ : ResU Loc Val}
    {l₀ : Loc} {s : LSet} {v : Val} {hs : ρ'i.InStratum s.join}
    (hreb : ResU.Reb β ρ'i ρ)
    (hareb : AgW (ρ.restrictDom ρ'i.exclPart) areb)
    (ha₂ : AgW (ResU.single l₀ (CellU.immOf s v ρ'i hs)) a₂)
    {es as pS : ResU Loc Val} (hexS : ExR ρ'i es) (hagS : AgW ρ'i as)
    (hfS : ResU.CompR es as pS) :
    ∃ bi, ResU.CompR (ρ.restrictDom ρ'i.exclPart) bi areb ∧
      ResU.LeR bi a₂ := by
  classical
  have himmR : ∀ m ψ, (ρ.restrictDom ρ'i.exclPart).get m = some ψ →
      ψ.kind = Kind.imm :=
    fun m ψ hψ => ResU.reb_imm_image hreb (ResU.restrictDom_get_inv hψ)
  cases hareb with
  | mk hsm hsi hwm hwi hbm hbi ha hσ =>
      rename_i aa bm bi wm wi
      obtain rfl : wm = [] := by
        have hnil : wm.map Prod.fst = [] :=
          ResU.sites_nil_of_none hsm (fun m ψ hψ => by
            rw [himmR m ψ hψ]; exact fun e => Kind.noConfusion e)
        cases wm with
        | nil => rfl
        | cons q t => simp at hnil
      obtain rfl : bm = (PMap.empty : ResU Loc Val) := BigComp.nil_inv hbm
      have hrestr : (ρ.restrictDom ρ'i.exclPart).restrict Kind.imm
          = ρ.restrictDom ρ'i.exclPart := by
        refine PMap.ext fun m => ?_
        cases e : (ρ.restrictDom ρ'i.exclPart).get m with
        | none => exact ResU.restrict_get_none e
        | some ψ => exact ResU.restrict_get_some e (himmR m ψ e)
      obtain rfl : aa = ρ.restrictDom ρ'i.exclPart := by
        rw [← hrestr]
        exact (ResU.CompR.functional ha (ResU.comp_empty_right _))
      refine ⟨bi, hσ, a₂, BigComp.absorb hbi (fun τ hm => ?_)⟩
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
      obtain ⟨ψq, evq, avq, hψq, hexq, hagq, hcq⟩ := AgWitsI.mem hwi q hq
      exact (ResU.reb_wit_absorbs hreb ha₂ hexS hagS hfS hψq hexq hagq hcq).absorb

end BoCa.Fig16

namespace BoCa.Fig16

/-- `⊓ᾱ ⊐ β` says `β` is strictly shorter than the shortest member of `ᾱ`, so
`β` is not a member.  `⊓ᾱ` is `LSet.meet` and `LSet.meet_least` is the row that
says it is least. -/
theorem LSet.notMem_of_meet_sqsupset {s : LSet} {b : Life} (h : s.meet ⊐ b) :
    ¬ s.mem b := fun hb => absurd (s.meet_least b hb) (by exact not_le.mpr h)

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- The same read off a cell: a component that outlives `β` carries no borrow at
`β`.  `CellU.inStratum_immOf` is `@imm(ᾱ, v, ρ) = ⊓ᾱ`. -/
theorem CellU.notMem_of_inStratum {Loc Val : Type} {s : LSet} {v : Val}
    {χ : ResU Loc Val} {h : χ.InStratum s.join} {b : Life}
    (hc : (CellU.immOf s v χ h).InStratum b) : ¬ s.mem b :=
  LSet.notMem_of_meet_sqsupset hc

end BoCa.Fig16

namespace BoCa.Fig16

/-- …and the mixed case cannot arise: `{β}` alone is never `ᾱ ∪ {β}` for an `ᾱ`
that misses `β`, because a lifetime set is **nonempty** — `℘⁺`, carried by
`LSet.join_mem` — so `ᾱ` contributes a member `{β}` does not have.  This is what
rules out one side contributing an `imm` at `ℓ` and the other contributing
nothing or a cell that `ρ_reb`'s `imm` absorbs. -/
theorem LSet.union_singleton_ne_singleton {s : LSet} {b : Life} (hs : ¬ s.mem b) :
    s ∪ LSet.singleton b ≠ LSet.singleton b := by
  intro h
  have hj : (s ∪ LSet.singleton b).mem s.join := Or.inl s.join_mem
  rw [h] at hj
  exact hs ((hj : s.join = b) ▸ s.join_mem)

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- `x ○ imm({β}, v, χ)` at an `imm` cell `x`: the value and the witness are
forced to agree and the sets union.  `β` is not in the left set, because the
component it comes from outlives `β` — which is the closing sentence's first
clause, at one cell. -/
theorem CellU.compR_immBeta_imm {β : Life} {v : Val} {χ : ResU Loc Val}
    {hχ : χ.InStratum (LSet.singleton β).join} {a x : CellU Loc Val}
    (h : CellU.CompR a (CellU.immOf (LSet.singleton β) v χ hχ) x)
    (ho : a.InStratum β) (hak : a.kind = Kind.imm) :
    ∃ (s : LSet) (hs : χ.InStratum s.join) (hu : χ.InStratum (s ∪ LSet.singleton β).join),
      a = CellU.immOf s v χ hs ∧ x = CellU.immOf (s ∪ LSet.singleton β) v χ hu ∧
        ¬ s.mem β := by
  rcases CellU.CompR.inv h with ⟨e, -⟩ | ⟨k, ex⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, -, e₂, -⟩ | ⟨-, hk2, -⟩ | ⟨-, hk1, -⟩ |
      ⟨-, -, hk2⟩ | ⟨-, hk1, -⟩
  · rw [e] at ho
    exact absurd ((CellU.inStratum_immOf β _ v χ hχ).mp ho) (lt_irrefl _)
  · have hcs : CellU.CompS a (CellU.immOf (LSet.singleton β) v χ hχ) x :=
      ex ▸ CellU.compS_spec _ _ k
    obtain ⟨s₁, s₂, u, τ, k₁, k₂, k₃, f₁, f₂, f₃⟩ := hcs
    obtain ⟨hs2, hu2, hτ2⟩ := CellU.immOf_inj f₂
    subst hs2
    subst hu2
    subst hτ2
    refine ⟨s₁, k₁, k₃, f₁, f₃, ?_⟩
    rw [f₁] at ho
    exact LSet.notMem_of_meet_sqsupset ((CellU.inStratum_immOf β s₁ v χ k₁).mp ho)
  · exact absurd e₂ CellU.immOf_ne_mutOf
  · simp at hk2
  · rw [hak] at hk1; simp at hk1
  · simp at hk2
  · rw [hak] at hk1; simp at hk1

/-- **A component that contributes an `imm` at a reborrowed location is visible
through `ρ_reb`'s borrow.**  Its set is `ᾱ ∪ {β}`, and `ᾱ` is non-empty (`℘⁺`)
and misses `β`, so the composite is never `ρ_reb`'s cell alone.  This is what
rules out one side contributing an `imm` at `ℓ` where the other is silent or
contributes a cell the `{β}` borrow absorbs. -/
theorem CellU.reb_frame_imm_ne_singleton {β : Life} {v : Val} {χ : ResU Loc Val}
    {hχ : χ.InStratum (LSet.singleton β).join} {a x : CellU Loc Val}
    (h : CellU.CompR a (CellU.immOf (LSet.singleton β) v χ hχ) x)
    (ho : a.InStratum β) (hak : a.kind = Kind.imm) :
    x ≠ CellU.immOf (LSet.singleton β) v χ hχ := by
  obtain ⟨s, hs, hu, -, ex, hβs⟩ := CellU.compR_immBeta_imm h ho hak
  intro e
  rw [ex] at e
  exact LSet.union_singleton_ne_singleton hβs (CellU.immOf_inj e).1

/-- **Where `ag(ρ)` stands, `ex(ρ)_●` does not.**  `●` relates `imm` cells only,
and an `imm`-free exclusive walk has none to offer.
`[about ours: the disjointness of a flattening's two walks]` -/
theorem ResU.ex_none_of_ag_some {e a σ : ResU Loc Val}
    (himm : e.ImmFree) (hc : ResU.CompS e a σ)
    {l : Loc} {c : CellU Loc Val} (hg : a.get l = some c) :
    e.get l = none := by
  rcases ResU.CompatS.disjoint_of_immFree himm hc.1 l with h | h
  · exact h
  · rw [hg] at h; exact absurd h (by simp)

/-- **A flattening is its aliasable walk where that walk stands.**
`ResU.flat_eq_ag_at` reads this off a non-`imm` cell; this takes the same step
from the `imm`-freeness of `ex(ρ)_●` instead, so it holds at an `imm` cell too.
`[about ours: `ResU.flat_eq_ag_at` without its kind hypothesis]` -/
theorem ResU.flat_eq_ag_of_immFree {e a σ : ResU Loc Val}
    (himm : e.ImmFree) (hc : ResU.CompS e a σ)
    {l : Loc} {c : CellU Loc Val} (hg : a.get l = some c) :
    σ.get l = some c := by
  have hn := ResU.ex_none_of_ag_some himm hc hg
  rcases ResU.Comp.get hc l with ⟨-, f₂, -⟩ | ⟨ψ, f₁, -, -⟩ | ⟨ψ, -, f₂, f⟩ |
      ⟨ψ₁, ψ₂, ψ, f₁, -, -, -⟩
  · rw [hg] at f₂; exact absurd f₂ (by simp)
  · rw [hn] at f₁; exact absurd f₁ (by simp)
  · rw [f, show ψ = c from Option.some.inj (f₂.symm.trans hg)]
  · rw [hn] at f₁; exact absurd f₁ (by simp)

/-- **An `imm`-only resource has an empty exclusive walk.**  `ex(ρ)_◐` composes
`ρ|own`, `ρ|mut` and the walks of `ρ`'s `mut` witnesses, and an `imm`-only `ρ`
has none of the three.

Both `ρ_reb` and `ρᵢ` are `imm`-only — `ρ_reb` by `ResU.reb_imm_image`, `ρᵢ`
because it is one `imm` cell — so `ex(L ● ρ_reb)_●` and `ex(L ● ρᵢ)_●` are both
`ex(L)_●`.  The swap therefore moves nothing in the exclusive walk, and
the whole of `[TR]` 6.59's closing sentence lives in the aliasable one.
`[about ours: `ex(−)_◐` at a resource carrying `imm` cells only]` -/
theorem ExW.eq_empty_of_immOnly {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    {ρ : ResU Loc Val}
    (h : ∀ l ψ, ρ.get l = some ψ → ψ.kind = Kind.imm) :
    ExW R C ρ (PMap.empty : ResU Loc Val) := by
  have hr : ∀ k : Kind, k ≠ Kind.imm → ρ.restrict k = (PMap.empty : ResU Loc Val) := by
    intro k hk
    refine PMap.ext fun l => ?_
    show (ρ.get l).bind (fun ψ => if ψ.kind = k then some ψ else none) = _
    cases e : ρ.get l with
    | none => simp [PMap.empty_get]
    | some ψ =>
        have hne : ψ.kind ≠ k := by rw [h l ψ e]; exact fun c => hk c.symm
        simp [hne, PMap.empty_get]
  refine ExW.mk (w := []) (b := PMap.empty) (nm := PMap.empty)
    ⟨List.nodup_nil, fun l => ?_⟩ ExWits.nil BigComp.nil ?_ ?_
  · refine ⟨fun hl => absurd hl (by simp), ?_⟩
    rintro ⟨ψ, hg, hk⟩
    rw [h l ψ hg] at hk
    exact absurd hk (by simp)
  · rw [hr Kind.own (by simp), hr Kind.mut (by simp)]
    exact ResU.comp_empty_right _
  · exact ResU.comp_empty_right _

/-- **Swapping one `imm`-only factor for another leaves the exclusive walk
alone.**  Each factor's own exclusive walk is empty
(`ExW.eq_empty_of_immOnly`), so 6.18's split leaves `ex(L)_●` on both sides.

At `[TR]` 6.59 the two factors are `ρ_reb` and `ρᵢ`, both `imm`-only —
`ResU.reb_imm_image` and one `imm` cell — so the closing sentence's swap is
entirely a statement about the **aliasable** walk.
`[about ours: `ExS.split` at an `imm`-only factor]` -/
theorem ResU.ex_eq_of_swap_immOnly {L F G Lf Lg eF eG : ResU Loc Val}
    (hF : ∀ l ψ, F.get l = some ψ → ψ.kind = Kind.imm)
    (hG : ∀ l ψ, G.get l = some ψ → ψ.kind = Kind.imm)
    (hLf : ResU.CompS L F Lf) (hLg : ResU.CompS L G Lg)
    (heF : ExS Lf eF) (heG : ExS Lg eG) : eF = eG := by
  obtain ⟨e₁, e₂, he₁, he₂, hec⟩ := (ExS.split hLf).mp heF
  obtain ⟨d₁, d₂, hd₁, hd₂, hdc⟩ := (ExS.split hLg).mp heG
  cases ExS.functional he₂ (ExW.eq_empty_of_immOnly hF)
  cases ExS.functional hd₂ (ExW.eq_empty_of_immOnly hG)
  cases ExS.functional hd₁ he₁
  exact (ResU.CompS.functional hec (ResU.comp_empty_right _)).trans
    (ResU.CompS.functional (ResU.comp_empty_right _) hdc)

/-- **`ρ|dom(ρ′ᵢ|imm)` outlives `β`.**  `[TR]` 6.59's closing sentence says
*all* components besides `ρ_reb` outlive `β`, and the printed hypotheses name
only `ρ_b` and `ρ′`, with 6.52 supplying `ρ⁺ ⊟ ρ_reb`.  Those are three.
The fourth — the `imm`-part of `ρ`, a factor of the print's left side — is
named by the sentence and by no hypothesis, and it is **derived**: at an `imm`
source cell the image cell is `imm` over a subset of its lifetime set and so in
every stratum the source cell is (`ResU.reb_imm_cell_kw`), and `reb_α`'s own
first conjunct puts the source in the stratum.
`[about ours: the component of `[TR]` 6.59's left side that no printed
hypothesis mentions]` -/
theorem ResU.reb_immPart_inStratum {α : Life} {ρ' ρ : ResU Loc Val}
    (h : ResU.Reb α ρ' ρ) :
    (ρ.restrictDom (ρ'.restrict Kind.imm)).InStratum α := by
  intro l ψ hg
  have himg : ρ.get l = some ψ := ResU.restrictDom_get_inv hg
  cases e : (ρ'.restrict Kind.imm).get l with
  | none => rw [ResU.restrictDom_get_of_none e] at hg; exact absurd hg (by simp)
  | some φ =>
      obtain ⟨hsrc, hk⟩ := ResU.restrict_eq_some.mp e
      exact (ResU.reb_imm_cell_kw h himg hsrc hk).2.2.2 _ (h.1 l φ hsrc)

/-- **Attribution, where the ancestor is `R`'s own.**  If the `imm` cell that
`↭` pins at `m` is already an `imm` cell of `ag(R)`, then `⦇κ⦈_○` is a
`○`-factor of `ag(R)` (`AgW.flat_imm_wit_le`) and so of `ag(R) ○ ag(ρᵢ)` — the
goal's side — with no appeal to the reborrow at all.

`ResU.CompR.imm_source` is what makes this a **case split rather than a
guess**: an `imm` cell of a `○` comes from one of the operands, over the same
value and the same witness.  The other branch, where the cell is `ag(ρ_reb)`'s,
is `ResU.reb_flatR_absorb`'s.
`[about ours: the attribution branch of `[TR]` 6.59 where `ag(R)` carries the
ancestor]` -/
theorem ResU.reb_attribute_of_side {R aR ai aRi : ResU Loc Val}
    (haR : AgW R aR) (hRi : ResU.CompR aR ai aRi)
    {m : Loc} {t : LSet} {u : Val} {κ : ResU Loc Val} {hh : κ.InStratum t.join}
    (hm : aR.get m = some (CellU.immOf t u κ hh)) :
    ∃ ev av p z, ExR κ ev ∧ AgW κ av ∧ ResU.CompR ev av p ∧ ResU.CompR p z aRi := by
  obtain ⟨ev, av, p, z, hev, hav, hp, hz⟩ := AgW.flat_imm_wit_le haR m t u κ hh hm
  obtain ⟨x, -, hx⟩ := (ResU.CompR.assoc p z ai aRi).mpr ⟨aR, hz, hRi⟩
  exact ⟨ev, av, p, x, hev, hav, hp, hx⟩

/-- **The attribution, all three branches, to one conclusion.**  `↭` pins an
`imm` cell at the ancestor `m` of `ag(R ● ρ_reb)`, and `ResU.CompR.imm_source`
resolves where it comes from — over the same value and witness `κ` each time.
Either way `⦇κ⦈_○` is a `○`-factor of the **goal's** side `ag(R) ○ ag(ρᵢ)`:

* from `ag(R)` — `ResU.reb_attribute_of_side`, no appeal to the reborrow;
* from `ρ_reb`'s own cell — `ResU.reb_wit_absorbs`: the witness is `ρ′ᵢ`'s;
* from the raised family inside `ag(ρ_reb)` (`ResU.reb_ag_split`) — that family
  absorbs `ag(ρᵢ)`, so `ag(ρᵢ)` carries the same `imm` cell at `m` and
  `AgW.flat_imm_wit_le` places the subtree there.  This branch does **not**
  descend into the family, which is what keeps the argument finite.

So the attribution never has to choose: all three land in the same place, and
`ρᵢ` is on both sides of the goal.
`[about ours: `[TR]` 6.59's attribution, assembled]` -/
theorem ResU.reb_attribute {β : Life} {ρ'i ρ R aR areb a₂ aRreb aRi : ResU Loc Val}
    {l₀ : Loc} {s : LSet} {v : Val} {hs : ρ'i.InStratum s.join}
    (hreb : ResU.Reb β ρ'i ρ)
    (haR : AgW R aR)
    (hareb : AgW (ρ.restrictDom ρ'i.exclPart) areb)
    (ha₂ : AgW (ResU.single l₀ (CellU.immOf s v ρ'i hs)) a₂)
    {es as pS : ResU Loc Val} (hexS : ExR ρ'i es) (hagS : AgW ρ'i as)
    (hfS : ResU.CompR es as pS)
    (hRreb : ResU.CompR aR areb aRreb) (hRi : ResU.CompR aR a₂ aRi)
    {m : Loc} {t : LSet} {u : Val} {κ : ResU Loc Val} {hh : κ.InStratum t.join}
    (hm : aRreb.get m = some (CellU.immOf t u κ hh)) :
    ∃ ev av p z, ExR κ ev ∧ AgW κ av ∧ ResU.CompR ev av p ∧
      ResU.CompR p z aRi := by
  classical
  have hRc : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  have hofAbs : ∀ {q : ResU Loc Val}, ResU.CompR q a₂ a₂ →
      ∃ z, ResU.CompR q z aRi := by
    intro q habs
    obtain ⟨y, hy₁, hy₂⟩ := (ResU.CompR.assoc aR q a₂ aRi).mp ⟨a₂, habs, hRi⟩
    exact ResU.Comp.factor_trans hRc ResU.compLawsR (ResU.CompR.comm hy₁) hy₂
  rcases ResU.CompR.imm_source hRreb hm with ⟨t₁, h₁, hin⟩ | ⟨t₂, h₂, hin⟩
  · exact ResU.reb_attribute_of_side haR hRi hin
  · obtain ⟨bi, hσ, hbiabs⟩ := ResU.reb_ag_split hreb hareb ha₂ hexS hagS hfS
    obtain ⟨ev, av, p, -, hev, hav, hp, -⟩ :=
      AgW.flat_imm_wit_le hareb m t₂ u κ h₂ hin
    have habs : ResU.LeR p a₂ := by
      rcases ResU.CompR.imm_source hσ hin with ⟨t₃, h₃, hown⟩ | ⟨t₄, h₄, hbi⟩
      · refine ResU.reb_wit_absorbs hreb ha₂ hexS hagS hfS hown ?_ ?_ hp
        · rw [show (CellU.immOf t₃ u κ h₃).wit = κ from CellU.wit_immOf _ _ _ _]
          exact hev
        · rw [show (CellU.immOf t₃ u κ h₃).wit = κ from CellU.wit_immOf _ _ _ _]
          exact hav
      · obtain ⟨t₅, h₅, ha₂m⟩ := ResU.CompR.imm_left_get hbiabs.absorb hbi
        obtain ⟨ev', av', p', z', hev', hav', hp', hz'⟩ :=
          AgW.flat_imm_wit_le ha₂ m t₅ u κ h₅ ha₂m
        cases ExR.functional hev' hev
        cases AgW.functional hav' hav
        cases ResU.CompR.functional hp' hp
        exact ⟨_, hz'⟩
    obtain ⟨z, hz⟩ := hofAbs habs.absorb
    exact ⟨ev, av, p, z, hev, hav, hp, hz⟩

/-- **Off `dom(ρ_reb)`, `ag(ρ_reb)`'s cell is absorbed by `ag(ρᵢ)`'s** — and
without `ρ # ρᵢ`.

`ResU.reb_ag_absorbed_off_dom` reads `ResU.reb_flatR_absorb`'s `iff`, so it
needs the composite `ag(ρ_reb) ○ ag(ρᵢ)` to exist before it can say anything;
that is `✓(ρ ● ρᵢ)`, which is 6.55's corollary and is carried here only under a
restriction.  `ResU.reb_ag_split` needs no composite: `ag(ρ_reb)` **is**
`ρ_reb ○ bi` with `bi ≼ ag(ρᵢ)`, so off `ρ_reb`'s own domain the walk's cell is
`bi`'s, and `≼` absorbs it.
`[about ours: `ResU.reb_ag_absorbed_off_dom` without the `#` it was waiting
on]` -/
theorem ResU.reb_ag_cell_absorbed_off_dom {β : Life} {ρ'i ρ areb a₂ : ResU Loc Val}
    {l₀ : Loc} {s : LSet} {v : Val} {hs : ρ'i.InStratum s.join}
    (hreb : ResU.Reb β ρ'i ρ)
    (hareb : AgW (ρ.restrictDom ρ'i.exclPart) areb)
    (ha₂ : AgW (ResU.single l₀ (CellU.immOf s v ρ'i hs)) a₂)
    {es as pS : ResU Loc Val} (hexS : ExR ρ'i es) (hagS : AgW ρ'i as)
    (hfS : ResU.CompR es as pS)
    {m : Loc} (hm : (ρ.restrictDom ρ'i.exclPart).get m = none)
    {ψ : CellU Loc Val} (hψ : areb.get m = some ψ) :
    ∃ φ, a₂.get m = some φ ∧ CellU.CompR ψ φ φ := by
  obtain ⟨bi, hσ, hbile⟩ := ResU.reb_ag_split hreb hareb ha₂ hexS hagS hfS
  -- off `ρ_reb`'s own domain the walk's cell is `bi`'s
  have hbim : bi.get m = some ψ := by
    rcases ResU.Comp.get hσ m with ⟨-, f₂, f⟩ | ⟨ξ, f₁, -, -⟩ | ⟨ξ, -, f₂, f⟩ |
        ⟨ξ₁, ξ₂, ξ, f₁, -, -, -⟩
    · rw [f] at hψ; exact absurd hψ (by simp)
    · rw [hm] at f₁; exact absurd f₁ (by simp)
    · exact f₂.trans (congrArg some (Option.some.inj (f.symm.trans hψ)))
    · rw [hm] at f₁; exact absurd f₁ (by simp)
  -- and `≼` absorbs it
  rcases ResU.Comp.get hbile.absorb m with ⟨f₁, -, -⟩ | ⟨ξ, -, f₂, f⟩ |
      ⟨ξ, f₁, -, -⟩ | ⟨ξ₁, ξ₂, ξ, f₁, f₂, f, hC⟩
  · rw [hbim] at f₁; exact absurd f₁ (by simp)
  · rw [f] at f₂; exact absurd f₂.symm (by simp)
  · rw [hbim] at f₁; exact absurd f₁ (by simp)
  · refine ⟨ξ₂, f₂, ?_⟩
    obtain rfl : ξ₁ = ψ := Option.some.inj (f₁.symm.trans hbim)
    obtain rfl : ξ = ξ₂ := Option.some.inj (f.symm.trans f₂)
    exact hC

/-- **`○` at two `imm` cells: one value, one witness, the union of the sets.**
Clauses (1) and (2) are the only ones with two `imm` operands, and both return
an `imm` cell over the operands' common value and common witness.  The value is
`CellU.CompR.erase`, the witness is `CellU.CompR.wit`, and the set is
`CellU.CompR.imm_union`.

This is what lets a hypothesis about composites containing `ρ_reb` speak about
composites containing `ρᵢ`: at an ancestor the two differ in the lifetime set
and in nothing else, and `AgW.flat_imm_wit_le` keys the raised subtree on the
witness alone.  `CellU.CompR.imm_left_eq` is the same fact with the second
operand left free.
`[about ours: `[TR]` p. 5's `○` at two `imm` cells, read off the relation]` -/
theorem CellU.CompR.imm_imm_union {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompR ψ₁ ψ₂ ψ)
    (k₁ : ψ₁.kind = Kind.imm) (k₂ : ψ₂.kind = Kind.imm) :
    ∃ (a b : LSet) (u : Val) (χ : ResU Loc Val)
      (ha : χ.InStratum a.join) (hb : χ.InStratum b.join)
      (hu : χ.InStratum (a ∪ b).join),
      ψ₁ = CellU.immOf a u χ ha ∧ ψ₂ = CellU.immOf b u χ hb ∧
        ψ = CellU.immOf (a ∪ b) u χ hu := by
  obtain ⟨a, ha, e₁⟩ := CellU.imm_eta k₁
  obtain ⟨b, hb, e₂⟩ := CellU.imm_eta k₂
  have hv : ψ₁.erase = ψ₂.erase := (CellU.CompR.erase h).1
  have hw : ψ₁.wit = ψ₂.wit :=
    CellU.CompR.wit h (by rw [k₁]; simp) (by rw [k₂]; simp)
  have hb' : ψ₁.wit.InStratum b.join := by rw [hw]; exact hb
  have e₂' : ψ₂ = CellU.immOf b ψ₁.erase ψ₁.wit hb' :=
    e₂.trans (CellU.immOf_congr rfl hv.symm hw.symm hb hb')
  obtain ⟨hu, e⟩ := CellU.CompR.imm_union h e₁ e₂'
  exact ⟨a, b, ψ₁.erase, ψ₁.wit, ha, hb', hu, e₁, e₂', e⟩

/-- …and absorption is transitive, which is what carries an ancestor's cell down
a chain of walks. -/
theorem CellU.CompR.absorb_transC {X Y Z : CellU Loc Val}
    (h₁ : CellU.CompR X Y Y) (h₂ : CellU.CompR Y Z Z) : CellU.CompR X Z Z := by
  obtain ⟨w, hw, hx⟩ := (CellU.compR_assoc X Y Z Z).mpr ⟨Y, h₁, h₂⟩
  rwa [CellU.CompR.functional hw h₂] at hx

/-- **Absorption is pointwise.**  `ρ ○ σ = σ` is a statement at each location
and nothing more: `▷◁` is the cellwise composability that the cellwise
absorption already witnesses.
`[about ours: `ResU.CompR` at a resource absorbed cell by cell]` -/
theorem ResU.compR_absorb_of_cells {X W : ResU Loc Val}
    (h : ∀ n ψ, X.get n = some ψ → ∃ φ, W.get n = some φ ∧ CellU.CompR ψ φ φ) :
    ResU.CompR X W W := by
  refine ⟨fun l ψ₁ ψ₂ e₁ e₂ => ?_, fun l => ?_⟩
  · obtain ⟨φ, hφ, hc⟩ := h l ψ₁ e₁
    rw [hφ] at e₂
    obtain rfl : φ = ψ₂ := Option.some.inj e₂
    exact ⟨φ, hc⟩
  · show OptComp CellU.CompR (X.get l) (W.get l) (W.get l)
    cases e : X.get l with
    | none =>
        cases f : W.get l with
        | none => rfl
        | some φ => rfl
    | some ψ =>
        obtain ⟨φ, hφ, hc⟩ := h l ψ e
        rw [hφ]
        exact ⟨φ, rfl, hc⟩

/-- **`≼` read at one location.**  Where the smaller resource stands, so does
the larger, and the larger's cell absorbs the smaller's.
`[about ours: `ResU.LeR` at one location]` -/
theorem ResU.LeR.get_some {τ σ : ResU Loc Val} (h : ResU.LeR τ σ) {m : Loc}
    {ψ : CellU Loc Val} (hg : τ.get m = some ψ) :
    ∃ χ, σ.get m = some χ ∧ CellU.CompR ψ χ χ := by
  have habs := h.absorb.2 m
  rw [hg] at habs
  cases f : σ.get m with
  | none =>
      rw [f] at habs
      exact absurd (show (none : Option (CellU Loc Val)) = some ψ from habs) (by simp)
  | some χ =>
      rw [f] at habs
      obtain ⟨ζ, hζ, hc⟩ := habs
      obtain rfl : χ = ζ := Option.some.inj hζ
      exact ⟨_, rfl, hc⟩

/-- **The first of the two things `[TR]` 6.59's closing sentence must know about
a walk**: every `imm` cell of `ag(X)` is absorbed by `W`.  At 6.59 `W` is the
goal's other side and this is `↭`'s first clause, which pins an `imm` cell
outright, together with the attribution that puts the pinned cell in `ag(R)`
rather than only in `ag(R ● ρ_reb)`.
`[about ours: the `imm`-cell half of the hypothesis `[TR]` 6.59's closing
sentence spends on a walk]` -/
def AgW.AbsImm (σ W : ResU Loc Val) : Prop :=
  ∀ m ψ, σ.get m = some ψ → ψ.kind = Kind.imm →
    ∃ φ, W.get m = some φ ∧ CellU.CompR ψ φ φ

/-- **…and the second**: every `imm` cell's witness has its whole `⦇−⦈_○`
inside `W`.  This is the ancestor step's own conclusion — `↭`'s first clause
pins the cell **with its witness** (`ResU.upd_ag_imm_wit_factor`), and the
walks are functional, so the witness names one resource and that resource is a
`○`-factor of the other side.
`[about ours: the witness half of the hypothesis `[TR]` 6.59's closing sentence
spends on a walk]` -/
def AgW.AbsAnc (σ W : ResU Loc Val) : Prop :=
  ∀ (m : Loc) (t : LSet) (u : Val) (κ : ResU Loc Val) (hh : κ.InStratum t.join),
    σ.get m = some (CellU.immOf t u κ hh) →
    ∀ ev av p, ExR κ ev → AgW κ av → ResU.CompR ev av p → ResU.CompR p W W

/-- Both halves pass to a `○`-factor of the walk: a factor's `imm` cell is the
walk's `imm` cell over the same witness (`CellU.CompR.imm_left_eq`), and the
factor's cell is absorbed by the walk's. -/
theorem AgW.AbsImm.of_le {τ σ W : ResU Loc Val} (hle : ResU.LeR τ σ)
    (h : AgW.AbsImm σ W) : AgW.AbsImm τ W := by
  intro m ψ hg hk
  obtain ⟨χ, hχ, hc⟩ := hle.get_some hg
  have hχk : χ.kind = Kind.imm := by
    obtain ⟨t, ht, e⟩ := CellU.imm_eta hk
    obtain ⟨t', h', e'⟩ := CellU.CompR.imm_left_eq hc e
    rw [e']; exact CellU.kind_immOf _ _ _ _
  obtain ⟨φ, hφ, hcf⟩ := h m χ hχ hχk
  exact ⟨φ, hφ, CellU.CompR.absorb_transC hc hcf⟩

theorem AgW.AbsAnc.of_le {τ σ W : ResU Loc Val} (hle : ResU.LeR τ σ)
    (h : AgW.AbsAnc σ W) : AgW.AbsAnc τ W := by
  intro m t u κ hh hg ev av p hev hav hp
  obtain ⟨χ, hχ, hc⟩ := hle.get_some hg
  obtain ⟨t', h', e'⟩ := CellU.CompR.imm_left_eq hc rfl
  rw [e'] at hχ
  exact h m t' u κ h' hχ ev av p hev hav hp

/-- **Every cell of `ag(X)` is accounted for by `ag(X)`'s own `imm` cells.**
This is `AgW.nonimm_beneath_imm` in the form `[TR]` 6.59's closing sentence
needs it — not *"this cell has an ancestor"* but *"no contribution is lost"*.

`ag(X) = (X∣imm ○ ⨀ ag(w_ℓ)) ○ ⨀ (ex(χ_ℓ)_○ ○ ag(χ_ℓ))` has exactly three
groups, and each lands in `W`:

* `X∣imm` — its cells are `ag(X)`'s own `imm` cells, which `AgW.AbsImm` absorbs;
* the `imm` family — each entry is the `⦇χ_ℓ⦈_○` of an `imm` cell of `X`, hence
  of an `imm` cell of `ag(X)` over the same witness (`AgW.get_imm`), which
  `AgW.AbsAnc` places inside `W`;
* the `mut` family — each entry is an `ag(w_ℓ)`, a `○`-factor of `ag(X)`, so
  both hypotheses pass to it (`AgW.AbsImm.of_le`, `AgW.AbsAnc.of_le`) and the
  induction closes it.

`ResU.CompR.absorb_comp` and `BigComp.absorb` then carry the three to the whole.
The `mut` family is where the recursion lives, and it is why the statement is
about `ag(X)`'s `imm` cells rather than `X`'s: a `mut` witness's walk raises
`imm` cells `X` never had.
`[about ours: `AgW.nonimm_beneath_imm` as an absorption rather than a trace]` -/
theorem AgW.absorb_of_ancestors {X a : ResU Loc Val} (h : AgW X a) :
    ∀ W : ResU Loc Val, AgW.AbsImm a W → AgW.AbsAnc a W → ResU.CompR a W W := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  refine AgW.rec
    (motive_1 := fun _ σ _ => ∀ W, AgW.AbsImm σ W → AgW.AbsAnc σ W →
      ResU.CompR σ W W)
    (motive_2 := fun _ w _ => ∀ q ∈ w, ∀ W, AgW.AbsImm q.2 W → AgW.AbsAnc q.2 W →
      ResU.CompR q.2 W W)
    (motive_3 := fun _ _ _ => True)
    ?mk ?nilM ?consM ?nilI ?consI h
  case mk =>
    intro ρ' σ' aa bm bi wm wi hsm hsi hwm hwi hbm hbi ha hσ ihm _ W himm hanc
    have hag : AgW ρ' σ' := AgW.mk hsm hsi hwm hwi hbm hbi ha hσ
    have hleA : ResU.LeR aa σ' := ResU.LeR.left hσ
    have hleBi : ResU.LeR bi σ' := ResU.LeR.right hσ
    have hleBm : ResU.LeR bm aa := ResU.LeR.right ha
    have hleImm : ResU.LeR (ρ'.restrict Kind.imm) aa := ResU.LeR.left ha
    -- (1) the top-level `imm` cells
    have h1 : ResU.CompR (ρ'.restrict Kind.imm) W W := by
      refine ResU.compR_absorb_of_cells (fun n ψ hg => ?_)
      exact AgW.AbsImm.of_le (hleImm.trans hleA) himm n ψ hg
        (ResU.restrict_eq_some.mp hg).2
    -- (2) the `mut` family
    have h2 : ResU.CompR bm W W := by
      refine BigComp.absorb hbm (fun τ hm => ?_)
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
      obtain ⟨z, hz⟩ := BigComp.mem_factor hR ResU.compLawsR hbm q.2
        (List.mem_map.mpr ⟨q, hq, rfl⟩)
      have hle : ResU.LeR q.2 σ' :=
        (ResU.LeR.left hz).trans (hleBm.trans hleA)
      exact ihm q hq W (AgW.AbsImm.of_le hle himm) (AgW.AbsAnc.of_le hle hanc)
    -- (3) the `imm` family
    have h3 : ResU.CompR bi W W := by
      refine BigComp.absorb hbi (fun τ hm => ?_)
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
      obtain ⟨ψ, ev, av, hψ, hex, hav, hp⟩ := AgWitsI.mem hwi q hq
      obtain ⟨ψ', hψ', hk'⟩ := (hsi.2 q.1).mp (List.mem_map.mpr ⟨q, hq, rfl⟩)
      obtain rfl : ψ' = ψ := Option.some.inj (hψ'.symm.trans hψ)
      obtain ⟨χ, hχ, hχk, hχe, hχw⟩ := AgW.get_imm hag hψ hk'
      obtain ⟨t, ht, he⟩ := CellU.imm_eta hχk
      rw [he] at hχ
      refine hanc q.1 t χ.erase χ.wit ht hχ ev av q.2 ?_ ?_ hp
      · rw [hχw]; exact hex
      · rw [hχw]; exact hav
    exact ResU.CompR.absorb_comp hσ (ResU.CompR.absorb_comp ha h1 h2) h3
  case nilM => intro ρ' q hq; exact absurd hq (by simp)
  case consM =>
    intro ρ' e l w ψ hψ hk he hw ihe ihw q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact ihe
    · exact ihw q hq'
  case nilI => intro _; trivial
  case consI => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; trivial

end BoCa.Fig16

namespace BoCa.Fig16

/-- **`ᾱ ⊆ ᾱ_R ∪ {β}` and `β ∉ ᾱ` give `ᾱ ⊆ ᾱ_R`.**  The `⊆` form of
`LSet.union_singleton_cancel`: what survives at an ancestor is not that the two
sets are equal but that the left one is inside the right one once the `{β}`
`ρ_reb` contributes is discounted — and *"all components of the composition
besides for `ρ_reb` outlive `β`"* is exactly `β ∉ ᾱ`. -/
theorem LSet.union_singleton_le_cancel {s t : LSet} {b : Life} (hs : ¬ s.mem b)
    (h : s ∪ (t ∪ LSet.singleton b) = t ∪ LSet.singleton b) : s ∪ t = t := by
  refine LSet.ext (fun x => ?_)
  have hx : (s ∪ (t ∪ LSet.singleton b)).mem x ↔ (t ∪ LSet.singleton b).mem x := by
    rw [h]
  by_cases hb : x = b
  · subst hb
    exact ⟨fun c => c.elim (fun d => absurd d hs) id, fun c => Or.inr c⟩
  · refine ⟨fun c => ?_, fun c => Or.inr c⟩
    rcases c with c | c
    · exact ((hx.mp (Or.inl c)).elim id (fun d => absurd d hb))
    · exact c

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- **What `↭` leaves at an ancestor `ρ_reb` reaches.**  `ρ_reb`'s cell
`imm({β}, v, χ)` stands between the two sides: the hypothesis pins
`ψ ○ (d ○ imm({β}, v, χ))` and the goal asks about `ψ ○ d`.  Composing with an
`imm` cell only joins lifetime sets, so the `{β}` may be cancelled off
both — `ψ` misses `β` because its component outlives `β` — and `ψ` is absorbed
by `d` alone.

The case where `d` is not an `imm` cell cannot arise: `ρ_reb`'s borrow would
absorb it outright and the composite would be `{β}` on the nose, which no
non-empty `β`-free `ᾱ` can be inside of (`LSet.union_singleton_ne_singleton`).
`[about ours: `[TR]` 6.59's *"neither have the immutable borrow at `β` from
`ρ_reb`"* as a `≼` at one cell]` -/
theorem CellU.reb_frame_imm_le {β : Life} {u : Val} {κ : ResU Loc Val}
    {hy : κ.InStratum (LSet.singleton β).join} {ψ d e : CellU Loc Val}
    (hψβ : ψ.InStratum β) (hψk : ψ.kind = Kind.imm)
    (hdB : CellU.CompR d (CellU.immOf (LSet.singleton β) u κ hy) e)
    (hψe : CellU.CompR ψ e e) : CellU.CompR ψ d d := by
  classical
  have hBk : (CellU.immOf (LSet.singleton β) u κ hy).kind = Kind.imm :=
    CellU.kind_immOf _ _ _ _
  have hcomm : CellU.CompR (CellU.immOf (LSet.singleton β) u κ hy) d e :=
    CellU.CompR.comm hdB
  have hek : e.kind = Kind.imm := by
    obtain ⟨E, hE, heE⟩ := CellU.CompR.imm_left_eq hcomm rfl
    rw [heE]; exact CellU.kind_immOf _ _ _ _
  obtain ⟨a, c, uu, χ, ha, hc, hu, eψ, ee, ecomp⟩ :=
    CellU.CompR.imm_imm_union hψe hψk hek
  have haE : a ∪ c = c := (CellU.immOf_inj (ecomp.symm.trans ee)).1
  have hβa : ¬ a.mem β := CellU.notMem_of_inStratum (eψ ▸ hψβ)
  by_cases hdk : d.kind = Kind.imm
  · obtain ⟨D, sb, ud, χd, hD, hsb, hud, ed, eB, ecd⟩ :=
      CellU.CompR.imm_imm_union hdB hdk hBk
    obtain ⟨rfl, rfl, rfl⟩ := CellU.immOf_inj eB.symm
    obtain ⟨rfl, rfl, rfl⟩ := CellU.immOf_inj (ee.symm.trans ecd)
    have haD : a ∪ D = D := LSet.union_singleton_le_cancel hβa haE
    have hcs : ψ.CompatS d := by
      rw [eψ, ed]; exact ⟨a, D, uu, χ, ha, hD, rfl, rfl⟩
    obtain ⟨s₁, s₂, vv, ρρ, k₁, k₂, k₃, f₁, f₂, f₃⟩ := CellU.compS_spec ψ d hcs
    obtain ⟨rfl, rfl, rfl⟩ := CellU.immOf_inj (eψ.symm.trans f₁)
    obtain ⟨rfl, -, -⟩ := CellU.immOf_inj (ed.symm.trans f₂)
    have hfix : CellU.compS ψ d hcs = d := by
      rw [f₃, ed]; exact CellU.immOf_congr haD rfl rfl k₃ hD
    have hstr : CellU.CompR ψ d (CellU.compS ψ d hcs) := CellU.CompR.strict hcs
    rwa [hfix] at hstr
  · exfalso
    have heB : e = CellU.immOf (LSet.singleton β) u κ hy :=
      CellU.CompR.imm_nonimm_left hcomm hBk hdk
    have h2 := (CellU.immOf_inj (ee.symm.trans heB)).1
    refine LSet.union_singleton_ne_singleton hβa ?_
    rw [← h2]; exact haE

/-- **`ag(ρᵢ)` stands wherever `ρ_reb` does.**  A reborrowed `ℓ` is an `own` or
a `mut` cell of `ρ′ᵢ`, the exclusive walk carries such a cell up
(`ExR.get_of_ne_imm`), and `⦇ρ′ᵢ⦈_○` is `ag(ρᵢ)`'s own `imm`-family entry
(`AgW.single_imm_inv`).
`[about ours: `ag(ρᵢ)` at a location `ρ_reb` covers]` -/
theorem ResU.ag_single_imm_some_of_reb
    {ρ'i ρ ai : ResU BoCa.Loc BoCa.Val}
    {l₀ : BoCa.Loc} {s : LSet} {v : BoCa.Val} {hs : ρ'i.InStratum s.join}
    (hai : AgW (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ai)
    {l : BoCa.Loc} {ζ : CellU BoCa.Loc BoCa.Val}
    (hζ : (ρ.restrictDom ρ'i.exclPart).get l = some ζ) :
    ∃ c, ai.get l = some c := by
  obtain ⟨es, as, pS, hexS, hagS, hfS, hagi⟩ := AgW.single_imm_inv hai
  obtain ⟨φ', hφ'⟩ := ResU.restrictDom_dom hζ
  obtain ⟨hφ'g, hφ'k⟩ := ResU.exclPart_eq_some.mp hφ'
  obtain ⟨ξ, hξ, -, -⟩ := ExR.get_of_ne_imm hexS hφ'g hφ'k
  have hpS : ∃ c, pS.get l = some c := by
    rcases ResU.Comp.get hfS l with ⟨f₁, -, -⟩ | ⟨ψ, -, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
        ⟨ψ₁, ψ₂, ψ, -, -, f, -⟩
    · rw [hξ] at f₁; exact absurd f₁ (by simp)
    · exact ⟨ψ, f⟩
    · rw [hξ] at f₁; exact absurd f₁ (by simp)
    · exact ⟨ψ, f⟩
  obtain ⟨cS, hcS⟩ := hpS
  rcases ResU.Comp.get hagi l with ⟨-, f₂, -⟩ | ⟨ψ, -, -, f⟩ | ⟨ψ, -, f₂, f⟩ |
      ⟨ψ₁, ψ₂, ψ, -, -, f, -⟩
  · rw [hcS] at f₂; exact absurd f₂ (by simp)
  · exact ⟨ψ, f⟩
  · exact ⟨ψ, f⟩
  · exact ⟨ψ, f⟩

/-- **…and where the aliasable walk is silent the flattening is the exclusive
one.**  `ResU.flat_eq_ag_of_immFree` is the other half of reading
`⦇ρ⦈ ≜ ex(ρ)_● ● ag(ρ)` at a location.
`[about ours: `⦇ρ⦈` where `ag(ρ)` carries nothing]` -/
theorem ResU.flat_eq_ex_of_ag_none {Loc Val : Type} {e a σ : ResU Loc Val}
    (hc : ResU.CompS e a σ) {l : Loc} (h : a.get l = none) :
    σ.get l = e.get l := by
  rcases ResU.Comp.get hc l with ⟨f₁, -, f⟩ | ⟨ψ, f₁, -, f⟩ | ⟨ψ, -, f₂, -⟩ |
      ⟨ψ₁, ψ₂, ψ, -, f₂, -, -⟩
  · rw [f, f₁]
  · rw [f, f₁]
  · rw [h] at f₂; exact absurd f₂ (by simp)
  · rw [h] at f₂; exact absurd f₂ (by simp)

/-- Two flattenings that agree at `ℓ` are `ResU.SimFormAt` there: `∼` between a
cell and itself is `CellU.Sim.refl`, and `−∣imm,mut` drops the `own` case. -/
theorem ResU.simFormAt_of_eq {σ₁ σ₂ : ResU BoCa.Loc BoCa.Val} {l : BoCa.Loc}
    (h : σ₁.get l = σ₂.get l) : ResU.SimFormAt σ₁ σ₂ l := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨ψ, hψ⟩
    obtain ⟨hg, hk⟩ := ResU.borrowPart_eq_some.mp hψ
    exact ⟨ψ, ResU.borrowPart_eq_some.mpr ⟨h ▸ hg, hk⟩⟩
  · rintro ⟨ψ, hψ⟩
    obtain ⟨hg, hk⟩ := ResU.borrowPart_eq_some.mp hψ
    exact ⟨ψ, ResU.borrowPart_eq_some.mpr ⟨h.symm ▸ hg, hk⟩⟩
  · intro ψ hψ
    obtain ⟨hg, hk⟩ := ResU.borrowPart_eq_some.mp hψ
    exact ⟨ψ, h ▸ hg, CellU.Sim.refl hk⟩

/-- `ResU.SimFormAt` reads its two flattenings at `ℓ` and nowhere else, `−∣imm,mut`
being a restriction of the same map. -/
theorem ResU.simFormAt_congr {σ₁ σ₂ τ₁ τ₂ : ResU BoCa.Loc BoCa.Val} {l : BoCa.Loc}
    (h₁ : σ₁.get l = τ₁.get l) (h₂ : σ₂.get l = τ₂.get l)
    (h : ResU.SimFormAt τ₁ τ₂ l) : ResU.SimFormAt σ₁ σ₂ l := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨ψ, hψ⟩
    obtain ⟨hg, hk⟩ := ResU.borrowPart_eq_some.mp hψ
    obtain ⟨φ, hφ⟩ := h.1.1 ⟨ψ, ResU.borrowPart_eq_some.mpr ⟨h₁.symm.trans hg, hk⟩⟩
    obtain ⟨hg₂, hk₂⟩ := ResU.borrowPart_eq_some.mp hφ
    exact ⟨φ, ResU.borrowPart_eq_some.mpr ⟨h₂.trans hg₂, hk₂⟩⟩
  · rintro ⟨ψ, hψ⟩
    obtain ⟨hg, hk⟩ := ResU.borrowPart_eq_some.mp hψ
    obtain ⟨φ, hφ⟩ := h.1.2 ⟨ψ, ResU.borrowPart_eq_some.mpr ⟨h₂.symm.trans hg, hk⟩⟩
    obtain ⟨hg₂, hk₂⟩ := ResU.borrowPart_eq_some.mp hφ
    exact ⟨φ, ResU.borrowPart_eq_some.mpr ⟨h₁.trans hg₂, hk₂⟩⟩
  · intro ψ hψ
    obtain ⟨hg, hk⟩ := ResU.borrowPart_eq_some.mp hψ
    obtain ⟨φ, hφ, hsim⟩ :=
      h.2 ψ (ResU.borrowPart_eq_some.mpr ⟨h₁.symm.trans hg, hk⟩)
    exact ⟨φ, h₂.trans hφ, hsim⟩

/-- **`ResU.SixFiftyNineResidual` at Definition 6.3's paragraph.**  Every binder,
hypothesis and conclusion is `ResU.SixFiftyNineResidual`'s; the single difference
is that `χ` is bound by `ResU.SubKeep` rather than by `ResU.Sub`.
`[about ours: `ResU.SixFiftyNineResidual` with Definition 6.3's third bullet
read through the paragraph below it]` -/
def ResU.SixFiftyNineResidualKeep : Prop :=
  ∀ (β : Life) (ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY : ResU BoCa.Loc BoCa.Val)
    (l₀ : BoCa.Loc) (s : LSet) (v : BoCa.Val) (hs : ρ'i.InStratum s.join),
    ResU.Reb β ρ'i ρ →
    ResU.CompS ρ ρb ρρb →
    ResU.CompS ρ' ρp ρ'p →
    ResU.UpdV ρρb ρ'p →
    ρb.InStratum β →
    ρ'.InStratum β →
    ResU.Hash ρb (ResU.single l₀ (CellU.immOf s v ρ'i hs)) →
    ResU.Hash ρ'p (ResU.single l₀ (CellU.immOf s v ρ'i hs)) →
    ResU.SubKeep ρp (ρ.restrictDom ρ'i.exclPart) χ →
    ResU.CompS (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ρb Xi →
    (∃ w, ResU.CompS ρ' χ w ∧
      ResU.CompS w (ResU.single l₀ (CellU.immOf s v ρ'i hs)) Y) →
    ResU.Flat Xi σX →
    ResU.Flat Y σY →
    ∀ l : BoCa.Loc, (∃ ζ, (ρ.restrictDom ρ'i.exclPart).get l = some ζ) →
      ResU.SimFormAt σX σY l

theorem ResU.reb_immOnly {β : Life} {ρ'i ρ : ResU BoCa.Loc BoCa.Val}
    (hreb : ResU.Reb β ρ'i ρ) :
    ∀ l ψ, ρ.get l = some ψ → ψ.kind = Kind.imm :=
  fun _ _ hg => ResU.reb_imm_image hreb hg

theorem ResU.reb_reb_immOnly {β : Life} {ρ'i ρ : ResU BoCa.Loc BoCa.Val}
    (hreb : ResU.Reb β ρ'i ρ) :
    ∀ l ψ, (ρ.restrictDom ρ'i.exclPart).get l = some ψ → ψ.kind = Kind.imm :=
  fun _ _ hg => ResU.reb_imm_image hreb (ResU.restrictDom_get_inv hg)

theorem ResU.single_imm_immOnly {ρ'i : ResU BoCa.Loc BoCa.Val} {l₀ : BoCa.Loc}
    {s : LSet} {v : BoCa.Val} {hs : ρ'i.InStratum s.join} :
    ∀ l ψ, (ResU.single l₀ (CellU.immOf s v ρ'i hs)).get l = some ψ →
      ψ.kind = Kind.imm := by
  intro l ψ hg
  obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hg
  exact CellU.kind_immOf _ _ _ _

/-- **`ResU.SixFiftyNineOffReb` at Definition 6.3's paragraph.**  Every binder,
hypothesis and conclusion is `ResU.SixFiftyNineOffReb`'s; the single difference
is that `χ` is bound by `ResU.SubKeep` rather than by `ResU.Sub`.
`[about ours: `ResU.SixFiftyNineOffReb` with Definition 6.3's third bullet read
through the paragraph below it]` -/
def ResU.SixFiftyNineOffRebKeep : Prop :=
  ∀ (β : Life) (ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY : ResU BoCa.Loc BoCa.Val)
    (l₀ : BoCa.Loc) (s : LSet) (v : BoCa.Val) (hs : ρ'i.InStratum s.join),
    ResU.Reb β ρ'i ρ →
    ResU.CompS ρ ρb ρρb →
    ResU.CompS ρ' ρp ρ'p →
    ResU.UpdV ρρb ρ'p →
    ρb.InStratum β →
    ρ'.InStratum β →
    ResU.Hash ρb (ResU.single l₀ (CellU.immOf s v ρ'i hs)) →
    ResU.Hash ρ'p (ResU.single l₀ (CellU.immOf s v ρ'i hs)) →
    ResU.SubKeep ρp (ρ.restrictDom ρ'i.exclPart) χ →
    ResU.CompS (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ρb Xi →
    (∃ w, ResU.CompS ρ' χ w ∧
      ResU.CompS w (ResU.single l₀ (CellU.immOf s v ρ'i hs)) Y) →
    ResU.Flat Xi σX →
    ResU.Flat Y σY →
    ∀ l : BoCa.Loc, (ρ.restrictDom ρ'i.exclPart).get l = none →
      ResU.SimFormAt σX σY l

end BoCa.Fig16

end
