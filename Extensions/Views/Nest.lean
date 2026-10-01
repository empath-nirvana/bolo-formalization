import Views.Uses

/-!
# Views — where the typed world stops a same-lifetime view

The typed world (`Fig16.LogRel.Typed.TW`, `docs/adjudications.md` §12.72) is the family of
resources the printed proofs' operations produce, and `Fig16.LogRel.Typed.TW.inv` is its
invariant.  One clause of that invariant, `Fig16.LogRel.Typed.NestLife`, asks that a view at a
chain position be strictly shorter-lived than the view at the position before it: every view
the printed operations make below an existing view comes from `[TR]` 6.150 at a fresh, shorter
`β`.

`minted_not_nestLife` builds the share frame's resource for `ℓ ↦ own(ℓ₁) ● ℓ₁ ↦ own(ℓ₂) ●
ℓ₂ ↦ own(())` at `α` (`mint_shr_of`): the views at `ℓ₁` and at `ℓ₂` are both at `α`, and
`NestLife` fails at the record of that frame.  So no `TW` world holding that record is the
share frame's resource (`minted_not_TW`), and the share frame is not one of the typed world's
operations.  Adding it means relaxing `NestLife` to `⊑` (and `FrameLife`'s second clause, which
asks the same of a frame's lineage), and adding the frame's entry and exit to `TW`.

`[about ours]`: an extension, not a transcription.
-/

noncomputable section

namespace BoCa.Views
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel
open BoCa.Fig16.LogRel.Typed
open BoCa.Lifetime (LSub LifeVar)

/-- Adding a fresh `own` cell to a resource with a memory keeps it valid. -/
theorem add_own_valid {ρ ρ' : WRes} {μ : BoCa.BoLo.Heap} {l : Loc} {v : Val}
    (hμ : ResU.Lower ρ μ) (hl : μ l = none) (hc : ResU.CompS ρ (ResU.single l (CellU.ownOf v)) ρ') :
    ResU.Valid ρ' ∧ ResU.Lower ρ' (BoCa.BoLo.Heap.upd μ l v) := by
  obtain ⟨σ', hσ', hh, hlow⟩ := hash_compS_own (compS_empty_left ρ) hμ hl hc
  cases eq_of_compS_empty_left hσ'
  exact ⟨(hash_valid hh).2, hlow⟩

/-- The three cells `2 ↦ own(1)`, `1 ↦ own(0)`, `0 ↦ own(())`: `O` is all three, `R` the last
two, `𝒱⟦Ref (Ref 1)⟧δ(1)(R)`. -/
theorem three_cells (δ : LSub) :
    ∃ R O, ResU.CompS (ResU.single 2 (CellU.ownOf (Val.loc 1))) R O ∧
      ResU.CompS (ResU.single 1 (CellU.ownOf (Val.loc 0))) (pointee 0) R ∧
      vDen (.ref (.ref .unit)) δ (Val.loc 1) R ∧ ResU.Valid O ∧ (∀ β, R.InStratum β) := by
  have h01 : (pointee 0).get 1 = none := ResU.single_get_ne _ (by decide)
  have hμ₀ : ResU.Lower (pointee 0) (fun k => ((pointee 0).get k).map CellU.erase) :=
    ⟨_, ResU.flat_single_own 0 Val.unit, fun _ => rfl⟩
  obtain ⟨R, hR⟩ := (ResU.compS_defined_iff (pointee 0)
    (ResU.single 1 (CellU.ownOf (Val.loc 0)))).mpr (compatS_single_of_get_none h01)
  obtain ⟨-, hμR⟩ := add_own_valid hμ₀ (by simp [h01]) hR
  have hR2 : R.get 2 = none := (ResU.Comp.eq_none_iff hR 2).mpr
    ⟨ResU.single_get_ne _ (by decide), ResU.single_get_ne _ (by decide)⟩
  obtain ⟨O, hO⟩ := (ResU.compS_defined_iff R
    (ResU.single 2 (CellU.ownOf (Val.loc 1)))).mpr (compatS_single_of_get_none hR2)
  have hμR2 : (BoCa.BoLo.Heap.upd (fun k => ((pointee 0).get k).map CellU.erase) 1 (Val.loc 0))
      2 = none := by
    simp [BoCa.BoLo.Heap.upd, ResU.single_get_ne _ (show (2 : Loc) ≠ 0 by decide)]
  obtain ⟨hvO, -⟩ := add_own_valid hμR hμR2 hO
  exact ⟨R, O, ResU.CompS.comm hO, ResU.CompS.comm hR,
    ⟨1, Val.loc 0, PMap.empty, R, ResU.comp_empty_left R, ⟨rfl, rfl⟩, _, _,
      ResU.CompS.comm hR, rfl, vDen_ref_unit δ 0⟩, hvO,
    fun β => ResU.CompS.inStratum hR (single_own_inStratum _ _ _) (single_own_inStratum _ _ _)⟩

/-- At a mint `Y` over a valid `O`, `ag(Y)` holds each of `Y`'s cells as it is. -/
theorem Mint.ag_get {α : Life} {O Y : WRes} (hM : Mint α O Y) (hvO : ResU.Valid O) {a : WRes}
    (ha : AgW Y a) {m : Loc} {ψ : CellU Loc Val} (e : Y.get m = some ψ) : a.get m = some ψ := by
  obtain ⟨σ, eO, aO, heO, haO, hcO⟩ := hvO
  obtain ⟨p, hp, hYp⟩ := hM.ag eO aO a heO haO ha
  rw [ResU.CompR.functional hp (ResU.CompS.toCompR hcO)] at hYp
  have hσm := flat_own_of_ex ⟨eO, aO, heO, haO, hcO⟩ heO (hM.own eO heO m ψ e)
  rcases ResU.Comp.get hYp m with ⟨f, -, -⟩ | ⟨χ, f₁, f₂, -⟩ | ⟨χ, f₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, f₂, f, hC⟩
  · rw [f] at e; cases e
  · rw [hσm] at f₂; cases f₂
  · rw [f₁] at e; cases e
  · rw [e] at f₁; cases Option.some.inj f₁
    rw [hσm] at f₂; cases Option.some.inj f₂
    rw [f, CellU.compR_own_right hC]

/-- `O`'s `ex` holds an `own` cell of `O`. -/
theorem ex_own_of_get {O : WRes} {m : Loc} {u : Val} (h : O.get m = some (CellU.ownOf u)) :
    ∀ eO, ExS O eO → eO.get m = some (CellU.ownOf u) :=
  fun _ heO => ExS.get_of_ne_imm heO h (by simp)

/-- **The share frame's resource fails `NestLife`.**  At `2 ↦ own(1) ● 1 ↦ own(0) ●
0 ↦ own(())`, the share frame at `α` mints `Y = 2 ↦ imm({α}, 1, R) ● 1 ↦ imm({α}, 0, …) ●
0 ↦ imm({α}, (), ∅)`, a member of `Shr α (Ref (Ref 1))(2)`; at the frame's record
`⟨2, 1, R, Ref (Ref 1), δ⟩`, the view at `0` is not shorter than the view at `1`. -/
theorem minted_not_nestLife (α : Life) (δ : LSub) :
    ∃ (R O Y : WRes), Mint α O Y ∧ shrDen α (.ref (.ref .unit)) δ (Val.loc 2) Y ∧
      ¬ NestLife Y ⟨2, Val.loc 1, R, .ref (.ref .unit), δ⟩ := by
  obtain ⟨R, O, hc, hR, hRden, hvO, hRα⟩ := three_cells δ
  have hRα' : R.InStratum (LSet.singleton α).join := hRα _
  have hP0 : ResU.InStratum (LSet.singleton α).join (pointee 0) := single_own_inStratum _ _ _
  have hE : ResU.InStratum (LSet.singleton α).join (PMap.empty : WRes) := ResU.inStratum_empty _
  -- `O`'s cells
  have hO2 : O.get 2 = some (CellU.ownOf (Val.loc 1)) :=
    (ResU.CompS.get_left_of_ne_imm hc (ResU.single_get_self _ _) (by simp)).2
  have hR1 : R.get 1 = some (CellU.ownOf (Val.loc 0)) :=
    (ResU.CompS.get_left_of_ne_imm hR (ResU.single_get_self _ _) (by simp)).2
  have hR0 : R.get 0 = some (CellU.ownOf Val.unit) :=
    (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hR) (ResU.single_get_self _ _) (by simp)).2
  have hO1 := (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hc) hR1 (by simp)).2
  have hO0 := (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hc) hR0 (by simp)).2
  -- the head, then the view at `1`, then the view at `0`
  have hM₀ : Mint α O (ResU.single 2 (CellU.immOf (LSet.singleton α) (Val.loc 1) R hRα')) :=
    mint_single (ResU.CompS.comm hc) hvO
  have hP0O : ResU.Le (pointee 0) O :=
    (le_of_compS_right hR).trans (le_of_compS_right hc)
  obtain ⟨Y₁, hY₁, hM₁⟩ := Mint.add (u := Val.loc 0) (w := pointee 0) (h := hP0) hM₀ hvO
    (ex_own_of_get hO1) (ResU.single_get_ne _ (by decide)) hP0O
  obtain ⟨Y, hY, hM⟩ := Mint.add (m := 0) (u := Val.unit) (w := PMap.empty) (h := hE) hM₁ hvO
    (ex_own_of_get hO0)
    ((ResU.Comp.eq_none_iff hY₁ 0).mpr ⟨ResU.single_get_ne _ (by decide),
      ResU.single_get_ne _ (by decide)⟩) (ResU.Le.empty O)
  -- `Y`'s cells at `1` and `0`
  have hY1 : Y.get 1 = some (CellU.immOf (LSet.singleton α) (Val.loc 0) (pointee 0) hP0) := by
    have h₁ : Y₁.get 1 = some (CellU.immOf (LSet.singleton α) (Val.loc 0) (pointee 0) hP0) :=
      (ResU.Comp.get_of_left_none hY₁ (ResU.single_get_ne _ (by decide))).trans
        (ResU.single_get_self _ _)
    exact (ResU.Comp.get_of_right_none hY (ResU.single_get_ne _ (by decide))).trans h₁
  have hY0 : Y.get 0 = some (CellU.immOf (LSet.singleton α) Val.unit PMap.empty hE) :=
    (ResU.Comp.get_of_left_none hY ((ResU.Comp.eq_none_iff hY₁ 0).mpr
      ⟨ResU.single_get_ne _ (by decide), ResU.single_get_ne _ (by decide)⟩)).trans
      (ResU.single_get_self _ _)
  -- `Y ∈ Shr α (Ref (Ref 1))(2)`
  have hshr : shrDen α (.ref (.ref .unit)) δ (Val.loc 2) Y := by
    obtain ⟨V, hV, hHV⟩ := (ResU.CompS.assoc _ _ _ Y).mpr ⟨Y₁, hY₁, hY⟩
    refine ⟨2, Val.loc 1, PMap.empty, Y, ResU.comp_empty_left Y, ⟨rfl, rfl⟩, _, V, hHV,
      ⟨LSet.singleton α, Val.loc 1, R, hRα', rfl, ⟨rfl, hRden⟩, le_refl α⟩, ?_⟩
    refine ⟨1, Val.loc 0, PMap.empty, V, ResU.comp_empty_left V, ⟨rfl, rfl⟩, _, _, hV,
      ⟨LSet.singleton α, Val.loc 0, pointee 0, hP0, rfl, ⟨rfl, vDen_ref_unit δ 0⟩, le_refl α⟩,
      ?_⟩
    refine ⟨0, Val.unit, PMap.empty, _, ResU.comp_empty_left _, ⟨rfl, rfl⟩, _, PMap.empty,
      ResU.comp_empty_right _,
      ⟨LSet.singleton α, Val.unit, PMap.empty, hE, rfl, ⟨rfl, rfl, rfl⟩, le_refl α⟩,
      ⟨rfl, rfl⟩⟩
  refine ⟨R, O, Y, hM, hshr, fun hN => ?_⟩
  -- the chain `2 → 1 → 0` of the record
  have hch : Chain R (.ref (.ref .unit)) (Val.loc 1) (some 1) 0 .unit Val.unit :=
    Chain.step (RefPos.ref (.ref .unit) 1) hR1 (Chain.one (RefPos.ref .unit 0) hR0)
  obtain ⟨a, ha⟩ := hM.agDef
  obtain ⟨ζ, t, y, eζ, ht, hy, hlt⟩ := hN 1 0 .unit Val.unit hch a ha _ _
    (hM.ag_get hvO ha hY0) (CellU.lsOf_immOf _ _ _ _) α rfl
  rw [hM.ag_get hvO ha hY1] at eζ
  cases Option.some.inj eζ
  rw [CellU.lsOf_immOf] at ht
  cases Option.some.inj ht
  have : y = α := hy
  subst this
  exact lt_irrefl _ hlt

/-- **No typed world is the share frame's resource with its record**: every `TW` world
satisfies `NestLife` at each record (`TW.inv`). -/
theorem minted_not_TW (α : Life) (δ : LSub) :
    ∃ (R Y : WRes), shrDen α (.ref (.ref .unit)) δ (Val.loc 2) Y ∧
      ∀ ps rs, ⟨2, Val.loc 1, R, .ref (.ref .unit), δ⟩ ∈ rs → ¬ TW Y ps rs := by
  obtain ⟨R, O, Y, -, hshr, hN⟩ := minted_not_nestLife α δ
  exact ⟨R, Y, hshr, fun ps rs hr hT => hN (hT.inv.2.2.2.2.1 _ hr)⟩

end BoCa.Views

end
