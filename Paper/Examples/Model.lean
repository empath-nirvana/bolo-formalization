import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Paper.S6_2_NonStandardLemmas.Lemmas

/-!
# Examples — the model's walks and splits at a shared location

`[TR]` Lemmas 6.7, 6.18 and 6.20 are Kleene equalities whose difficulty is the case
where two operands share an `imm` location.  These declarations build that case —
`0 ↦ imm({2}, 5, ∅)` and `0 ↦ imm({3}, 5, ∅)`, composed by `[TR]` Lemma 6.43 to
`0 ↦ imm({2,3}, 5, ∅)` — and run the lemmas on it, so their hypotheses are
inhabited at the configuration the printed proofs spend their last step on.

The last section inhabits hypotheses that rows of `[TR]` §6.2 bind or add.

`[about ours: instances of [TR] Lemmas 6.7 and 6.20 at a shared `imm` location, and
inhabitants of hypotheses of §6.2's rows]`
-/

namespace BoCa.Fig16

namespace SplitExample
noncomputable section

/-- The witness of the shared `imm` cell, taken empty. -/
private def wit : ResU Nat Nat := PMap.empty

private theorem wit_get (l : Nat) : wit.get l = none := rfl

private theorem wit_inStratum (α : Life) : wit.InStratum α := by
  intro l ψ e
  rw [wit_get] at e
  exact absurd e (by simp)

private theorem wit_restrict (k : Kind) : wit.restrict k = wit :=
  PMap.ext (fun l => ResU.restrict_get_none (wit_get l))

private theorem wit_sites (k : Kind) : wit.Sites k [] := by
  refine ⟨List.nodup_nil, fun l => ⟨fun h => absurd h (by simp), ?_⟩⟩
  rintro ⟨ψ, e, -⟩
  rw [wit_get] at e
  exact absurd e (by simp)

/-- `ex(∅)_○ = ∅`. -/
private theorem exR_wit : ExR wit wit := by
  refine ExW.mk (w := []) (b := PMap.empty) (nm := wit) (wit_sites Kind.mut) ExWits.nil
    BigComp.nil ?_ (ResU.comp_empty_right _)
  rw [wit_restrict, wit_restrict]
  exact ResU.comp_empty_right _

/-- `ag(∅) = ∅`. -/
private theorem agW_wit : AgW wit wit := by
  refine AgW.mk (wm := []) (wi := []) (a := wit) (bm := PMap.empty) (bi := PMap.empty)
    (wit_sites Kind.mut) (wit_sites Kind.imm) AgWitsM.nil AgWitsI.nil
    BigComp.nil BigComp.nil ?_ (ResU.comp_empty_right _)
  rw [wit_restrict]
  exact ResU.comp_empty_right _

/-- `imm(ᾱ, 5, ∅)` — the cell the two operands share, differing only in `ᾱ`. -/
def cell (s : LSet) : CellU Nat Nat := CellU.immOf s 5 wit (wit_inStratum s.join)

private theorem cell_kind (s : LSet) : (cell s).kind = Kind.imm := rfl

private theorem cell_wit (s : LSet) : (cell s).wit = wit := CellU.wit_immOf _ _ _ _

/-- `ag(0 ↦ imm(ᾱ, 5, ∅)) = 0 ↦ imm(ᾱ, 5, ∅)`.  The derivation goes through
`AgWitsI.cons`: the resource has an `imm` cell, so the imm family is not empty
and the walk descends into the witness. -/
theorem agW_res (s : LSet) :
    AgW (ResU.single 0 (cell s)) (ResU.single 0 (cell s)) := by
  have hget : (ResU.single 0 (cell s)).get 0 = some (cell s) := ResU.single_get_self _ _
  have hres : (ResU.single 0 (cell s)).restrict Kind.imm = ResU.single 0 (cell s) := by
    refine PMap.ext (fun l => ?_)
    by_cases e : l = 0
    · subst e
      rw [hget]
      exact ResU.restrict_get_some (k := Kind.imm) hget (cell_kind s)
    · rw [ResU.single_get_ne _ e]
      exact ResU.restrict_get_none (ResU.single_get_ne _ e)
  refine AgW.mk (wm := []) (wi := [(0, wit)]) (a := ResU.single 0 (cell s))
    (bm := PMap.empty) (bi := wit)
    ⟨List.nodup_nil, fun l => ⟨fun h => absurd h (by simp), ?_⟩⟩
    ⟨by simp, fun l => ⟨?_, ?_⟩⟩ AgWitsM.nil ?_ BigComp.nil
    (BigComp.cons BigComp.nil (ResU.comp_empty_right _)) ?_ ?_
  · -- there is no `mut` cell
    rintro ⟨ψ, e, ek⟩
    obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some e
    exact absurd (ek.symm.trans (cell_kind s)) (by decide)
  · -- and exactly one `imm` cell, at `0`
    intro h
    have : l = 0 := by simpa using h
    subst this
    exact ⟨cell s, hget, cell_kind s⟩
  · rintro ⟨ψ, e, -⟩
    obtain ⟨rfl, -⟩ := ResU.single_get_eq_some e
    simp
  · refine AgWitsI.cons (cell s) hget (cell_kind s) wit wit ?_ ?_
      (ResU.comp_empty_right _) AgWitsI.nil
    · show ExR (cell s).wit wit
      rw [cell_wit]; exact exR_wit
    · show AgW (cell s).wit wit
      rw [cell_wit]; exact agW_wit
  · rw [hres]; exact ResU.comp_empty_right _
  · exact ResU.comp_empty_right _

def sA : LSet := LSet.singleton 2
def sB : LSet := LSet.singleton 3

/-- **`AgW.split` at a genuine `imm` overlap.**  `0 ↦ imm({2}, 5, ∅)` and
`0 ↦ imm({3}, 5, ∅)` are `▸◂`-compatible and their `●` is
`0 ↦ imm({2,3}, 5, ∅)`, so both operands and the composite have a value of `ag`
and 6.20 relates them.  Reading the conclusion back through `AgW.functional`
turns it into `ag(ρ₁) ○ ag(ρ₂) = ag(ρ₁ ● ρ₂)` at these three resources. -/
theorem overlap :
    ResU.CompR (ResU.single 0 (cell sA)) (ResU.single 0 (cell sB))
      (ResU.single 0 (cell (sA.union sB))) := by
  have h₁₂ : ResU.CompS (ResU.single 0 (cell sA)) (ResU.single 0 (cell sB))
      (ResU.single 0 (cell (sA.union sB))) :=
    ResU.compS_single_imm 0 sA sB 5 wit (wit_inStratum _) (wit_inStratum _)
      (wit_inStratum _)
  obtain ⟨σ₁, σ₂, k₁, k₂, kc⟩ := (AgW.split h₁₂).mp (agW_res _)
  rw [AgW.functional k₁ (agW_res sA), AgW.functional k₂ (agW_res sB)] at kc
  exact kc

end
end SplitExample

namespace LowerExample
noncomputable section
open SplitExample

/-- An `imm` cell survives neither the `own` nor the `mut` restriction. -/
private theorem res_restrict_ne (s : LSet) {k : Kind} (hk : k ≠ Kind.imm) :
    (ResU.single 0 (cell s)).restrict k = PMap.empty := by
  refine PMap.ext fun l => ?_
  by_cases e : l = 0
  · subst e
    exact ResU.restrict_get_ne (ResU.single_get_self _ _)
      (fun h => hk (h.symm.trans (cell_kind s)))
  · exact ResU.restrict_get_none (ResU.single_get_ne _ e)

/-- …and the resource indexes no `mut` site. -/
private theorem res_sites_mut (s : LSet) :
    ResU.Sites (ResU.single 0 (cell s)) Kind.mut [] := by
  refine ⟨List.nodup_nil, fun l => ⟨fun h => absurd h (by simp), ?_⟩⟩
  rintro ⟨ψ, e, ek⟩
  obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some e
  exact absurd (ek.symm.trans (cell_kind s)) (by decide)

/-- So `ex(0 ↦ imm(ᾱ, 5, ∅))_● = ∅`: the exclusive walk composes nothing. -/
theorem exS_res (s : LSet) : ExS (ResU.single 0 (cell s)) PMap.empty := by
  refine ExW.mk (w := []) (b := PMap.empty) (nm := PMap.empty)
    (res_sites_mut s) ExWits.nil BigComp.nil ?_ (ResU.comp_empty_right _)
  rw [res_restrict_ne s (by decide), res_restrict_ne s (by decide)]
  exact ResU.comp_empty_right _

/-- `⦇0 ↦ imm(ᾱ, 5, ∅)⦈ = 0 ↦ imm(ᾱ, 5, ∅)` — the empty exclusive walk against
the aliasable walk `SplitExample.agW_res` computes. -/
theorem flat_res (s : LSet) :
    ResU.Flat (ResU.single 0 (cell s)) (ResU.single 0 (cell s)) :=
  ⟨PMap.empty, ResU.single 0 (cell s), exS_res s, agW_res s,
    ResU.CompS.comm (ResU.comp_empty_right _)⟩

/-- The two operands share the location `0`, at different lifetime sets over one
witness and one value — the composition `[TR]` Lemma 6.43 licenses, and the one
`SplitExample.overlap` runs 6.20 on.
`[about ours: an instance of `ResU.compS_single_imm`, which is the printed
Lemma 6.43]` -/
theorem compS_res :
    ResU.CompS (ResU.single 0 (cell sA)) (ResU.single 0 (cell sB))
      (ResU.single 0 (cell (sA.union sB))) :=
  ResU.compS_single_imm 0 sA sB 5 wit (wit_inStratum _) (wit_inStratum _)
    (wit_inStratum _)

/-- `0 ↦ imm({2}, 5, ∅) # 0 ↦ imm({3}, 5, ∅)`: they are `▸◂`-compatible and
their `●` is valid, so 6.7's printed hypothesis holds of a pair that shares a
location. -/
theorem hash_res :
    ResU.Hash (ResU.single 0 (cell sA)) (ResU.single 0 (cell sB)) :=
  ⟨compS_res.1, _, compS_res, _, flat_res (sA.union sB)⟩

/-- **6.7 at a genuine overlap.**  Both operands of the `∪` are defined at `0`
and carry the same value there, so `OptUnion`'s overlap clause is the one that
runs, and the union it produces is `⟦ρ₁ ● ρ₂⟧`. -/
theorem split_overlap :
    ∃ m₁ m₂ m,
      ResU.Lower (ResU.single 0 (cell sA)) m₁ ∧
      ResU.Lower (ResU.single 0 (cell sB)) m₂ ∧
      ResU.Lower (ResU.single 0 (cell (sA.union sB))) m ∧
      MemUnion m₁ m₂ m ∧ m₁ 0 = some 5 ∧ m₂ 0 = some 5 := by
  have hlow : ResU.Lower (ResU.single 0 (cell (sA.union sB)))
      (fun l => ((ResU.single 0 (cell (sA.union sB))).get l).map CellU.erase) :=
    ⟨_, flat_res (sA.union sB), fun _ => rfl⟩
  obtain ⟨m₁, m₂, k₁, k₂, ku⟩ := (ResU.Lower.split compS_res hash_res).mp hlow
  refine ⟨m₁, m₂, _, k₁, k₂, hlow, ku, ?_, ?_⟩
  · rw [ResU.Lower.functional k₁
      (show ResU.Lower (ResU.single 0 (cell sA)) _ from
        ⟨_, flat_res sA, fun _ => rfl⟩)]
    show ((ResU.single 0 (cell sA)).get 0).map CellU.erase = some 5
    rw [ResU.single_get_self]
    rfl
  · rw [ResU.Lower.functional k₂
      (show ResU.Lower (ResU.single 0 (cell sB)) _ from
        ⟨_, flat_res sB, fun _ => rfl⟩)]
    show ((ResU.single 0 (cell sB)).get 0).map CellU.erase = some 5
    rw [ResU.single_get_self]
    rfl

end
end LowerExample

/-! ## Added and bound hypotheses, inhabited -/

section Inhabited
variable {Loc Val : Type}

/-- `⦇ℓ ↦ own(v)⦈_○ = ℓ ↦ own(v)`: the `FlatR` hypothesis of `ResU.flatR_idem`
(`[TR]` Lemma 6.19), which binds it and does not use it, is satisfiable. -/
theorem ResU.flatR_single_own (l : Loc) (v : Val) :
    ResU.FlatR (ResU.single l (CellU.ownOf v)) (ResU.single l (CellU.ownOf v)) :=
  ⟨PMap.empty, ResU.single l (CellU.ownOf v),
    AgW.single_own l v, ExW.single_own l v, ResU.comp_empty_left _⟩

/-- `∅ # ℓ ↦ mut(α, v, ∅, ⊤)`: the `#` hypotheses of `[TR]` Lemmas 6.17 and
6.22–6.25 are inhabited at a `mut` cell. -/
theorem ResU.hash_empty_single_mut (l : Loc) (b : Life) (v : Val) :
    ResU.Hash (PMap.empty : ResU Loc Val) (ResU.single l
      (CellU.mutOf b v (PMap.empty : ResU Loc Val) (ResU.inStratum_empty b)
        (fun _ _ => True) trivial)) :=
  ResU.six23 (ResU.comp_empty_left _)
    ⟨ResU.Compat.of_disjoint (fun _ => Or.inl rfl), _, ResU.comp_empty_left _,
      ResU.valid_single_own l v⟩

/-- `EscrowAgree` is satisfiable: a resource agrees with itself. -/
theorem escrowAgree_self (χ ρ : ResU Loc Val) : EscrowAgree χ ρ ρ := by
  intro l v ψ ψf _ hρ hf _ _
  rw [Option.some.inj (hρ.symm.trans hf)]

/-- `EscrowAgree` in the shape 6.53 and 6.55 take it, quantified over the aliasable
walk of the frame, holds at every source with no `own` cell. -/
theorem escrowAgree_walk_of_no_own {χ : ResU Loc Val}
    (h : ∀ l ψ, χ.get l = some ψ → ψ.kind ≠ Kind.own) (ρ ρf : ResU Loc Val) :
    ∀ a, AgW ρf a → EscrowAgree χ ρ a :=
  fun a _ => escrowAgree_of_no_own h ρ a

end Inhabited

end BoCa.Fig16
