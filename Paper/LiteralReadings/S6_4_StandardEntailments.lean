import Paper.S5_Model.Definitions
import Support.Model.Notation
import Support.Model.Propositions

/-!
# Literal readings — [TR] §6.4

Measurements of §6.4's rules where the Lean adds a premise the printed statement
omits and the printed proof uses:

* 6.84 (`!l`): `bang_L_needs_premise`, the premise `P ⊨ Q` checked at the values
  where dropping it leaves `!P ⊨ Q` standing alone;
* 6.88 (`!∀`): `bang_all_needs_nonempty`, the index type the printed proof's
  *"Suppose `X ≠ ∅`"* excludes.

**How this file reads.**  Each run opens with the result it measures and says where
that result's record is.  Each declaration carries its tag; an
`[about ours: …]` tag names what is measured.  Nothing in the paper tree depends on
this file.
-/

noncomputable section

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
### Lemma 6.84 (!l) — literal reading

The printed statement, the printed proof and the adjudication are in `Paper/S6_4_StandardEntailments/Lemmas.lean`, under the record of Lemma 6.84 (!l).
-/
/-- **6.84's premise is not assumed.**  `bang_L` carries `P ⊨ Q`; read with the
free `Q` and no premise at all, the row would say `∀P Q. !P ⊨ Q`, and the
display's own `!P ≜ emp ∧ P` does not give that at `P ≜ emp` and `Q ≜ ⊥`.  So
the hypothesis is load-bearing rather than decoration, and it is discharged
rather than carried at the value 6.97 prints (`bang_L_dereliction`).
`[about ours: 6.84's added hypothesis, checked at the values where dropping it
would leave the entailment alone]` -/
theorem bang_L_needs_premise : ¬ ∀ (P Q : SPropU Loc Val), !ₛP ⊨ Q :=
  fun h => h emp bot PMap.empty ⟨emp_empty, emp_empty⟩

/-!
### Lemma 6.88 (!∀) — literal reading

The printed statement, the printed proof and the adjudication are in `Paper/S6_4_StandardEntailments/Lemmas.lean`, under the record of Lemma 6.88 (!∀).
-/
/-- 6.88's restriction is not assumed: at an empty index type the premise is
vacuous and the conclusion still demands `ρ = ∅`, so the printed statement fails
at any resource with a cell.
`[about ours: the printed 6.88 at the index type where it is false]` -/
theorem bang_all_needs_nonempty (l : Loc) (v : Val) :
    ¬ (all (fun _ : Empty => !ₛ(top : SPropU Loc Val)) ⊨
        !ₛ(all (fun _ : Empty => (top : SPropU Loc Val)))) := by
  intro h
  have hb := h (ResU.single l (CellU.ownOf v)) (fun x => x.elim)
  have hnone : (ResU.single l (CellU.ownOf v)).get l = none := by
    rw [hb.1.1]; rfl
  rw [ResU.single_get_self] at hnone
  exact absurd hnone (by simp)

end BoCa.Fig16.BoLo

end
