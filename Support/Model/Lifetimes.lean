import Paper.S5_Model.Definitions

/-!
# Support — Model — Lifetimes

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
facts about lifetimes and nonempty lifetime sets: commutativity, idempotence and associativity of `⊓` and `∪`, extensionality, extremal members and monotonicity of the meet.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa.Fig16

theorem Life.meet_comm (a b : Life) : a ⊓ b = b ⊓ a := inf_comm ..

theorem Life.meet_self (a : Life) : a ⊓ a = a := inf_idem ..

end BoCa.Fig16

namespace BoCa.Fig16.LSet

/-- The set determines `join` and `meet`; `LSet` is `℘⁺` with no extra data. -/
theorem ext {s t : LSet} (h : ∀ x, s.mem x ↔ t.mem x) : s = t := by
  have hm : s.mem = t.mem := funext fun x => propext (h x)
  have hlo : s.join = t.join :=
    Nat.le_antisymm (s.join_greatest _ ((h t.join).mpr t.join_mem))
      (t.join_greatest _ ((h s.join).mp s.join_mem))
  have hhi : s.meet = t.meet :=
    Nat.le_antisymm (t.meet_least _ ((h s.meet).mp s.meet_mem))
      (s.meet_least _ ((h t.meet).mpr t.meet_mem))
  cases s; cases t; cases hm; cases hlo; cases hhi; rfl

theorem union_comm (s t : LSet) : s.union t = t.union s :=
  ext fun _ => ⟨fun h => h.symm, fun h => h.symm⟩

theorem union_self (s : LSet) : s.union s = s :=
  ext fun _ => ⟨fun h => h.elim id id, Or.inl⟩

theorem union_assoc (s t u : LSet) : (s.union t).union u = s.union (t.union u) :=
  ext fun _ =>
    ⟨fun h => by
        rcases h with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h),
     fun h => by
        rcases h with h | (h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h⟩

end BoCa.Fig16.LSet

end
