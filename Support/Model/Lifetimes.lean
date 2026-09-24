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

theorem Life.top_sqsubseteq (a : Life) : a ⊑ ⊤ := le_top

theorem Life.meet_comm (a b : Life) : a ⊓ b = b ⊓ a := inf_comm ..

theorem Life.meet_self (a : Life) : a ⊓ a = a := inf_idem ..

end BoCa.Fig16

namespace BoCa.Fig16.LSet

/-- **A subset has the longer meet.**  `⊓ᾱ₁` is a member of `ᾱ₁` and so of
`ᾱ`, which `⊓ᾱ` lies below; extra members can only drag a meet down. -/
theorem meet_mono_of_subset {s₁ s : LSet} (h : ∀ x, s₁.mem x → s.mem x) :
    s.meet ⊑ s₁.meet :=
  s.meet_least _ (h _ s₁.meet_mem)

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

theorem exists_greatest (s : Nat → Prop) :
    ∀ n : Nat, (∃ x, s x) → (∀ x, s x → x ≤ n) → ∃ m, s m ∧ ∀ x, s x → x ≤ m
  | 0, ⟨a, ha⟩, hb => ⟨a, ha, fun x hx => by have h₁ := hb x hx; have h₂ := hb a ha; omega⟩
  | n + 1, hne, hb => by
      by_cases h : s (n + 1)
      · exact ⟨n + 1, h, hb⟩
      · refine exists_greatest s n hne (fun x hx => ?_)
        have h₁ := hb x hx
        have h₂ : x ≠ n + 1 := fun e => h (e ▸ hx)
        omega

theorem exists_least (s : Nat → Prop) :
    ∀ n : Nat, (∃ x, s x ∧ x ≤ n) → ∃ m, s m ∧ ∀ x, s x → m ≤ x
  | 0, ⟨a, ha, hle⟩ => ⟨a, ha, fun x _ => by omega⟩
  | n + 1, ⟨a, ha, hle⟩ => by
      by_cases h : ∃ x, s x ∧ x ≤ n
      · exact exists_least s n h
      · refine ⟨a, ha, fun x hx => ?_⟩
        have h₁ : ¬ x ≤ n := fun e => h ⟨x, hx, e⟩
        have h₂ : ¬ a ≤ n := fun e => h ⟨a, ha, e⟩
        omega

/-- Conversely, an `LSet` is a nonempty set of lifetimes. -/
theorem nonempty (t : LSet) : ∃ a, t.mem a := ⟨t.join, t.join_mem⟩

end BoCa.Fig16.LSet

end
