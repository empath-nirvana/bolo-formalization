import Paper.S5_Model.Definitions
import Paper.S6_4_StandardEntailments.Lemmas
import Support.Model.Algebra
import Support.Model.Lifetimes
import Support.Model.Notation
import Support.Model.Propositions
import Support.Model.Update

/-!
# Support — Model — Entailments

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
what §6.5–§6.6's entailments need beyond the propositions: `⫤⊨` reflexive and extensional, a `●`-factor of a reborrowed `imm` cell and the clauses that admit it, `reb_α` at `∅` and its outlives bound, and the join-indexed conclusion 6.115's literal reading measures.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- A `●`-factor of an `imm` cell is `imm` over a subset of its lifetime set, at
the same value and witness.  Clause (2) of `●` unions the sets.
`[about ours: the cell-level content of `[TR]` 6.43, read at one factor]` -/
theorem ResU.factor_imm_sub {ρ₁ ρ₂ ρ : ResU Loc Val} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    {l : Loc} {ψ₁ : CellU Loc Val} (h₁ : ρ₁.get l = some ψ₁)
    {s : LSet} {v : Val} {χ : ResU Loc Val} {hχ : χ.InStratum s.join}
    (he : ρ.get l = some (CellU.immOf s v χ hχ)) :
    ∃ (t : LSet) (ht : χ.InStratum t.join), (∀ x, t.mem x → s.mem x) ∧
      ρ₁.get l = some (CellU.immOf t v χ ht) := by
  rcases ResU.Comp.get hc l with ⟨f₁, -, -⟩ | ⟨φ, f₁, -, f⟩ | ⟨φ, f₁, -, -⟩ |
      ⟨φa, φb, φ, f₁, -, f, hC⟩
  · rw [h₁] at f₁; exact absurd f₁ (by simp)
  · rw [he] at f
    exact ⟨s, hχ, fun _ h => h, f₁.trans f.symm⟩
  · rw [h₁] at f₁; exact absurd f₁ (by simp)
  · rw [he] at f
    obtain rfl := Option.some.inj f
    obtain ⟨s₁, s₂, w, ζ, k₁, k₂, k₃, e₁, -, e₃⟩ := hC
    obtain ⟨rfl, rfl, rfl⟩ := CellU.immOf_inj e₃
    exact ⟨s₁, k₁, fun x hx => Or.inl hx, f₁.trans (congrArg some e₁)⟩

/-- A nonempty subset of `{α}` is `{α}`, so an `imm` cell over it is the cell
`reb_α` writes at `{α}`. -/
theorem immOf_sub_singleton {α : Life} {t : LSet} {v : Val} {χ : ResU Loc Val}
    {ht : χ.InStratum t.join} (hts : ∀ x, t.mem x → (LSet.singleton α).mem x)
    (h : χ.InStratum (LSet.singleton α).join) :
    CellU.immOf t v χ ht = CellU.immOf (LSet.singleton α) v χ h := by
  have e : t = LSet.singleton α := LSet.ext fun x =>
    ⟨hts x, fun hx => by
      have hj : t.join = α := hts _ t.join_mem
      show t.mem x
      rw [show x = α from hx, ← hj]; exact t.join_mem⟩
  subst e; rfl

/-- **`reb_α`'s body survives passing to a `●`-factor of the image**, at every
location that factor defines.  At the `own` and `mut` clauses the image cell is
`imm({α}, …)` and a factor of it is the same cell (`immOf_sub_singleton`); at
the `imm` clause a factor is `imm` over a subset of a subset.  This is `[TR]`
6.127's closing substitution `ρ′ → ρ′₁` inside `F`.
`[about ours: the `ρ′` half of `[TR]` 6.127's closing sentence, at our `reb_α`]` -/
theorem ResU.RebAt.factor {α : Life} {ρ ρ' ρ'₁ ρ'₂ : ResU Loc Val} {l : Loc}
    {p : ResU Loc Val} (h : ResU.RebAt α ρ ρ' l p) (hc : ResU.CompS ρ'₁ ρ'₂ ρ')
    {ψ : CellU Loc Val} (hψ : ρ'₁.get l = some ψ) : ResU.RebAt α ρ ρ'₁ l p := by
  refine ⟨h.1, fun v hv => ?_, fun b v χ hb P hw hm => ?_, fun s v χ hs hm => ?_⟩
  · obtain ⟨hh, he⟩ := h.2.1 v hv
    obtain ⟨t, ht, hts, e⟩ := ResU.factor_imm_sub hc hψ he
    exact ⟨hh, e.trans (congrArg some (immOf_sub_singleton hts hh))⟩
  · obtain ⟨⟨hh, he⟩, hd⟩ := h.2.2.1 b v χ hb P hw hm
    obtain ⟨t, ht, hts, e⟩ := ResU.factor_imm_sub hc hψ he
    exact ⟨⟨hh, e.trans (congrArg some (immOf_sub_singleton hts hh))⟩, hd⟩
  · obtain ⟨⟨t, ht, hts, he⟩, hd⟩ := h.2.2.2 s v χ hs hm
    obtain ⟨t', ht', hts', e⟩ := ResU.factor_imm_sub hc hψ he
    exact ⟨⟨t', ht', fun x hx => hts x (hts' x hx), e⟩, hd⟩

end BoCa.Fig16

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

theorem BiEntails.refl (P : SPropU Loc Val) : P ⫤⊨ P := ⟨Entails.refl P, Entails.refl P⟩

/-- Two propositions that entail each other are equal — `propext` and `funext`.
Used by `ptoMut_inv`, where the cell stores the invariant itself. -/
theorem eq_of_biEntails {P Q : SPropU Loc Val} (h : P ⫤⊨ Q) : P = Q :=
  funext fun ρ => propext ⟨fun k => h.1 ρ k, fun k => h.2 ρ k⟩

end BoCa.Fig16.BoLo

namespace BoCa.Fig16.BoLo

/-- `[TR]` 6.115 at the printed index `α ⊔ β`, over our `ptoImm`.
`[about ours: 6.115's printed conclusion index over the connective at `⊓β̄`]` -/
def IAgreeAtJoin : Prop :=
  ∀ (l : Nat) (α β : Life) (P Q : Nat → SPropU Nat Nat),
    (ptoImm l α P ⋆ ptoImm l β Q) ⊨ ptoImm l (α ⊔ β) (fun v => and (P v) (Q v))

end BoCa.Fig16.BoLo

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-- "To start, it only holds of resources `ρ` that live longer than `α`"
([CONF] §4.4, p. 415:23): `reb_α`'s first conjunct is `[α]`'s own. -/
theorem reborrow_outlives (α : Life) (P : SPropU Loc Val) :
    reborrow α P ⊨ (fun ρ => Outlives ρ α) := by
  rintro ρ ⟨ρ', ⟨ho, -⟩, -⟩
  exact ho

end BoCa.Fig16.BoLo

namespace BoCa.Fig16.BoLo

/-- The singleton family `π = [(ℓ, p)]` has `(ℓ, p)` for its only member. -/
theorem memSingle {A B : Type} {a a' : A} {b b' : B} (hm : (a, b) ∈ [(a', b')]) :
    a = a' ∧ b = b' := by
  have he := List.mem_singleton.mp hm
  exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩

end BoCa.Fig16.BoLo

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-- `∅ ∈ reb_α(∅)`, at every `α` — `π` is empty, so none of `reb_α`'s three
implications is exercised, and its leading `@∅ ⊐ α` is the one `[TR]` 6.124
(p. 33) closes "by definition": `∅` carries no borrow cell. -/
theorem reb_empty (α : Life) :
    ResU.Reb α (PMap.empty : ResU Loc Val) PMap.empty := by
  refine ⟨fun l ψ e => absurd e (by simp), [], PMap.empty, ⟨by simp, fun l => ?_⟩,
    BigComp.nil, ResU.Le.refl _, fun l p hm => absurd hm (by simp)⟩
  simp

end BoCa.Fig16.BoLo

end
