import Paper.S5_Model.Definitions
import Support.Model.Cells
import Support.Model.Prelude

/-!
# [TR] §6.2 Non-standard Lemmas — the three printed Definitions  (pp. 9, 13, 17)

`[TR]` numbers its Definitions in a sequence of their own; all three fall in §6.2.

* **Definition 6.1** (p. 9).  Let `⦇ρ⦈_○ ≔ ag(ρ) ○ ex(ρ)_○`.
* **Definition 6.2** (p. 13).  Let `ψ ∼ ψ′ ≔ (ψ = mut(α, _, _, P̂) ∧ ψ′ = mut(α, _, _, P̂))
  ∨ (ψ = ψ′ = imm(α, v, ρ))`.
* **Definition 6.3** (p. 17).  `ρ ⊟ ρ′ ≜ ρ∣own,mut ● ρ″` where
  - `ρ′∣own,mut = ∅`;
  - `ρ″ ≤ ρ∣imm`;
  - if `ℓ ∈ dom(ρ∣imm) ∖ dom(ρ′)` then `ℓ ∈ dom(ρ″)`;
  - if `ℓ ∈ dom(ρ∣imm) ∩ dom(ρ′)` and `ρ(ℓ) = imm(α, ρᵢ, v)` and `ρ′(ℓ) = imm(β, ρᵢ, v)` then
    if `α ∖ β = ∅`, then `ℓ ∉ ρ″`; if `α ∖ β ≠ ∅`, then `ρ′(ℓ) = imm(α ∖ β, ρᵢ, v)`.

  *"Intuitively, `ρ ⊟ ρ′` is `ρ` without the immutable borrows in `ρ′`.  But since
  immutable borrows can alias at the same location, 'without' means removing the
  lifetimes of borrows from `ρ′`, but keeping the lifetimes only in `ρ`."*

`ResU.SubKeep` is Definition 6.3 read with that sentence, which fixes the cell
the third bullet leaves free and makes `⊟` a term (source `docs/boca-rules.md`
§12.64); `ResU.Sub` is the bullets alone, kept for comparison.

**How this file reads.**  Each printed item is a row of `[TR]`'s section, in the
order the page prints it, as far as Lean's definition-before-use allows; a row
that has to come earlier than printed does so because something printed before
it is defined through it.  Each row opens with a comment giving its number, the
printed form, the page, a tag, and the reason the Lean has the shape it has:

* `[as printed]` — the Lean is the printed item, symbol for symbol;
* `[encoding]` — it differs only by a representation choice that changes nothing
  (de Bruijn indices, a graph for a partial function, a list for a finite map);
* `[repair]` — it deliberately differs, and the comment gives the adjudication
  and the sentences of the paper that ground it;
* `[about ours]` — a declaration the paper does not print, placed here only
  because Lean needs it before the next printed row.

Row numbers are those of the source repository's `docs/definition-inventory.md`;
citations of `docs/…` and `BoCa/…` are to that repository (`borrow_lang` at
`970a9d0`).  Declaration names are the source's, unchanged, so that
`Bridge/Names.csv` can check each one against its original.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### 5.61 · `⦇ρ⦈_○ ≜ ag(ρ) ○ ex(ρ)_○` — [TR] Definition 6.1, not a p. 5 row · [TR] p. 9 · `[as printed]`

[TR] p. 9 prints it: "Definition 6.1. Let `⦇ρ⦈_○ ≜ ag(ρ) ○ ex(ρ)_○`."  Carried in this section because `ag`'s third piece calls `ex` at ○, and implemented as a graph, convention G4, like row 5.22's total flattening; the declaration carries `[as printed]`
-/
/-- `⦇ρ⦈_○ = σ` — `[TR]` Definition 6.1 (p. 9): `⦇ρ⦈_○ ≜ ag(ρ) ○ ex(ρ)_○`.
`[as printed]` (as a graph — G4) -/
def ResU.FlatR (ρ σ : ResU Loc Val) : Prop :=
  ∃ a e, AgW ρ a ∧ ExR ρ e ∧ ResU.CompR a e σ

/-!
### 5.65 · `ψ ∼ ψ′ ≔ (ψ = mut(α,_,_,P̂) ∧ ψ′ = mut(α,_,_,P̂)) ∨ (ψ = ψ′ = imm(ᾱ,v,ρ))` — [TR] Definition 6.2, not a p. 5 row · [TR] p. 13 · `[as printed]`

[TR] p. 13 prints it and then unfolds `↭` through it at Lemmas 6.39, 6.40, 6.44 and 6.59, always as "dom(⦇ρ₁⦈∣imm,mut) = dom(⦇ρ₂⦈∣imm,mut) and for every ℓ in that domain, ⦇ρ₁⦈(ℓ) ∼ ⦇ρ₂⦈(ℓ)". Read at 1200 dpi: α and P̂ are bound outside the `mut` conjunction and the two `_`s — value and witness — inside each conjunct, while the `imm` disjunct asks for equality outright, which is `BoCa.Fig16.ResU.UpdImm`/`UpdMut`'s asymmetry printed as one relation. `upd_iff_sim` is the bridge and it is a theorem: [CONF] Fig. 18b's two clauses and [TR] §6's `dom + ∼` form are the same relation, both flattenings named (G4). `ResU.borrowPart` is `ρ∣imm,mut`, the same printed coverage gap row 5.51 closes for `ρ∣own,mut`. [TR] Lemma 6.44's proof asserts `∼` is transitive "since imms are required to be equal and muts are required to have" the same lifetime and invariant; `CellU.Sim.trans` is that. **This definition had no row and no Lean declaration before this entry**, which is why [TR] §6's proofs had no printed route to follow
-/
/-- `ψ ∼ ψ′` — **`[TR]` Definition 6.2** (p. 13), read at 1200 dpi.

`α` and `P̂` are bound outside the `mut` conjunction and so are the same on both
sides, while the two `_`s — the value and the witness — are bound inside each
conjunct and may differ; the `imm` disjunct asks for equality outright.  That is
the asymmetry `ResU.UpdImm` and `ResU.UpdMut` carry clause by clause, printed
here as one relation.  An `own` cell is related to nothing, which is why the
printed uses restrict to `dom(−|imm,mut)`.  `[as printed]` -/
def CellU.Sim (ψ ψ' : CellU Loc Val) : Prop :=
  (∃ (a : Life) (P : Val → SPropS Loc Val a),
      (∃ (v : Val) (χ : ResU Loc Val) (h : χ.InStratum a) (hw : P v ⟨χ, h⟩),
          ψ = CellU.mutOf a v χ h P hw) ∧
      (∃ (v : Val) (χ : ResU Loc Val) (h : χ.InStratum a) (hw : P v ⟨χ, h⟩),
          ψ' = CellU.mutOf a v χ h P hw)) ∨
  (∃ (s : LSet) (v : Val) (χ : ResU Loc Val) (h : χ.InStratum s.join),
      ψ = CellU.immOf s v χ h ∧ ψ' = CellU.immOf s v χ h)

/-!
Row 5.65, continued.
-/
/-- `∼` is reflexive on a borrow cell — it relates no `own` cell, which is what
the printed uses' restriction to `dom(−|imm,mut)` is for. -/
theorem CellU.Sim.refl {ψ : CellU Loc Val} (hk : ψ.kind ≠ Kind.own) :
    CellU.Sim ψ ψ := by
  rcases CellU.rep ψ with ⟨v, rfl⟩ | ⟨s, v, χ, hh, rfl⟩ | ⟨b, v, χ, hh, P, hw, rfl⟩
  · exact absurd (by simp : (CellU.ownOf (Loc := Loc) v).kind = Kind.own) hk
  · exact Or.inr ⟨s, v, χ, hh, rfl, rfl⟩
  · exact Or.inl ⟨b, P, ⟨v, χ, hh, hw, rfl⟩, ⟨v, χ, hh, hw, rfl⟩⟩

/-!
Row 5.65, continued.
-/
/-- `ρ|imm,mut` — the borrow part, `ResU.exclPart`'s twin.  `[TR]` §6 uses it
from Lemma 6.39 on, in `dom(⦇ρ⦈|imm,mut)`, and p. 5's defining row gives only
the single-tag `ρ|ι`; this is the same printed coverage gap `ResU.exclPart`
closes.
`[variant: as `ResU.restrictOn`; no defining row is printed for the multi-tag
restriction]` -/
def ResU.borrowPart (ρ : ResU Loc Val) : ResU Loc Val :=
  ρ.restrictOn (fun k => !(k == Kind.own))

/-!
Row 5.65, continued.
-/
/-- The form `[TR]` §6's proofs unfold `↭` to, at two named flattenings (G4):
the `imm,mut` parts have the same domain, and at every location of it the two
cells are `∼`. -/
def ResU.SimForm (σ₁ σ₂ : ResU Loc Val) : Prop :=
  (∀ l : Loc, (∃ ψ, σ₁.borrowPart.get l = some ψ) ↔
      (∃ ψ, σ₂.borrowPart.get l = some ψ)) ∧
  (∀ (l : Loc) (ψ₁ : CellU Loc Val), σ₁.borrowPart.get l = some ψ₁ →
      ∃ ψ₂, σ₂.get l = some ψ₂ ∧ CellU.Sim ψ₁ ψ₂)

/-!
### 5.66 · `ρ ⊟ ρ′ ≜ ρ∣own,mut ● ρ″ where …` — [TR] Definition 6.3, not a p. 5 row · [TR] p. 17 · `[repair]`

The fourth bullet's second sub-case prints `ρ′(ℓ) = imm(ᾱ ∖ β̄, ρᵢ, v)` with a single prime, which its own hypothesis contradicts; `ρ″` is what [TR] Lemma 6.52's proof and the surrounding prose require. Adjudicated at `docs/boca-rules.md` §12.34, and `BoCa.Fig16.ResU.SubL` with `BoCa.Fig16.ResU.subClauseL_forces_empty` is the literal reading carried alongside, shown degenerate. The declaration existed with `[variant: …]` from the start; **the row did not**, so the definition layer had no record of it. **The third bullet is also short a clause**, and it is printed one line below the definition: *"removing the lifetimes of borrows from `ρ′`, but keeping the lifetimes only in `ρ`"*. Off `dom(ρ′)` every lifetime of `ρ(ℓ)` is one "only in `ρ`", so `ρ″(ℓ) = ρ(ℓ)` and not merely `ℓ ∈ dom(ρ″)`; `BoCa.Fig16.ResU.SubKeep` is the bullet read through that sentence and `BoCa.Fig16.ResU.SubKeep.toSub` the implication. On it `⊟` is a function (`BoCa.Fig16.ResU.SubKeep.functional`) — which is what licenses [TR]'s writing `ρ ⊟ ρ′` as a term — and [TR] 6.52's equation holds of every admissible value (`BoCa.Fig16.ResU.SubKeep.compS`). `BoCa.Fig16.ResU.sub_not_functional` measures the bullet's own glyphs, not `⊟`; adjudicated at `docs/boca-rules.md` §12.58, which is the correction to §12.38
-/
/-- The fourth bullet of `[TR]` Definition 6.3 (p. 17), with the second
sub-case read as a constraint on `ρ″`.
`[variant: the print writes `ρ′(ℓ) = imm(ᾱ ∖ β̄, ρᵢ, v)` with a single prime,
which its own hypothesis contradicts (§19); `ρ″` is what 6.52's proof and the
surrounding prose require]` -/
def ResU.SubClause (ρ ρ' ρ'' : ResU Loc Val) : Prop :=
  ∀ (l : Loc) (s s' : LSet) (v : Val) (ρi : ResU Loc Val)
    (h : ρi.InStratum s.join) (h' : ρi.InStratum s'.join),
    ρ.get l = some (CellU.immOf s v ρi h) →
    ρ'.get l = some (CellU.immOf s' v ρi h') →
    (LSet.DiffEmpty s s' → ρ''.get l = none) ∧
    (∀ u : LSet, LSet.Diff s s' u → ¬ LSet.DiffEmpty s s' →
        ∃ hu : ρi.InStratum u.join, ρ''.get l = some (CellU.immOf u v ρi hu))

/-!
Row 5.66, continued.
-/
/-- The same bullet of `[TR]` Definition 6.3 **as printed**: the second
sub-case constrains `ρ′`.  `[as printed]` -/
def ResU.SubClauseL (ρ ρ' ρ'' : ResU Loc Val) : Prop :=
  ∀ (l : Loc) (s s' : LSet) (v : Val) (ρi : ResU Loc Val)
    (h : ρi.InStratum s.join) (h' : ρi.InStratum s'.join),
    ρ.get l = some (CellU.immOf s v ρi h) →
    ρ'.get l = some (CellU.immOf s' v ρi h') →
    (LSet.DiffEmpty s s' → ρ''.get l = none) ∧
    (∀ u : LSet, LSet.Diff s s' u → ¬ LSet.DiffEmpty s s' →
        ∃ hu : ρi.InStratum u.join, ρ'.get l = some (CellU.immOf u v ρi hu))

/-!
Row 5.66, continued.
-/
/-- **Definition 6.3's bullets alone** — the third bullet at its own glyphs,
`ℓ ∈ dom(ρ″)`, without the paragraph one line below that says which cell stands
there.  That paragraph is part of the definition, so this is an **incomplete
transcription**, kept beside `ResU.SubKeep` — which is Definition 6.3 — for
comparison and as what `ResU.sub_not_functional` measures.  Prefer `SubKeep`
in new work.  `docs/boca-rules.md` §12.64.
`[variant: Definition 6.3's bullets without its paragraph; the last sub-case's
single prime is read as `ρ″`, see §19 and `ResU.subClauseL_forces_empty`]` -/
def ResU.Sub (ρ ρ' χ : ResU Loc Val) : Prop :=
  ∃ ρ'' : ResU Loc Val,
    ρ'.exclPart = PMap.empty ∧
    ResU.Le ρ'' (ρ.restrict Kind.imm) ∧
    (∀ l, (ρ.restrict Kind.imm).get l ≠ none → ρ'.get l = none → ρ''.get l ≠ none) ∧
    ResU.SubClause ρ ρ' ρ'' ∧
    ResU.CompS ρ.exclPart ρ'' χ

/-!
Row 5.66, continued.
-/
/-- `ρ ⊟ ρ′ = χ` — `[TR]` Definition 6.3 on the literal reading of the last
sub-case.  The sub-case itself is the print's, glyph for glyph, and so is `≤`
(`[CONF]` p. 415:24 fn. 1, §16).  The tag is not `[as printed]` for the one
remaining reason: the body restricts on **two** tags at once, `ρ|own,mut`, and
`[TR]` p. 5 prints `ρ|ι` with a single `ι`, so that operand has no defining row
on any page.
`[variant: `ρ|own,mut` restricts on two tags where the printed `ρ|ι` takes one,
and no document prints a defining row for it]` -/
def ResU.SubL (ρ ρ' χ : ResU Loc Val) : Prop :=
  ∃ ρ'' : ResU Loc Val,
    ρ'.exclPart = PMap.empty ∧
    ResU.Le ρ'' (ρ.restrict Kind.imm) ∧
    (∀ l, (ρ.restrict Kind.imm).get l ≠ none → ρ'.get l = none → ρ''.get l ≠ none) ∧
    ResU.SubClauseL ρ ρ' ρ'' ∧
    ResU.CompS ρ.exclPart ρ'' χ

/-!
Row 5.66, continued.
-/
/-- `ρ ⊟ ρ′ = χ` — `[TR]` Definition 6.3 with its **third bullet read through
the paragraph printed one line below it** (p. 17):

> *"Intuitively, `ρ ⊟ ρ′` is `ρ` without the immutable borrows in `ρ′`.  But
> since immutable borrows can alias at the same location, "without" means
> removing the lifetimes of borrows from `ρ′`, but keeping the lifetimes only in
> `ρ`."*

At a location `ρ′` does not cover, **every** lifetime of `ρ(ℓ)` is one "only in
`ρ`", so all of them are kept and `ρ″(ℓ)` is `ρ(ℓ)`.  The bullet's own glyphs
ask only `ℓ ∈ dom(ρ″)`, and `ResU.Sub` is those glyphs; the difference between
the two is exactly what `ResU.sub_not_functional` measures, and it is why `⊟`
can be written as a term — which the print does wherever it occurs.

The fourth bullet is as in `ResU.Sub`, on the `ρ″` reading of its single prime.

**This is Definition 6.3**, not a variant of it.  A definition is what the paper
says a thing is: the displayed bullets *together with* the paragraph that
disambiguates them.  Transcribing the bullets alone is an incomplete
transcription, not a faithful one, and completing it from the prose is not a
departure — `ResU.Sub` is the partial reading, kept beside this one for
comparison and for `ResU.sub_not_functional`.  `docs/boca-rules.md` §12.64.
`[as printed]` (`[TR]` p. 17, the four bullets and the paragraph one line below
them; the fourth bullet's single prime read as `ρ″`, as `ResU.Sub`) -/
def ResU.SubKeep (ρ ρ' χ : ResU Loc Val) : Prop :=
  ∃ ρ'' : ResU Loc Val,
    ρ'.exclPart = PMap.empty ∧
    ResU.Le ρ'' (ρ.restrict Kind.imm) ∧
    (∀ l, (ρ.restrict Kind.imm).get l ≠ none → ρ'.get l = none →
      ρ''.get l = (ρ.restrict Kind.imm).get l) ∧
    ResU.SubClause ρ ρ' ρ'' ∧
    ResU.CompS ρ.exclPart ρ'' χ

end BoCa.Fig16

end
