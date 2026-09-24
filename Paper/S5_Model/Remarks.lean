import Paper.S1_Syntax.Definitions
import Paper.S3_Dynamics.Definitions
import Paper.S5_Model.Definitions
import Support.Dynamics.Machine
import Support.Model.Algebra
import Support.Model.Ancestors
import Support.Model.Cells
import Support.Model.Compatibility
import Support.Model.Composition
import Support.Model.Flattening
import Support.Model.Prelude
import Support.Model.Propositions
import Support.Model.WalkSplitting
import Support.Model.Walks

/-!
# [TR] §5 Model — remarks on the definitions

Row 5.62's `wp_eq_wpU` (the two printed readings of `↭` give the same `wp`),
row 5.56's `BigComp.perm` (`⨀` is order-independent), and row 5.67's theorems
(`[CONF]`'s prose characterisation of `✓`).

These are theorems about printed definitions — rows of the source's
`docs/definition-inventory.md` whose Lean is a theorem — whose proofs use results
of `[TR]` §6, so they cannot sit with the definitions.  Each carries the row's
number, printed form, page, tag and note.  A row's theorem that a §6 result's Lean
needs is declared in that result's file, and the row here says where.
-/

noncomputable section

/-!
### 5.56 · `⨀` — the iterated composition, with no printed empty case · [TR] p. 5, rows 11, 12, 19 · `[repair]`

The fold behind the printed large operator. The empty case is printed nowhere, and without it `ex(ρ)_◖` would have no value on any mut-free ρ — so `✓ρ` on the simplest resources depends on it; `BoCa.Fig16.BigComp.perm` makes the fold order irrelevant. Adjudicated at `BoCa/Fig16.lean` §16: the empty case is necessary and not convenient — neither document prints it, and without it `ex(ρ)_◖` has no value on any mut-free ρ — and `BoCa.Fig16.BigComp.perm` discharges the order-independence out of [TR] Lemmas 6.1–6.3 instead of assuming it

`BoCa.Fig16.BigComp.perm` is declared in `Paper/S6_2_NonStandardLemmas/Remarks.lean`, ahead of this file: the Lean of row 5.65's theorem there uses it.
-/

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### 5.67 · — [CONF] §4.3's characterisation of `✓`: *"in a valid resource, every pair of aliases map to the same object and each has an immutable ancestor"*, and *"aliasing of exclusive locations … not guarded by immutable cells … violates the mutability-xor-aliasing restriction"* — · [CONF] p. 415:21, not in [TR] §5 · `[as printed]`

Prose, not a defining row, and it characterises an object that already has one — `✓ρ ≜ ⦇ρ⦈ defined` (row 5.59). [CONF] p. 415:21 says the enforcement is composition itself and nothing more: *"the advantage of reusing composition is that it already rules out all of the inconsistent aliasing cases"*, and names the mechanism — *"the conflict at `ℓ₁` causes `•` and therefore `E•` to be undefined, while the conflict at `ℓ₂` causes `◦` and therefore `A` to be undefined"*. So there is nothing extra to transcribe, and the three clauses are already theorems: *same object* is `CellU.compatR_iff`, proved as an **iff** (`▷◁ ⟺ a common value, and a common witness wherever there is one to share`), with `CellU.CompatS.imm_imm` at `●`; *an immutable ancestor* is `AgW.nonimm_beneath_imm` with `ExW.immFree` (6.36); *no cell both exclusive and aliasable* is `ResU.CompatS.disjoint_of_immFree` and `ResU.flat_eq_ag_at`. The row exists because the prose was uncited for the whole of `[TR]` §6's development; `docs/boca-rules.md` §12.52 assembles it and records what it does **not** say
-/
/-- `[TR]` Lemma 6.36 (p. 12): if `ex(ρ)_◐` is defined then `ex(ρ)_◐|imm = ∅`.
The hypothesis `hC` names the print's schematic operator and is discharged
outright at both of its values, by `CellU.compS_ne_imm` and
`CellU.compR_ne_imm`.  `ResU.restrict_imm_empty_iff` is `ρ|imm = ∅` written
pointwise.
`[as printed]` -/
theorem ExW.immFree {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ₁.kind ≠ Kind.imm → ψ₂.kind ≠ Kind.imm →
        ψ.kind ≠ Kind.imm)
    {ρ σ : ResU Loc Val} (h : ExW R C ρ σ) : σ.ImmFree := by
  induction h using ExW.rec
    (motive_2 := fun _ w _ => ∀ p ∈ w, ResU.ImmFree p.2)
  case mk ρ' σ' nm b w hs hw hb hnm hσ ih =>
      refine ResU.ImmFree.comp hC hσ
        (ResU.ImmFree.comp hC hnm (ResU.immFree_restrict (fun e => Kind.noConfusion e))
          (ResU.immFree_restrict (fun e => Kind.noConfusion e)))
        (ResU.ImmFree.bigComp hC hb ?_)
      intro e he
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
      exact ih p hp
  case nil ρ' p hp =>
      exact absurd hp (by simp)
  case cons ρ' e l w ψ hψ hk he hw ihe ihw p hp =>
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ihe
      · exact ihw p hp

/-! `[about ours]` — what the Lean of row 5.62's theorem needs; the paper prints nothing here. -/
/-- `[TR]` Lemma 6.36 at `●`, which is the value `[CONF]` Fig. 18a's `E⦇ρ′⦈_•`
names.  This performs the discharge of `ExW.immFree`'s `hC`, by
`CellU.compS_ne_imm`.  `[as printed]` -/
theorem ExS.immFree {ρ σ : ResU Loc Val} (h : ExS ρ σ) : σ.ImmFree :=
  ExW.immFree (fun ψ₁ ψ₂ ψ hc h₁ _ => CellU.compS_ne_imm ψ₁ ψ₂ ψ hc h₁) h

/-!
Row 5.67, continued.
-/
/-- `▸◂` with an `imm`-free resource is outright disjointness — the print's
first sentence.  `▸◂` relates `imm` cells only, so a shared location would put
an `imm` cell in `ρ`.
`[about ours: the step "Since ρ|imm = ∅, ρ ▸◂ ρ′ implies dom(ρ) ∩ dom(ρ′) = ∅"
of `[TR]` Lemma 6.30's proof, with `dom` written pointwise]` -/
theorem ResU.CompatS.disjoint_of_immFree {ρ ρ' : ResU Loc Val}
    (himm : ρ.ImmFree) (h : ResU.CompatS ρ ρ') (l : Loc) :
    ρ.get l = none ∨ ρ'.get l = none := by
  cases e : ρ.get l with
  | none => exact Or.inl rfl
  | some ψ =>
      cases e' : ρ'.get l with
      | none => exact Or.inr rfl
      | some ψ' => exact absurd (CellU.CompatS.kinds (h l ψ ψ' e e')).1 (himm l ψ e)

/-! `[about ours]` — what the Lean of row 5.62's theorem needs; the paper prints nothing here. -/
/-- **`[TR]` Lemma 6.30** (p. 11): if `ρ ▸◂ (ρ₁ ○ ρ₂)` and `ρ|imm = ∅` then
`ρ ▸◂ ρ₁` and `ρ ▸◂ ρ₂`.  The proof is the print's: `ρ|imm = ∅` turns the
hypothesis into disjointness from the composite, the composite's domain is the
union of the operands' domains, so `ρ` is disjoint from each operand, and
disjoint resources are compatible.  `ρ|imm = ∅` is carried literally, as §12's
`ResU.restrict` against `PMap.empty`; `ResU.restrict_imm_empty_iff` (§17) turns
it into the pointwise `ResU.ImmFree` inside the proof.
`[as printed]` (the printed `ρ₁ ○ ρ₂` appears as its graph — G4) -/
theorem ResU.CompatS.of_compR_left {ρ ρ₁ ρ₂ r : ResU Loc Val}
    (himm : ρ.restrict Kind.imm = PMap.empty)
    (hr : ResU.CompR ρ₁ ρ₂ r) (h : ResU.CompatS ρ r) :
    ResU.CompatS ρ ρ₁ ∧ ResU.CompatS ρ ρ₂ := by
  have hfree : ρ.ImmFree := (ResU.restrict_imm_empty_iff ρ).mp himm
  have hdisj := ResU.CompatS.disjoint_of_immFree hfree h
  refine ⟨ResU.Compat.of_disjoint fun l => ?_, ResU.Compat.of_disjoint fun l => ?_⟩ <;>
    rcases hdisj l with e | e
  · exact Or.inl e
  · exact Or.inr ((ResU.Comp.eq_none_iff hr l).mp e).1
  · exact Or.inl e
  · exact Or.inr ((ResU.Comp.eq_none_iff hr l).mp e).2

/-- 6.35's "by the previous constraint": if an `imm`-free composite is `▸◂`
something, so is each of its factors.  Being `imm`-free the composite is
disjoint from that something, and a factor's domain sits inside the
composite's.
`[about ours: the second of the composability constraints `[TR]` Lemma 6.35's
proof lists, with `dom` written pointwise]` -/
theorem ResU.CompatS.of_compS_left_immFree {ρ₁ ρ₂ ρ σ : ResU Loc Val}
    (himm : ρ.ImmFree) (h : ResU.CompS ρ₁ ρ₂ ρ) (hc : ResU.CompatS ρ σ) :
    ResU.CompatS ρ₁ σ ∧ ResU.CompatS ρ₂ σ := by
  have hdisj := ResU.CompatS.disjoint_of_immFree himm hc
  refine ⟨ResU.Compat.of_disjoint fun l => ?_, ResU.Compat.of_disjoint fun l => ?_⟩ <;>
    rcases hdisj l with e | e
  · exact Or.inl ((ResU.Comp.eq_none_iff h l).mp e).1
  · exact Or.inr e
  · exact Or.inl ((ResU.Comp.eq_none_iff h l).mp e).2
  · exact Or.inr e

/-- **The display and the composability constraints of `[TR]` Lemma 6.35's
proof** (p. 12).  From `⦇ρ₁ ● ρ₂⦈ = σ` it returns the printed factorisation
`ex(ρ₁)_● ● ex(ρ₂)_● ● (ag(ρ₁) ○ ag(ρ₂))` — 6.18 and 6.20 through
`ResU.Flat.split` (§20b) — together with the two composites
`ex(ρᵢ)_● ● ag(ρᵢ)` that 6.30 and 6.36 show are defined.  Those two are `⦇ρ₁⦈`
and `⦇ρ₂⦈`, so this is 6.35 with its intermediate values still in hand, which
is what 6.7 needs of it.
`[about ours: the body of `[TR]` Lemma 6.35's proof, stated with the walks and
the compositions as graphs (G4) so that its intermediate values survive]` -/
theorem ResU.Flat.split_factors {ρ₁ ρ₂ ρ₁₂ σ : ResU Loc Val}
    (h : ResU.CompS ρ₁ ρ₂ ρ₁₂) (hσ : ResU.Flat ρ₁₂ σ) :
    ∃ e₁ e₂ e a₁ a₂ a σ₁ σ₂,
      ExS ρ₁ e₁ ∧ ExS ρ₂ e₂ ∧ ResU.CompS e₁ e₂ e ∧
      AgW ρ₁ a₁ ∧ AgW ρ₂ a₂ ∧ ResU.CompR a₁ a₂ a ∧ ResU.CompS e a σ ∧
      ResU.CompS e₁ a₁ σ₁ ∧ ResU.CompS e₂ a₂ σ₂ := by
  obtain ⟨e₁, e₂, e, a₁, a₂, a, he₁, he₂, hec, ha₁, ha₂, hac, hc⟩ :=
    (ResU.Flat.split h).mp hσ
  -- `(ex(ρ₁)_● ● ex(ρ₂)_●)|imm = ∅`, by 6.36 at each factor.
  have himm : e.ImmFree := ResU.ImmFree.compS hec (ExS.immFree he₁) (ExS.immFree he₂)
  -- `ex(ρ₁)_● ● ex(ρ₂)_● ▸◂ ag(ρᵢ)`, by 6.30 on `ag(ρ₁) ○ ag(ρ₂)`.
  obtain ⟨hca₁, hca₂⟩ :=
    ResU.CompatS.of_compR_left ((ResU.restrict_imm_empty_iff e).mpr himm) hac hc.1
  -- `ex(ρᵢ)_● ▸◂ ag(ρᵢ)`, "by the previous constraint".
  obtain ⟨hd₁, -⟩ := ResU.CompatS.of_compS_left_immFree himm hec hca₁
  obtain ⟨-, hd₂⟩ := ResU.CompatS.of_compS_left_immFree himm hec hca₂
  -- …"which implies `⦇ρᵢ⦈` is defined", by 6.9.
  obtain ⟨σ₁, hσ₁⟩ := (ResU.compS_defined_iff e₁ a₁).mpr hd₁
  obtain ⟨σ₂, hσ₂⟩ := (ResU.compS_defined_iff e₂ a₂).mpr hd₂
  exact ⟨e₁, e₂, e, a₁, a₂, a, σ₁, σ₂, he₁, he₂, hec, ha₁, ha₂, hac, hc, hσ₁, hσ₂⟩

/-- **`[TR]` Lemma 6.10** (p. 7) — equivalently **`[TR]` Lemma 6.35** (p. 12).
6.10 reads *if `✓(ρ₁ ● ρ₂)` then `✓ρ₁` and `✓ρ₂`*; 6.35 reads *if `⦇ρ ● ρ′⦈` is
defined then `⦇ρ⦈` and `⦇ρ′⦈` are defined*.  p. 5's table has the row
`✓ρ ≜ ⦇ρ⦈ defined`, which is `ResU.Valid`, so the two lines are one proposition
and this single declaration is both of them.  The proof is 6.35's, the longer of
the two printed ones, run through `ResU.Flat.split_factors`.
`[as printed]` (both of them; the printed `ρ₁ ● ρ₂` appears as its graph — G4) -/
theorem ResU.Valid.split {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    (hv : ρ.Valid) : ρ₁.Valid ∧ ρ₂.Valid := by
  obtain ⟨σ, hσ⟩ := hv
  obtain ⟨e₁, e₂, e, a₁, a₂, a, σ₁, σ₂, he₁, he₂, -, ha₁, ha₂, -, -, hσ₁, hσ₂⟩ :=
    ResU.Flat.split_factors h hσ
  exact ⟨⟨σ₁, e₁, a₁, he₁, ha₁, hσ₁⟩, ⟨σ₂, e₂, a₂, he₂, ha₂, hσ₂⟩⟩

/-- **`[TR]` Lemma 6.11** (p. 7): if `ρ₁ ● ρ₂ # ρ₃` then `ρ₁ # ρ₃` and
`ρ₂ # ρ₃`.  The print's two halves are the two conjuncts of `#`.  "Definedness
of `ρ₁ ● ρ₃` and `ρ₂ ● ρ₃` follow from unfolding definitions" is 6.3
(`ResU.CompS.assoc`, §20) regrouping `(ρ₁ ● ρ₂) ● ρ₃` as `ρ₁ ● (ρ₂ ● ρ₃)` and —
after 6.2 — as `ρ₂ ● (ρ₁ ● ρ₃)`, each regrouping carrying the inner composite's
own `▸◂` as its first conjunct.  "`✓(ρ₁ ● ρ₃)` and `✓(ρ₂ ● ρ₃)` follow from
theorem 6.10 applied to `✓(ρ₁ ● ρ₂ ● ρ₃)`" is `ResU.Valid.split` at each
regrouping.
`[as printed]` (the printed `ρ₁ ● ρ₂` appears as its graph — G4) -/
theorem ResU.Hash.split {ρ₁ ρ₂ ρ₁₂ ρ₃ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ₁₂)
    (hh : ResU.Hash ρ₁₂ ρ₃) : ResU.Hash ρ₁ ρ₃ ∧ ResU.Hash ρ₂ ρ₃ := by
  obtain ⟨-, ρ, hρ, hv⟩ := hh
  obtain ⟨x, hx, hρx⟩ := (ResU.CompS.assoc ρ₁ ρ₂ ρ₃ ρ).mpr ⟨ρ₁₂, h, hρ⟩
  obtain ⟨y, hy, hρy⟩ := (ResU.CompS.assoc ρ₂ ρ₁ ρ₃ ρ).mpr ⟨ρ₁₂, ResU.CompS.comm h, hρ⟩
  exact ⟨⟨hy.1, y, hy, (ResU.Valid.split hρy hv).2⟩,
    ⟨hx.1, x, hx, (ResU.Valid.split hρx hv).2⟩⟩

end BoCa.Fig16

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-- `ρ₁ # ρ₂` gives `✓ρ₁` and `✓ρ₂` — `[TR]` Lemma 6.10 at the composite `#`
asserts is valid.  `[as printed]` (6.10, at the bundled `#`) -/
theorem hash_valid {ρ₁ ρ₂ : WRes} (h : ResU.Hash ρ₁ ρ₂) :
    ResU.Valid ρ₁ ∧ ResU.Valid ρ₂ := by
  obtain ⟨σ, hσ, hv⟩ := h.2
  exact ResU.Valid.split hσ hv

/-- **The two readings of `↭` agree inside the row.**  `ResU.UpdV` is
`ResU.Upd` with `✓` on each side, and the row already asserts both: `✓ρ` is the
printed `ρ_f # ρ` through `[TR]` Lemma 6.10, and `✓(ρ′ ● ρ⁺)` is the printed
`ρ⁺ # (ρ_f ● ρ′)` through `[TR]` Lemma 6.11.  So ledger D3 does not separate the two
documents here.  `[about ours: the two printed `↭`s, read inside the printed
row]` -/
theorem wp_updV_iff_upd (e : Expr) (Q : Val → WProp) (ρ : WRes) :
    wp e Q ρ ↔ wpU e Q ρ := by
  constructor
  · intro hw ρf hf
    obtain ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
      hA, hB, hC⟩ := hw ρf hf
    exact ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
      hA.1, hB, hC⟩
  · intro hw ρf hf
    obtain ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
      hA, hB, hC⟩ := hw ρf hf
    obtain ⟨-, hp'⟩ := ResU.Hash.split h₂ (ResU.hash_symm h₃)
    exact ⟨ρ', ρp, fρ, fρ', fρ'p, π, v, μ, μ', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
      ⟨hA, (hash_valid hf).2, hash_valid_comp hp' h₉⟩, hB, hC⟩

/-!
### 5.62 · — [CONF] Fig. 18b's unguarded ↭, and the `wp` row read at it — · not in [TR] §5 · `[repair]`

The second printed reading of ↭ (`docs/axiom-ledger.md` D3), kept alongside [TR]'s; `BoCa.Fig16.BoLo.wp_eq_wpU` proves the two readings give the same `SProp` inside the `wp` row, so nothing downstream has to choose. Adjudicated at `docs/axiom-ledger.md` D3 with `BoCa/Fig16.lean` §20e and `BoCa/Fig16Wp.lean` §2: both readings of ↭ are printed rows in the same documents, so both are carried and the choice is closed by proof rather than fiat — `BoCa.Fig16.BoLo.wp_eq_wpU` shows [TR]'s two guards follow from the `#`s that `wp` already quantifies over — and what survives away from `wp` is named. `BoCa.Fig16.ResU.Upd` is itself `[as printed]` against [CONF] Fig. 18b, so this row bundles a printed item with two declarations of ours
-/
/-- …and hence the two readings are the same `SProp`.
`[about ours: the equality of the two printed readings]` -/
theorem wp_eq_wpU (e : Expr) (Q : Val → WProp) : wp e Q = wpU e Q :=
  funext fun ρ => propext (wp_updV_iff_upd e Q ρ)

end BoCa.Fig16.BoLo

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
Row 5.67, continued.
-/
/-- **`⋈` is exactly "a common value, and a common witness wherever there is one
to share".**  Left to right is `CellU.CompR.erase` and `CellU.CompR.wit` (§13);
right to left is the case analysis over the two tags that p. 5's five clauses
decide, one clause per pair of tags — `own` against anything is (1), (4) or (5),
two `imm` cells over one witness are (2), two `mut` cells over one witness are
(3), and an `imm` against a `mut` over one witness is (5).

The second conjunct is the wrinkle `[TR]` Lemma 6.14's proof names, and the
right-to-left direction is what that proof spends: `○` merges an `imm` cell with
an own-or-mut cell "only when the given own-or-mut cell has the same value and
subresource inside of it", and here that condition is not merely necessary but
sufficient, so a composite that inherits it is `⋈` whatever the operand was.
`[about ours: §15's `⋈`, which is `[TR]` p. 5's printed second disjunct on the
reading argued there, in the projections of §7 and §13]` -/
theorem CellU.compatR_iff {ψ₁ ψ₂ : CellU Loc Val} :
    CellU.CompatR ψ₁ ψ₂ ↔
      (ψ₁.erase = ψ₂.erase ∧
        (ψ₁.kind ≠ Kind.own → ψ₂.kind ≠ Kind.own → ψ₁.wit = ψ₂.wit)) := by
  constructor
  · rintro ⟨ψ, h⟩
    exact ⟨(CellU.CompR.erase h).1, fun k₁ k₂ => CellU.CompR.wit h k₁ k₂⟩
  · rintro ⟨hv, hw⟩
    rcases CellU.rep ψ₁ with ⟨v₁, rfl⟩ | ⟨s₁, v₁, τ₁, m₁, rfl⟩ |
        ⟨b₁, v₁, τ₁, m₁, P₁, w₁, rfl⟩ <;>
      rcases CellU.rep ψ₂ with ⟨v₂, rfl⟩ | ⟨s₂, v₂, τ₂, m₂, rfl⟩ |
        ⟨b₂, v₂, τ₂, m₂, P₂, w₂, rfl⟩ <;>
      simp only [CellU.erase_ownOf, CellU.erase_immOf, CellU.erase_mutOf] at hv <;>
      subst hv
    -- `own` on the left: clauses (1), (5) and (4), which ask only for the value.
    · exact ⟨_, CellU.CompR.same _⟩
    · exact ⟨_, CellU.CompR.ownImm s₂ _ τ₂ m₂⟩
    · exact ⟨_, CellU.CompR.ownMut b₂ _ τ₂ m₂ P₂ w₂⟩
    -- `imm` on the left: clause (5) against `own`, then (2) and (5), which ask
    -- for the witness as well.
    · exact ⟨_, CellU.CompR.immOwn s₁ _ τ₁ m₁⟩
    · have hτ : τ₁ = τ₂ := by
        have hww := hw (by simp) (by simp)
        rwa [CellU.wit_immOf, CellU.wit_immOf] at hww
      subst hτ
      exact ⟨_, CellU.CompR.strict ⟨s₁, s₂, _, τ₁, m₁, m₂, rfl, rfl⟩⟩
    · have hτ : τ₁ = τ₂ := by
        have hww := hw (by simp) (by simp)
        rwa [CellU.wit_immOf, CellU.wit_mutOf] at hww
      subst hτ
      exact ⟨_, CellU.CompR.immMut s₁ _ τ₁ m₁ b₂ m₂ P₂ w₂⟩
    -- `mut` on the left: clause (4) against `own`, then (5) and (3).
    · exact ⟨_, CellU.CompR.mutOwn b₁ _ τ₁ m₁ P₁ w₁⟩
    · have hτ : τ₁ = τ₂ := by
        have hww := hw (by simp) (by simp)
        rwa [CellU.wit_mutOf, CellU.wit_immOf] at hww
      subst hτ
      exact ⟨_, CellU.CompR.mutImm s₂ _ τ₁ m₂ b₁ m₁ P₁ w₁⟩
    · have hτ : τ₁ = τ₂ := by
        have hww := hw (by simp) (by simp)
        rwa [CellU.wit_mutOf, CellU.wit_mutOf] at hww
      subst hτ
      exact ⟨_, CellU.CompR.mutMut b₁ b₂ _ τ₁ m₁ m₂ P₁ P₂ w₁ w₂⟩

/-!
Row 5.67, continued.
-/
/-- **Where `ag(ρ)` carries a cell that is not `imm`, `⦇ρ⦈` carries that very
cell.**  `⦇ρ⦈ ≜ ex(ρ)● ● ag(ρ)` and `▶◀` holds only between two `imm` cells, so
the exclusive walk is silent there and the outer `●` returns the aliasable
walk's cell unchanged (`ResU.ex_none_of_ag_ne_imm` says the first half on its
own, further down).
`[about ours: `⦇ρ⦈` at a non-`imm` cell of `ag(ρ)`]` -/
theorem ResU.flat_eq_ag_at {ρ e a σ : ResU Loc Val} (_he : ExS ρ e)
    (hc : ResU.CompS e a σ) {n : Loc} {ψ : CellU Loc Val} (hg : a.get n = some ψ)
    (hk : ψ.kind ≠ Kind.imm) : σ.get n = some ψ := by
  have hen : e.get n = none := by
    cases f : e.get n with
    | none => rfl
    | some ξ => exact absurd (CellU.CompatS.kinds (hc.1 n ξ ψ f hg)).2 hk
  rcases ResU.Comp.get hc n with ⟨-, f₂, -⟩ | ⟨ξ, f₁, -, -⟩ | ⟨ξ, -, f₂, f⟩ |
      ⟨ξ₁, ξ₂, ξ, f₁, -, -, -⟩
  · rw [hg] at f₂; exact absurd f₂ (by simp)
  · rw [hen] at f₁; exact absurd f₁ (by simp)
  · rw [hg] at f₂; rw [f, Option.some.inj f₂]
  · rw [hen] at f₁; exact absurd f₁ (by simp)

/-!
Row 5.67, continued.
-/
/-- **Every non-`imm` cell of `ag(ρ)` sits beneath an `imm` cell of `ag(ρ)`.**
`ag(ρ) = (ρ|imm ○ ⨀ ag(ρᵥ)) ○ ⨀ (ex(ρ′)_○ ○ ag(ρ′))`; the first group carries no
`own` or `mut` cell of its own and the second carries none either, by the same
argument one level down — so such a cell enters only through `ex(−)_○` inside
the `imm` family,
and the `imm` cell it entered beneath is carried to the top at its own location
by the same chain of `ag`s.

This is why `[TR]` 6.59's closing step lands on `↭`'s **first** clause, which
pins an `imm` cell together with its witness, rather than on the second, which
leaves a `mut` cell's value and witness free (§20e).
`[about ours: where `ag(ρ)`'s `mut` cells come from]` -/
theorem AgW.nonimm_beneath_imm {ρ σ : ResU Loc Val} (h : AgW ρ σ) :
    ∀ (n : Loc) (φ : CellU Loc Val), σ.get n = some φ → φ.kind ≠ Kind.imm →
      ∃ (m : Loc) (s : LSet) (u : Val) (χ : ResU Loc Val)
        (hh : χ.InStratum s.join) (ev av p : ResU Loc Val) (ξ : CellU Loc Val),
        σ.get m = some (CellU.immOf s u χ hh) ∧
        ExR χ ev ∧ AgW χ av ∧ ResU.CompR ev av p ∧
        p.get n = some ξ ∧ ξ.kind ≠ Kind.imm ∧
        ξ.wit = φ.wit ∧ ξ.erase = φ.erase := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  refine AgW.rec
    (motive_1 := fun ρ σ _ => ∀ (n : Loc) (φ : CellU Loc Val),
      σ.get n = some φ → φ.kind ≠ Kind.imm →
      ∃ (m : Loc) (s : LSet) (u : Val) (χ : ResU Loc Val)
        (hh : χ.InStratum s.join) (ev av p : ResU Loc Val) (ξ : CellU Loc Val),
        σ.get m = some (CellU.immOf s u χ hh) ∧
        ExR χ ev ∧ AgW χ av ∧ ResU.CompR ev av p ∧
        p.get n = some ξ ∧ ξ.kind ≠ Kind.imm ∧
        ξ.wit = φ.wit ∧ ξ.erase = φ.erase)
    (motive_2 := fun ρ w _ => ∀ q ∈ w, ∀ (n : Loc) (φ : CellU Loc Val),
      q.2.get n = some φ → φ.kind ≠ Kind.imm →
      ∃ (m : Loc) (s : LSet) (u : Val) (χ : ResU Loc Val)
        (hh : χ.InStratum s.join) (ev av p : ResU Loc Val) (ξ : CellU Loc Val),
        q.2.get m = some (CellU.immOf s u χ hh) ∧
        ExR χ ev ∧ AgW χ av ∧ ResU.CompR ev av p ∧
        p.get n = some ξ ∧ ξ.kind ≠ Kind.imm ∧
        ξ.wit = φ.wit ∧ ξ.erase = φ.erase)
    (motive_3 := fun ρ w _ => ∀ q ∈ w, ∀ (n : Loc) (φ : CellU Loc Val),
      q.2.get n = some φ → φ.kind ≠ Kind.imm →
      ∃ (s : LSet) (u : Val) (χ : ResU Loc Val)
        (hh : χ.InStratum s.join) (ev av p : ResU Loc Val) (ξ : CellU Loc Val),
        ExR χ ev ∧ AgW χ av ∧ ResU.CompR ev av p ∧
        p.get n = some ξ ∧ ξ.kind ≠ Kind.imm ∧
        ξ.wit = φ.wit ∧ ξ.erase = φ.erase ∧
        ((∃ m, q.2.get m = some (CellU.immOf s u χ hh)) ∨
          ρ.get q.1 = some (CellU.immOf s u χ hh)))
    ?mk ?nilM ?consM ?nilI ?consI h
  case mk =>
    intro ρ' σ' a bm bi wm wi hsm hsi hwm hwi hbm hbi ha hσ ihm ihi n φ hg hk
    rcases ResU.CompR.nonimm_source hσ hg hk with
      ⟨ξa, ea, ka, wa, era⟩ | ⟨ξb, eb, kb, wb, erb⟩
    · rcases ResU.CompR.nonimm_source ha ea ka with
        ⟨ξr, er, kr, wr, err⟩ | ⟨ξm, em, km, wm2, erm⟩
      · exact absurd (ResU.restrict_eq_some.mp er).2 kr
      · obtain ⟨τ, hmem, ξ', e', k', w', er'⟩ := BigComp.nonimm_source hbm em km
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmem
        obtain ⟨m, s, u, χ, hh, ev, av, pp, ξ, hqm, hex, hag, hc, hpn, hkξ, hwξ, heξ⟩ :=
          ihm q hq n ξ' e' k'
        obtain ⟨z, hz⟩ := BigComp.mem_factor hR ResU.compLawsR hbm q.2
          (List.mem_map.mpr ⟨q, hq, rfl⟩)
        obtain ⟨y₁, hy₁⟩ :=
          ResU.Comp.factor_trans hR ResU.compLawsR hz (ResU.CompR.comm ha)
        obtain ⟨y₂, hy₂⟩ := ResU.Comp.factor_trans hR ResU.compLawsR hy₁ hσ
        obtain ⟨s'', h'', hσm⟩ := ResU.CompR.imm_left_get hy₂ hqm
        exact ⟨m, s'', u, χ, h'', ev, av, pp, ξ, hσm, hex, hag, hc, hpn, hkξ,
          hwξ.trans (w'.trans (wm2.trans wa)),
          heξ.trans (er'.trans (erm.trans era))⟩
    · obtain ⟨τ, hmem, ξ', e', k', w', er'⟩ := BigComp.nonimm_source hbi eb kb
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmem
      obtain ⟨s, u, χ, hh, ev, av, pp, ξ, hex, hag, hc, hpn, hkξ, hwξ, heξ, hdisj⟩ :=
        ihi q hq n ξ' e' k'
      obtain ⟨z, hz⟩ := BigComp.mem_factor hR ResU.compLawsR hbi q.2
        (List.mem_map.mpr ⟨q, hq, rfl⟩)
      obtain ⟨y₁, hy₁⟩ := ResU.Comp.factor_trans hR ResU.compLawsR hz (ResU.CompR.comm hσ)
      rcases hdisj with ⟨m, hqm⟩ | hρm
      · obtain ⟨s'', h'', hσm⟩ := ResU.CompR.imm_left_get hy₁ hqm
        exact ⟨m, s'', u, χ, h'', ev, av, pp, ξ, hσm, hex, hag, hc, hpn, hkξ,
          hwξ.trans (w'.trans wb), heξ.trans (er'.trans erb)⟩
      · have hri : (ρ'.restrict Kind.imm).get q.1 = some (CellU.immOf s u χ hh) :=
          ResU.restrict_get_some hρm (CellU.kind_immOf _ _ _ _)
        obtain ⟨s₁, h₁, ham⟩ := ResU.CompR.imm_left_get ha hri
        obtain ⟨s'', h'', hσm⟩ := ResU.CompR.imm_left_get hσ ham
        exact ⟨q.1, s'', u, χ, h'', ev, av, pp, ξ, hσm, hex, hag, hc, hpn, hkξ,
          hwξ.trans (w'.trans wb), heξ.trans (er'.trans erb)⟩
  case nilM => intro ρ' q hq; exact absurd hq (by simp)
  case consM =>
    intro ρ' e l w ψ hψ hk he hw ihe ihw q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact ihe
    · exact ihw q hq'
  case nilI => intro ρ' q hq; exact absurd hq (by simp)
  case consI =>
    intro ρ' pe l w ψ hψ hk e a hex hag hc hw iha ihw q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · intro n φ hg hkφ
      obtain ⟨s, hs, heta⟩ := CellU.imm_eta hk
      rcases ResU.CompR.nonimm_source hc hg hkφ with
        ⟨ξe, ee, ke, we, ere⟩ | ⟨ξa, ea, ka, wa, era⟩
      · exact ⟨s, ψ.erase, ψ.wit, hs, e, a, pe, φ, hex, hag, hc, hg, hkφ, rfl, rfl,
          Or.inr (hψ.trans (congrArg some heta))⟩
      · obtain ⟨m, s', u, χ, hh, ev, av, pp, ξ, ham, hex', hag', hc', hpn,
          hkξ, hwξ, heξ⟩ := iha n ξa ea ka
        obtain ⟨s'', h'', hpm⟩ :=
          ResU.CompR.imm_left_get (ResU.CompR.comm hc) ham
        exact ⟨s'', u, χ, h'', ev, av, pp, ξ, hex', hag', hc', hpn, hkξ,
          hwξ.trans wa, heξ.trans era, Or.inl ⟨m, hpm⟩⟩
    · exact ihw q hq'

end BoCa.Fig16

end
