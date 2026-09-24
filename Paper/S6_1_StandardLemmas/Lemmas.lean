import Paper.S5_Model.Definitions
import Support.Model.Algebra
import Support.Model.Cells
import Support.Model.Compatibility
import Support.Model.Composition
import Support.Model.Flattening
import Support.Model.Prelude
import Support.Model.WalkSplitting
import Support.Model.Walks

/-!
# [TR] §6.1 Standard Lemmas  (physical pp. 6–8), Lemmas 6.1–6.15

*"There's no strict definition, but lemmas feel 'standard' when their statement
doesn't unfold resources or definitions, and don't include any particularly
unusual/custom operations."*

The algebra of the two compositions (6.1–6.4, 6.9, 6.12–6.14), compatibility
`#` (6.5, 6.6, 6.11, 6.15), and lowering `⟦−⟧` (6.7, 6.8) and validity `✓` (6.10).
`[TR]` writes `▸◁` and `◐` for "either of `▸◂`/`▷◁`" and "either of `●`/`○`"; Lean
states such a lemma once over a schema and discharges it at both.

The printed proofs of 6.7, 6.10 and 6.15 cite §6.2's walk-splitting lemmas 6.18 and
6.20, and with them 6.30, 6.31 and 6.36; those five are declared in this file,
ahead of 6.7, and so are the definition-row theorems `BigComp.perm` (row 5.56) and
two of row 5.67's, which the same proofs use.

**How this file reads.**  The numbered results of the subsection, in printed order as
far as Lean's definition-before-use allows.  Each opens with a record:

* the result's number, page and status (`proved`, `proved*`, `variant`; the
  legend is in `Paper/INDEX.md`);
* the printed statement, quoted, with the extraction's garbled symbols restored;
* the printed proof, transcribed compactly and in its own order, citing the lemmas it
  cites;
* the Lean declaration (its docstring carries the tag and its account of the
  proof),
  and the numbered alias `TR.lemma_6_N` declared after it;
* a note on how the declaration reads the printed statement.

A result whose declaration an earlier subsection's printed proof needs is declared
in that subsection's file, under a heading saying so; its record and alias stay
here.  A run of declarations the paper does not print, placed in this file only
because a result below needs it and it needs a result above, is marked
`[about ours]` and names the result it serves.  `§N` citations are to
`docs/adjudications.md`.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.1 · `[TR]` p. 6 · `proved`

> ρ₁ ▸◁ ρ₂ = ρ₂ ▸◁ ρ₁

**Printed proof, transcribed.** By definition, and the fact that `▸◁` is commutative on cells: at `▸◂` commutativity is immediate; at `▷◁` the first case is the previous one, and the second is immediate since sets are unordered.

**Lean.** `BoCa.Fig16.ResU.compat_comm_iff`, alias `TR.lemma_6_1`, tag `[as printed]`.

**Note.** `Fig16.ResU.compat_comm_iff`, on the printed carrier — one theorem in the schema, as the print states it, with the print's own "`▸◁` is commutative on cells" as a hypothesis discharged at **both** values the metavariable takes: `Fig16.ResU.compatS_comm_iff` at `▶◀` and `Fig16.ResU.compatR_comm_iff` at `⋈` (settled, `docs/adjudications.md` §12.35). Definitions have no row in this file by design — they are definition rows of `Paper/INDEX.md`, at row 5.61
-/
/-- **`[TR]` Lemma 6.1** (p. 6): `ρ₁ ▶◁ ρ₂ = ρ₂ ▶◁ ρ₁`.  Stated once in the
schema, as the print states it; `hC` is the print's own "`▶◁` is commutative on
cells", discharged below at both of the values `▶◁` ranges over.
`[as printed]` -/
theorem ResU.compat_comm_iff (C : CellU Loc Val → CellU Loc Val → Prop)
    (hC : ∀ ψ₁ ψ₂, C ψ₁ ψ₂ → C ψ₂ ψ₁) (ρ₁ ρ₂ : ResU Loc Val) :
    ResU.Compat C ρ₁ ρ₂ ↔ ResU.Compat C ρ₂ ρ₁ :=
  ⟨ResU.Compat.comm hC, ResU.Compat.comm hC⟩

/-- `[TR]` Lemma 6.1 at `▶◀`.  `[as printed]` -/
theorem ResU.compatS_comm_iff (ρ₁ ρ₂ : ResU Loc Val) :
    ResU.CompatS ρ₁ ρ₂ ↔ ResU.CompatS ρ₂ ρ₁ :=
  ResU.compat_comm_iff _ (fun _ _ a => a.symm) ρ₁ ρ₂

/-- `[TR]` Lemma 6.1 at `⋈`.  `[as printed]` -/
theorem ResU.compatR_comm_iff (ρ₁ ρ₂ : ResU Loc Val) :
    ResU.CompatR ρ₁ ρ₂ ↔ ResU.CompatR ρ₂ ρ₁ :=
  ResU.compat_comm_iff _ (fun _ _ a => a.symm) ρ₁ ρ₂

end BoCa.Fig16

alias TR.lemma_6_1 := BoCa.Fig16.ResU.compat_comm_iff

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.2 · `[TR]` p. 6 · `proved`

> ρ₁ ◐ ρ₂ = ρ₂ ◐ ρ₁

**Printed proof, transcribed.** Composability follows from Lemma 6.1.  The rest follows from commutativity of composition on cells: at `●` it is immediate because `∪` is commutative; at `○` the first two cases are immediate, and the other two follow from noting that `ψᵢ` is invariant under changing the order of the cells.

**Lean.** `BoCa.Fig16.ResU.Comp.comm`, alias `TR.lemma_6_2`, tag `[as printed]`.

**Note.** `Fig16.ResU.Comp.comm`, on the printed carrier — one theorem in the schema, discharged at both `●` (`Fig16.ResU.CompS.comm`) and `○` (`Fig16.ResU.CompR.comm`), which is how the print proves it. As a graph it is definedness and value together, i.e. the print's Kleene equality. Definitions have no row in this file by design — they are definition rows of `Paper/INDEX.md`, at row 5.65
-/
/-- **`[TR]` Lemma 6.2** (p. 6): `ρ₁ ◐ ρ₂ = ρ₂ ◐ ρ₁`.  As a graph this is
definedness and value together, which is the print's equation between partial
expressions.  Stated once in the schema and discharged below at both `●` and
`○`, which is how the print proves it.  `[as printed]` -/
theorem ResU.Comp.comm {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hR : ∀ ψ₁ ψ₂, R ψ₁ ψ₂ → R ψ₂ ψ₁)
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → C ψ₂ ψ₁ ψ)
    {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.Comp R C ρ₁ ρ₂ ρ) :
    ResU.Comp R C ρ₂ ρ₁ ρ := by
  refine ⟨ResU.Compat.comm hR h.1, fun l => ?_⟩
  rcases h.get l with ⟨e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ |
      ⟨ψ₁, ψ₂, ψ, e₁, e₂, e, hC'⟩ <;> rw [e₁, e₂]
  · exact e
  · exact e
  · exact e
  · exact ⟨ψ, e, hC _ _ _ hC'⟩

end BoCa.Fig16

alias TR.lemma_6_2 := BoCa.Fig16.ResU.Comp.comm

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.3 · `[TR]` p. 6 · `proved`

> ρ₁ ◐ (ρ₂ ◐ ρ₃) = ρ₁ ◐ ρ₂ ◐ ρ₃

**Printed proof, transcribed.** Unfolding `◐`, the only interesting case is `ℓ ∈ dom(ρ₁) ∩ dom(ρ₂) ∩ dom(ρ₃)`.  At `●`, associativity of `∪`.  At `○`, split on `ρ₂ ○ ρ₃`: the first case is immediate; the second follows from `imm` always being preserved by `○`; in the third, if `ρ₁(ℓ)` is owned the `mut` is the result, if it is `mut` use associativity of `⊓` and `∧`, and if it is `imm` the result is `imm` either way; in the fourth, owned gives the `mut`, `mut` is immediate, `imm` gives `imm` either way; in the fifth, owned gives the `imm`, `mut` gives the `imm`, and `imm` combines the `imm`s.

**Lean.** `BoCa.Fig16.ResU.Comp.assoc`, alias `TR.lemma_6_3`, tag `[as printed]`.

**Note.** `Fig16.ResU.Comp.assoc`, on the printed carrier — the Kleene equality of the two partial expressions, at every result `w`, stated once in the schema and discharged at both `●` (`Fig16.ResU.CompS.assoc`) and `○` (`Fig16.ResU.CompR.assoc`), which is how the print states and proves it. `hR` and `hC` constrain only the schema parameters. The cell level is `Fig16.CellU.compS_assoc` (associativity of `∪`, the print's `●` case) and `Fig16.CellU.compR_assoc` (the five-clause split, its `○` case). Definitions have no row in this file by design — they are definition rows of `Paper/INDEX.md`, at row 5.66
-/
/-- **`[TR]` Lemma 6.3** (p. 6, its `○` case on p. 7):
`ρ₁ ◐ (ρ₂ ◐ ρ₃) = ρ₁ ◐ ρ₂ ◐ ρ₃`.  Both sides are partial, so the printed
equation is the Kleene equality of the two partial expressions: at every result
`w`, one side is defined with value `w` exactly when the other is.  Stated once
in the schema, as the print states it; `hR` and `hC` are the print's own facts
about the cell-level `◐` the schema is instantiated at, discharged below at both
`●` and `○`, which is how the print proves it.  `[as printed]` -/
theorem ResU.Comp.assoc {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂)
    (hC : ∀ ψ₁ ψ₂ ψ₃ ω, (∃ χ, C ψ₂ ψ₃ χ ∧ C ψ₁ χ ω) ↔ (∃ υ, C ψ₁ ψ₂ υ ∧ C υ ψ₃ ω))
    (ρ₁ ρ₂ ρ₃ w : ResU Loc Val) :
    (∃ x, ResU.Comp R C ρ₂ ρ₃ x ∧ ResU.Comp R C ρ₁ x w) ↔
    (∃ y, ResU.Comp R C ρ₁ ρ₂ y ∧ ResU.Comp R C y ρ₃ w) := by
  constructor
  · rintro ⟨x, h₂₃, h₁x⟩
    exact ResU.Comp.assoc_left hR (fun a b c d => (hC a b c d).mp) h₂₃ h₁x
  · rintro ⟨y, h₁₂, hy₃⟩
    obtain ⟨x, hx, hw⟩ :=
      ResU.Comp.assoc_left (R := fun a b => R b a) (C := fun a b c => C b a c)
        (fun ψ₁ ψ₂ ψ h => hR ψ₂ ψ₁ ψ h)
        (fun ψ₁ ψ₂ ψ₃ ω h => (hC ψ₃ ψ₂ ψ₁ ω).mpr h)
        ((ResU.Comp.swap _ _ _).mpr h₁₂) ((ResU.Comp.swap _ _ _).mpr hy₃)
    exact ⟨x, (ResU.Comp.swap _ _ _).mp hx, (ResU.Comp.swap _ _ _).mp hw⟩

end BoCa.Fig16

alias TR.lemma_6_3 := BoCa.Fig16.ResU.Comp.assoc

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.4 · `[TR]` p. 7 · `proved`

> ρ ◐ ∅ = ρ

**Printed proof, transcribed.** By definition `dom(ρ) ∩ ∅ = ∅`, so `▸◁` holds immediately, and the result is trivially `ρ`.

**Lean.** `BoCa.Fig16.ResU.comp_empty_right`, alias `TR.lemma_6_4`, tag `[as printed]`.

**Note.** `Fig16.ResU.comp_empty_right`, on the printed carrier — in the schema, so both `●` and `○`, definedness and value together.
-/
/-- **`[TR]` Lemma 6.4** (p. 7): `ρ ◐ ∅ = ρ`.  Definedness and value together,
in the schema, hence at both `●` and `○`.  `[as printed]` -/
theorem ResU.comp_empty_right {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} (ρ : ResU Loc Val) :
    ResU.Comp R C ρ PMap.empty ρ := by
  refine ⟨ResU.Compat.of_disjoint (fun _ => Or.inr rfl), fun l => ?_⟩
  show OptComp C (ρ.get l) none (ρ.get l)
  cases e : ρ.get l with
  | none => rfl
  | some ψ => rfl

end BoCa.Fig16

alias TR.lemma_6_4 := BoCa.Fig16.ResU.comp_empty_right

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.5 · `[TR]` p. 7 · `proved`

> If ✓ρ then ρ # ∅

**Printed proof, transcribed.** Immediate by definition.

**Lean.** `BoCa.Fig16.ResU.hash_empty_right`, alias `TR.lemma_6_5`, tag `[as printed]`.

**Note.** `Fig16.ResU.hash_empty_right`, on the printed carrier, at `Fig16.ResU.Hash` — which is the print's `ρ₁ ▶◀ ρ₂ ∧ ✓(ρ₁ ● ρ₂)` with `✓` the printed `⦇−⦈ defined`.
-/
/-- **`[TR]` Lemma 6.5** (p. 7): if `✓ρ` then `ρ # ∅`.  `[as printed]` -/
theorem ResU.hash_empty_right {ρ : ResU Loc Val} (h : ResU.Valid ρ) :
    ResU.Hash ρ PMap.empty :=
  ⟨ResU.Compat.of_disjoint (fun _ => Or.inr rfl), ρ, ResU.comp_empty_right ρ, h⟩

end BoCa.Fig16

alias TR.lemma_6_5 := BoCa.Fig16.ResU.hash_empty_right

namespace BoCa.Fig16
variable {Loc Val : Type}

/-! `[about ours]` — what the Lean of Lemma 6.6 needs; the paper prints nothing here. -/
/-- `[TR]` Lemma 6.2 at `●`.  `[as printed]` -/
theorem ResU.CompS.comm {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ) :
    ResU.CompS ρ₂ ρ₁ ρ :=
  ResU.Comp.comm (fun _ _ a => a.symm) (fun _ _ _ a => a.comm) h

/-- **`[TR]` Lemma 6.6** (p. 7), one direction: `ρ₁ # ρ₂` implies `ρ₂ # ρ₁`.
`[as printed]` -/
theorem ResU.hash_symm {ρ₁ ρ₂ : ResU Loc Val} (h : ResU.Hash ρ₁ ρ₂) :
    ResU.Hash ρ₂ ρ₁ := by
  obtain ⟨hc, ρ, hcomp, hv⟩ := h
  exact ⟨hc.symm, ρ, hcomp.comm, hv⟩

/-!
## Lemma 6.6 · `[TR]` p. 7 · `proved`

> ρ₁ # ρ₂ if and only if ρ₂ # ρ₁

**Printed proof, transcribed.** From Lemma 6.2, and unfolding `⦇−⦈` with Lemmas 6.20 and 6.18.

**Lean.** `BoCa.Fig16.ResU.hash_symm_iff`, alias `TR.lemma_6_6`, tag `[as printed]`.

**Note.** `Fig16.ResU.hash_symm_iff`, on the printed carrier — the printed "if and only if", from `Fig16.ResU.hash_symm` applied twice, which is 6.1 and 6.2 at `●`.
-/
/-- `[TR]` Lemma 6.6 (p. 7), the printed "if and only if".  `[as printed]` -/
theorem ResU.hash_symm_iff (ρ₁ ρ₂ : ResU Loc Val) :
    ResU.Hash ρ₁ ρ₂ ↔ ResU.Hash ρ₂ ρ₁ := ⟨ResU.hash_symm, ResU.hash_symm⟩

end BoCa.Fig16

alias TR.lemma_6_6 := BoCa.Fig16.ResU.hash_symm_iff

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.9 · `[TR]` p. 7 · `proved`

> ρ₁ ▸◂ ρ₂ iff ρ₁ ● ρ₂ is defined.

**Printed proof, transcribed.** By definition.

**Lean.** `BoCa.Fig16.ResU.compS_defined_iff`, alias `TR.lemma_6_9`, tag `[as printed]` `[variant: …]`.

**Note.** `Fig16.ResU.compS_defined_iff`, on the printed carrier. Which half is definitional should be said plainly: `ResU.Comp` carries the printed guard as its first conjunct, so the forward direction is that conjunct and nothing more; the content is the converse, which builds the composite from `▶◀` alone, cell by cell at every overlapping location (`Fig16.ResU.compS_spec`). `Fig16.ResU.compR_defined_iff` is the `○` twin, which the paper does not state
-/
/-- `ρ₁ ▶◀ ρ₂` iff `ρ₁ ● ρ₂` is defined — `[TR]` Lemma 6.9 (p. 7, 600 dpi),
whose own proof is "By definition".  `ResU.Comp` carries the printed guard as
its first conjunct, so the forward direction is that conjunct and nothing more.
The content is the converse — building the composite from `▶◀` alone, which
goes through `ResU.compS_spec`, cell by cell at every overlapping location.
Stated on this file's carrier, which is Fig. 16 on the settled reading of the
`fin` mark (§12.33, and the `[variant: …]` at `Res`).  `[as printed]` -/
theorem ResU.compS_defined_iff (ρ₁ ρ₂ : ResU Loc Val) :
    (∃ ρ, ResU.CompS ρ₁ ρ₂ ρ) ↔ ResU.CompatS ρ₁ ρ₂ :=
  ⟨fun ⟨_, h⟩ => h.1, fun h => ⟨_, ResU.compS_spec ρ₁ ρ₂ h⟩⟩

end BoCa.Fig16

alias TR.lemma_6_9 := BoCa.Fig16.ResU.compS_defined_iff

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### Lemma 6.36's declaration, ahead of its subsection

`[TR]` prints Lemma 6.36 in §6.2 (p. 12).  The Lean of Lemmas 6.7, 6.8, 6.10, 6.11 and 6.15 in this file needs it, so it is declared here; its statement, printed proof and alias are in `Paper/S6_2_NonStandardLemmas/Lemmas.lean`.
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

/-! `[about ours]` — what the Lean of Lemma 6.7 needs; the paper prints nothing here. -/
/-- `[TR]` Lemma 6.36 at `●`, which is the value `[CONF]` Fig. 18a's `E⦇ρ′⦈_•`
names.  This performs the discharge of `ExW.immFree`'s `hC`, by
`CellU.compS_ne_imm`.  `[as printed]` -/
theorem ExS.immFree {ρ σ : ResU Loc Val} (h : ExS ρ σ) : σ.ImmFree :=
  ExW.immFree (fun ψ₁ ψ₂ ψ hc h₁ _ => CellU.compS_ne_imm ψ₁ ψ₂ ψ hc h₁) h

/-!
### Lemma 6.31's declaration, ahead of its subsection

`[TR]` prints Lemma 6.31 in §6.2 (p. 11).  The Lean of Lemmas 6.7, 6.8, 6.10, 6.11 and 6.15 in this file needs it, so it is declared here; its statement, printed proof and alias are in `Paper/S6_2_NonStandardLemmas/Lemmas.lean`.
-/
/-- **`[TR]` Lemma 6.31** (p. 11): if `ρ ▶◀ ρ′` then `ρ ○ ρ′ = ρ ● ρ′`.  As an
equality of graphs, which is definedness and value together.  `[as printed]` -/
theorem ResU.compR_iff_compS {ρ₁ ρ₂ : ResU Loc Val} (h : ResU.CompatS ρ₁ ρ₂)
    (σ : ResU Loc Val) : ResU.CompR ρ₁ ρ₂ σ ↔ ResU.CompS ρ₁ ρ₂ σ := by
  constructor
  · intro hr
    refine ⟨h, fun l => ?_⟩
    rcases hr.get l with ⟨e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ |
        ⟨ψ₁, ψ₂, ψ, e₁, e₂, e, hC⟩ <;> rw [e₁, e₂]
    · exact e
    · exact e
    · exact e
    · have hk := h l _ _ e₁ e₂
      have hψ : ψ = CellU.compS _ _ hk :=
        CellU.CompR.functional hC (CellU.CompR.strict hk)
      exact ⟨ψ, e, hψ ▸ CellU.compS_spec _ _ hk⟩
  · intro hs
    refine ⟨fun l ψ₁ ψ₂ e₁ e₂ => CellU.CompatR.of_compatS (h l ψ₁ ψ₂ e₁ e₂), fun l => ?_⟩
    rcases hs.get l with ⟨e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ |
        ⟨ψ₁, ψ₂, ψ, e₁, e₂, e, hC⟩ <;> rw [e₁, e₂]
    · exact e
    · exact e
    · exact e
    · have hk := h l _ _ e₁ e₂
      have hψ : ψ = CellU.compS _ _ hk :=
        CellU.CompS.functional hC (CellU.compS_spec _ _ hk)
      exact ⟨ψ, e, hψ ▸ CellU.CompR.strict hk⟩

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {R : CellU Loc Val → CellU Loc Val → Prop}
variable {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}

/-! `[about ours]` — what the Lean of Lemma 6.7 needs; the paper prints nothing here. -/
/-- Exchanging the first two entries of the fold leaves value and definedness
alone.  Reading `hc₂ : σ₂ ◐ τ = χ` and `hc₁ : σ₁ ◐ χ = b`: Lemma 6.3
reassociates to `(σ₁ ◐ σ₂) ◐ τ = b`, Lemma 6.2 turns the head pair round, and
6.3 again puts `σ₂` outside, which is the transposed fold.  `swap` is the only
`List.Perm` constructor that is not structural, so this is the whole content of
`BigComp.of_perm`.
`[about ours: `[TR]` Lemmas 6.2 and 6.3 read at one step of the fold]` -/
theorem BigComp.swap (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) (hC : ResU.CompLaws C)
    {σ₁ σ₂ : ResU Loc Val} {l : List (ResU Loc Val)} {b : ResU Loc Val}
    (h : BigComp R C (σ₁ :: σ₂ :: l) b) : BigComp R C (σ₂ :: σ₁ :: l) b := by
  cases h with
  | cons h₁ hc₁ =>
      cases h₁ with
      | cons h₂ hc₂ =>
          obtain ⟨y, h₁₂, hy⟩ :=
            (ResU.Comp.assoc hR hC.assoc _ _ _ b).mp ⟨_, hc₂, hc₁⟩
          obtain ⟨x, hx, hb⟩ :=
            (ResU.Comp.assoc hR hC.assoc _ _ _ b).mpr
              ⟨y, ResU.Comp.comm_of_laws hR hC h₁₂, hy⟩
          exact BigComp.cons (BigComp.cons h₂ hx) hb

/-- Reordering the folded list carries the graph across unchanged — definedness
travels with the value, which is what settles the worry that the existential
over orderings could make `⨀` newly defined.
`[about ours: the order-independence of the fold, in transport form]` -/
theorem BigComp.of_perm (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) (hC : ResU.CompLaws C)
    {l l' : List (ResU Loc Val)} (hp : l.Perm l') :
    ∀ {b : ResU Loc Val}, BigComp R C l b → BigComp R C l' b := by
  induction hp with
  | nil => exact fun h => h
  | cons σ _ ih =>
      intro b h
      cases h with
      | cons hτ hc => exact BigComp.cons (ih hτ) hc
  | swap σ₁ σ₂ l => exact fun h => BigComp.swap hR hC h
  | trans _ _ ih₁ ih₂ => exact fun h => ih₂ (ih₁ h)

/-!
### Row 5.56's theorem `BoCa.Fig16.BigComp.perm`, ahead of its file

A remark on a printed definition of `[TR]` §5; its proof uses results of §6, and the Lean of Lemmas 6.7, 6.8, 6.10, 6.11 and 6.15 in this file needs it, so it is declared here.  The row is recorded in `Paper/S5_Model/Remarks.lean`.
-/
/-- **The fold list may be reordered.**  This is what `BigComp` owes: "`⨀` folds a
list, and that the value does not depend on the fold needs `[TR]` Lemmas 6.1,
6.2 and 6.3".  6.1 enters through `ResU.Comp.comm_of_laws`, 6.2 and 6.3 through
`BigComp.swap`.
`[about ours: `BigComp` is the fold shape; the printed `⨀` is the order-free
operator this makes it]` -/
theorem BigComp.perm (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) (hC : ResU.CompLaws C)
    {l l' : List (ResU Loc Val)} (hp : l.Perm l') {b b' : ResU Loc Val}
    (h : BigComp R C l b) (h' : BigComp R C l' b') : b = b' :=
  BigComp.functional hC (BigComp.of_perm hR hC hp h) h'

/-! `[about ours]` — what the Lean of Lemma 6.7 needs; the paper prints nothing here. -/
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
is the proof that the graph is a function — the obligation convention G4 incurs]` -/
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
over `ResU.Sites` lists, so both are pinned up to order and `BigComp.sites`
closes each `◯`; the two outer `○`s are `ResU.CompR.functional`.  `ag` is
always at `○`, so the schema hypotheses are discharged here rather than taken.
`[about ours: the print's `ag(ρ)` is a term and `AgW` is its graph (G4); this is
the proof that the graph is a function — the obligation convention G4 incurs]` -/
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

/-- **`⟦ρ⟧` is a term** — `⟦ρ⟧ ≜ [ℓ ↦ v | ⟦⦇ρ⦈(ℓ)⟧ = v]` (`[TR]` p. 5) reads
the erasure off `⦇ρ⦈` location by location, so it is determined as soon as
`⦇ρ⦈` is.
`[about ours: `ResU.Lower` is the graph of the printed `⟦ρ⟧` (G4); this is the
proof that the graph is a function]` -/
theorem ResU.Lower.functional {ρ : ResU Loc Val} {m m' : Loc → Option Val}
    (h : ρ.Lower m) (h' : ρ.Lower m') : m = m' := by
  obtain ⟨σ, hf, hm⟩ := h
  obtain ⟨σ', hf', hm'⟩ := h'
  cases ResU.Flat.functional hf hf'
  exact funext fun l => (hm l).trans (hm' l).symm

/-- The mirror of `ResU.CompS.get_left`. -/
theorem ResU.CompS.get_right {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {l : Loc} {ψ₂ : CellU Loc Val} (e₂ : ρ₂.get l = some ψ₂) :
    ∃ ψ, ρ.get l = some ψ ∧ ψ.kind = ψ₂.kind ∧ ψ.wit = ψ₂.wit :=
  ResU.CompS.get_left (ResU.CompS.comm h) e₂

/-- The mirror of `ResU.CompS.get_left_of_ne_imm`. -/
theorem ResU.CompS.get_right_of_ne_imm {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {l : Loc} {ψ : CellU Loc Val} (e₂ : ρ₂.get l = some ψ) (hk : ψ.kind ≠ Kind.imm) :
    ρ₁.get l = none ∧ ρ.get l = some ψ :=
  ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm h) e₂ hk

/-- `●` is an instance of `○` — `[TR]` Lemma 6.31 read left to right.
`[restricted: the `●`-implies-`○` half of the printed Kleene equality; the
other half is `ResU.compR_iff_compS`'s forward direction]` -/
theorem ResU.CompS.toCompR {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ) :
    ResU.CompR ρ₁ ρ₂ ρ :=
  (ResU.compR_iff_compS h.1 ρ).mpr h

/-- **`(ρ₁ ● ρ₂)|ι = ρ₁|ι ○ ρ₂|ι`** — the form 6.20 uses, whose composites are
all at `○` although its hypothesis is at `●`.
`[about ours: the printed `ρ|ι` and `●`, composed at `○` by 6.31; the equation
itself has no printed row]` -/
theorem ResU.CompS.restrictR {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    (k : Kind) :
    ResU.CompR (ρ₁.restrict k) (ρ₂.restrict k) (ρ.restrict k) :=
  ResU.CompS.toCompR (ResU.CompS.restrict h k)

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {R : CellU Loc Val → CellU Loc Val → Prop}
variable {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}

/-- `⨀[σ] = σ`, by [TR] Lemma 6.4 — and nothing else folds to anything else.
`[about ours: `BigComp` is the fold shape for the printed `⨀`]` -/
theorem BigComp.singleton_iff (hC : ResU.CompLaws C) {σ τ : ResU Loc Val} :
    BigComp R C [σ] τ ↔ τ = σ := by
  constructor
  · intro h
    cases h with
    | cons ht hc =>
        cases ht
        exact ResU.Comp.functional hC.functional hc (ResU.comp_empty_right _)
  · rintro rfl
    exact BigComp.cons BigComp.nil (ResU.comp_empty_right _)

/-- `⨀[σ₁, σ₂] = σ₁ ◐ σ₂` — the two-element fold is the binary composition.
`[about ours: `BigComp` is the fold shape for the printed `⨀`]` -/
theorem BigComp.pair (hC : ResU.CompLaws C) {σ₁ σ₂ τ : ResU Loc Val} :
    BigComp R C [σ₁, σ₂] τ ↔ ResU.Comp R C σ₁ σ₂ τ := by
  constructor
  · intro h
    cases h with
    | cons ht hc =>
        obtain rfl := BigComp.singleton_iff hC |>.mp ht
        exact hc
  · intro h
    exact BigComp.cons (BigComp.singleton_iff hC |>.mpr rfl) h

/-- **`⨀(l₁ ++ l₂) = ⨀l₁ ◐ ⨀l₂`**, as a Kleene equality: the concatenation
folds exactly when both halves fold to composable values, and then to their
composite.  This is where [TR] 6.3 and 6.4 are spent.
`[about ours: `BigComp` is the fold shape; the rebracketing is the printed
6.3 and the base case the printed 6.4]` -/
theorem BigComp.append (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) (hC : ResU.CompLaws C)
    {l₁ l₂ : List (ResU Loc Val)} {b : ResU Loc Val} :
    BigComp R C (l₁ ++ l₂) b ↔
      ∃ b₁ b₂, BigComp R C l₁ b₁ ∧ BigComp R C l₂ b₂ ∧ ResU.Comp R C b₁ b₂ b := by
  induction l₁ generalizing b with
  | nil =>
      refine ⟨fun h => ⟨PMap.empty, b, BigComp.nil, h, ResU.Comp.comm_of_laws hR hC (ResU.comp_empty_right b)⟩, ?_⟩
      rintro ⟨b₁, b₂, h₁, h₂, hc⟩
      cases h₁
      exact ResU.Comp.functional hC.functional
        (ResU.Comp.comm_of_laws hR hC (ResU.comp_empty_right b₂)) hc ▸ h₂
  | cons σ l ih =>
      constructor
      · intro h
        cases h with
        | cons hτ hcσ =>
            obtain ⟨b₁, b₂, k₁, k₂, kc⟩ := ih.mp hτ
            obtain ⟨y, hy₁, hy₂⟩ :=
              (ResU.Comp.assoc hR hC.assoc σ b₁ b₂ b).mp ⟨_, kc, hcσ⟩
            exact ⟨y, b₂, BigComp.cons k₁ hy₁, k₂, hy₂⟩
      · rintro ⟨b₁, b₂, h₁, h₂, hc⟩
        cases h₁ with
        | cons hτ hcσ =>
            obtain ⟨x, hx₁, hx₂⟩ :=
              (ResU.Comp.assoc hR hC.assoc σ _ b₂ b).mpr ⟨b₁, hcσ, hc⟩
            exact BigComp.cons (ih.mpr ⟨_, b₂, hτ, h₂, hx₁⟩) hx₂

/-- **The exchange of the middle two factors**, as a Kleene equality:

    (a₁ ◐ a₂) ◐ (b₁ ◐ b₂)  =  (a₁ ◐ b₁) ◐ (a₂ ◐ b₂).

Neither side's intermediate composites are assumed to exist — each is bound by
its own existential — so this is definedness and value together, which is what
"Kleene-equal" asks for.
`[about ours: the rearrangement [TR] 6.18's and 6.20's proofs perform on a
four-fold composite; the printed rows behind it are 6.2 and 6.3]` -/
theorem ResU.Comp.exchange₄ (hR : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) (hC : ResU.CompLaws C)
    (a₁ a₂ b₁ b₂ x : ResU Loc Val) :
    (∃ A B, ResU.Comp R C a₁ a₂ A ∧ ResU.Comp R C b₁ b₂ B ∧ ResU.Comp R C A B x) ↔
      (∃ S₁ S₂, ResU.Comp R C a₁ b₁ S₁ ∧ ResU.Comp R C a₂ b₂ S₂ ∧
        ResU.Comp R C S₁ S₂ x) := by
  -- Both sides are the fold of a four-element list; the two lists differ by the
  -- transposition of their middle entries.
  have hleft : (∃ A B, ResU.Comp R C a₁ a₂ A ∧ ResU.Comp R C b₁ b₂ B ∧
      ResU.Comp R C A B x) ↔ BigComp R C [a₁, a₂, b₁, b₂] x := by
    rw [show ([a₁, a₂, b₁, b₂] : List (ResU Loc Val)) = [a₁, a₂] ++ [b₁, b₂] from rfl,
      BigComp.append hR hC]
    exact ⟨fun ⟨A, B, hA, hB, hx⟩ =>
        ⟨A, B, BigComp.pair hC |>.mpr hA, BigComp.pair hC |>.mpr hB, hx⟩,
      fun ⟨A, B, hA, hB, hx⟩ =>
        ⟨A, B, BigComp.pair hC |>.mp hA, BigComp.pair hC |>.mp hB, hx⟩⟩
  have hright : (∃ S₁ S₂, ResU.Comp R C a₁ b₁ S₁ ∧ ResU.Comp R C a₂ b₂ S₂ ∧
      ResU.Comp R C S₁ S₂ x) ↔ BigComp R C [a₁, b₁, a₂, b₂] x := by
    rw [show ([a₁, b₁, a₂, b₂] : List (ResU Loc Val)) = [a₁, b₁] ++ [a₂, b₂] from rfl,
      BigComp.append hR hC]
    exact ⟨fun ⟨S₁, S₂, h₁, h₂, hx⟩ =>
        ⟨S₁, S₂, BigComp.pair hC |>.mpr h₁, BigComp.pair hC |>.mpr h₂, hx⟩,
      fun ⟨S₁, S₂, h₁, h₂, hx⟩ =>
        ⟨S₁, S₂, BigComp.pair hC |>.mp h₁, BigComp.pair hC |>.mp h₂, hx⟩⟩
  have hp : ([a₁, a₂, b₁, b₂] : List (ResU Loc Val)).Perm [a₁, b₁, a₂, b₂] :=
    List.Perm.cons a₁ (List.Perm.swap b₁ a₂ [b₂])
  rw [hleft, hright]
  exact ⟨BigComp.of_perm hR hC hp, BigComp.of_perm hR hC hp.symm⟩

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- The exchange at `●`, which is the one [TR] 6.18 uses.
`[about ours: `ResU.Comp.exchange₄` instantiated at `●`]` -/
theorem ResU.CompS.exchange₄ (a₁ a₂ b₁ b₂ x : ResU Loc Val) :
    (∃ A B, ResU.CompS a₁ a₂ A ∧ ResU.CompS b₁ b₂ B ∧ ResU.CompS A B x) ↔
      (∃ S₁ S₂, ResU.CompS a₁ b₁ S₁ ∧ ResU.CompS a₂ b₂ S₂ ∧ ResU.CompS S₁ S₂ x) :=
  ResU.Comp.exchange₄ (fun _ _ _ hc => CellU.CompS.compat hc) ResU.compLawsS
    a₁ a₂ b₁ b₂ x

/-- **The `own` and `mut` sites of `ρ₁ ● ρ₂` are those of `ρ₁` then those of
`ρ₂`.**  Duplicate-freeness survives the concatenation because `ResU.CompatS.right_eq_none` makes the two
lists disjoint. -/
theorem ResU.Sites.append_of_compS {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {k : Kind} (hk : k ≠ Kind.imm) {d₁ d₂ : List Loc}
    (h₁ : ρ₁.Sites k d₁) (h₂ : ρ₂.Sites k d₂) : ρ.Sites k (d₁ ++ d₂) := by
  refine ⟨List.nodup_append.mpr ⟨h₁.1, h₂.1, ?_⟩, fun l => ?_⟩
  · rintro a ha b hb rfl
    obtain ⟨ψ₁, g₁, gk₁⟩ := (h₁.2 a).mp ha
    obtain ⟨ψ₂, g₂, -⟩ := (h₂.2 a).mp hb
    rw [ResU.CompatS.right_eq_none h.1 g₁ (fun e => hk (gk₁.symm.trans e))] at g₂
    exact absurd g₂ (by simp)
  · refine ⟨fun hm => ?_, fun hm => ?_⟩
    · rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨ψ, g, gk⟩ := (h₁.2 l).mp hm
        exact ⟨ψ, (ResU.CompS.get_left_of_ne_imm h g (fun e => hk (gk.symm.trans e))).2, gk⟩
      · obtain ⟨ψ, g, gk⟩ := (h₂.2 l).mp hm
        exact ⟨ψ, (ResU.CompS.get_right_of_ne_imm h g (fun e => hk (gk.symm.trans e))).2, gk⟩
    · obtain ⟨ψ, g, gk⟩ := hm
      rcases ResU.CompS.get_split_of_ne_imm h g (fun e => hk (gk.symm.trans e)) with
        ⟨g₁, -⟩ | ⟨-, g₂⟩
      · exact List.mem_append.mpr (Or.inl ((h₁.2 l).mpr ⟨ψ, g₁, gk⟩))
      · exact List.mem_append.mpr (Or.inr ((h₂.2 l).mpr ⟨ψ, g₂, gk⟩))

/-- **A key-indexed family over the `own` or `mut` sites of `ρ₁ ● ρ₂` cuts into
a family over `ρ₁`'s sites and one over `ρ₂`'s**, up to order and with no entry
invented or lost.
`[about ours: `ResU.Sites` is convention G6's index set, and this is how
two of them sit inside a third]` -/
theorem ResU.Sites.split_pairs {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {k : Kind} (hk : k ≠ Kind.imm) {A : Type} {w : List (Loc × A)}
    (hs : ρ.Sites k (w.map Prod.fst)) :
    ∃ w₁ w₂ : List (Loc × A), w.Perm (w₁ ++ w₂) ∧
      ρ₁.Sites k (w₁.map Prod.fst) ∧ ρ₂.Sites k (w₂.map Prod.fst) ∧
      (∀ p ∈ w₁, p ∈ w) ∧ (∀ p ∈ w₂, p ∈ w) := by
  obtain ⟨w₁, w₂, hp, hm₁, hm₂⟩ :=
    List.split_by_key (fun l => ∃ ψ, ρ₁.get l = some ψ ∧ ψ.kind = k) w
  -- The key lists inherit duplicate-freeness from `hs` along `hp`.
  have hnd : ((w₁.map Prod.fst) ++ (w₂.map Prod.fst)).Nodup := by
    rw [← List.map_append]
    exact (hp.map Prod.fst).nodup hs.1
  obtain ⟨nd₁, nd₂, -⟩ := List.nodup_append.mp hnd
  refine ⟨w₁, w₂, hp, ⟨nd₁, fun l => ⟨?_, ?_⟩⟩, ⟨nd₂, fun l => ⟨?_, ?_⟩⟩,
    fun p hp' => ((hm₁ p).mp hp').1, fun p hp' => ((hm₂ p).mp hp').1⟩
  · intro hl
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hl
    exact ((hm₁ p).mp hp').2
  · intro hl
    obtain ⟨ψ, g, gk⟩ := hl
    have hρ : ρ.get l = some ψ :=
      (ResU.CompS.get_left_of_ne_imm h g (fun e => hk (gk.symm.trans e))).2
    obtain ⟨p, hp', hp1⟩ := List.mem_map.mp ((hs.2 l).mpr ⟨ψ, hρ, gk⟩)
    exact List.mem_map.mpr ⟨p, (hm₁ p).mpr ⟨hp', hp1 ▸ ⟨ψ, g, gk⟩⟩, hp1⟩
  · intro hl
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hl
    obtain ⟨hpw, hq⟩ := (hm₂ p).mp hp'
    obtain ⟨ψ, g, gk⟩ := (hs.2 p.1).mp (List.mem_map.mpr ⟨p, hpw, rfl⟩)
    rcases ResU.CompS.get_split_of_ne_imm h g (fun e => hk (gk.symm.trans e)) with
      ⟨g₁, -⟩ | ⟨-, g₂⟩
    · exact absurd ⟨ψ, g₁, gk⟩ hq
    · exact ⟨ψ, g₂, gk⟩
  · intro hl
    obtain ⟨ψ, g, gk⟩ := hl
    have hρ : ρ.get l = some ψ :=
      (ResU.CompS.get_right_of_ne_imm h g (fun e => hk (gk.symm.trans e))).2
    have hnone : ρ₁.get l = none :=
      (ResU.CompS.get_right_of_ne_imm h g (fun e => hk (gk.symm.trans e))).1
    obtain ⟨p, hp', hp1⟩ := List.mem_map.mp ((hs.2 l).mpr ⟨ψ, hρ, gk⟩)
    refine List.mem_map.mpr ⟨p, (hm₂ p).mpr ⟨hp', ?_⟩, hp1⟩
    rintro ⟨χ, gχ, -⟩
    rw [hp1, hnone] at gχ
    exact absurd gχ (by simp)

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}
variable {R : CellU Loc Val → CellU Loc Val → Prop}
variable {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}

/-- The mirror of `ExWits.of_compS_left`. -/
theorem ExWits.of_compS_right {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w : List (Loc × ResU Loc Val)} (hw : ExWits R C ρ₂ w) : ExWits R C ρ w :=
  ExWits.of_compS_left (ResU.CompS.comm h) hw

/-- The mirror of `ExWits.to_compS_left`. -/
theorem ExWits.to_compS_right {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w w₂ : List (Loc × ResU Loc Val)} (hw : ExWits R C ρ w)
    (hsub : ∀ p ∈ w₂, p ∈ w) (hs₂ : ρ₂.Sites Kind.mut (w₂.map Prod.fst)) :
    ExWits R C ρ₂ w₂ :=
  ExWits.to_compS_left (ResU.CompS.comm h) hw hsub hs₂

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### Lemma 6.18's declaration, ahead of its subsection

`[TR]` prints Lemma 6.18 in §6.2 (p. 8).  The Lean of Lemmas 6.7, 6.8, 6.10, 6.11 and 6.15 in this file needs it, so it is declared here; its statement, printed proof and alias are in `Paper/S6_2_NonStandardLemmas/Lemmas.lean`.
-/
/-- **`[TR]` Lemma 6.18** (p. 8): if `ρ₁ ▸◂ ρ₂` then `ex(ρ₁ ● ρ₂)_●` and
`ex(ρ₁)_● ● ex(ρ₂)_●` are Kleene-equal.  `[as printed]` (as a graph — G4) -/
theorem ExS.split {ρ₁ ρ₂ ρ₁₂ w : ResU Loc Val} (h₁₂ : ResU.CompS ρ₁ ρ₂ ρ₁₂) :
    ExS ρ₁₂ w ↔ ∃ σ₁ σ₂, ExS ρ₁ σ₁ ∧ ExS ρ₂ σ₂ ∧ ResU.CompS σ₁ σ₂ w := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompS ψ₁ ψ₂ ψ → CellU.CompatS ψ₁ ψ₂ :=
    fun _ _ _ hc => CellU.CompS.compat hc
  -- The printed second line, at `own` and at `mut`.
  have hown : ResU.CompS (ρ₁.restrict Kind.own) (ρ₂.restrict Kind.own)
      (ρ₁₂.restrict Kind.own) := ResU.CompS.restrict h₁₂ Kind.own
  have hmut : ResU.CompS (ρ₁.restrict Kind.mut) (ρ₂.restrict Kind.mut)
      (ρ₁₂.restrict Kind.mut) := ResU.CompS.restrict h₁₂ Kind.mut
  constructor
  · -- `ex(ρ₁₂)_●` is defined: cut its index set, its family and its fold in two,
    -- then exchange twice.
    intro h
    cases h with
    | mk hs hw hb hnm hσ =>
        rename_i u
        obtain ⟨u₁, u₂, hperm, hs₁, hs₂, hsub₁, hsub₂⟩ :=
          ResU.Sites.split_pairs h₁₂ Kind.mut_ne_imm hs
        have hperm' : (u.map Prod.snd).Perm (u₁.map Prod.snd ++ u₂.map Prod.snd) := by
          rw [← List.map_append]
          exact hperm.map Prod.snd
        obtain ⟨b₁, b₂, hb₁, hb₂, hbc⟩ :=
          (BigComp.append hR ResU.compLawsS).mp
            (BigComp.of_perm hR ResU.compLawsS hperm' hb)
        -- The printed third line.
        obtain ⟨nm₁, nm₂, hnm₁, hnm₂, hnmc⟩ :=
          (ResU.CompS.exchange₄ _ _ _ _ _).mp ⟨_, _, hown, hmut, hnm⟩
        -- The printed fourth line.
        obtain ⟨σ₁, σ₂, hσ₁, hσ₂, hσc⟩ :=
          (ResU.CompS.exchange₄ nm₁ nm₂ b₁ b₂ w).mp ⟨_, _, hnmc, hbc, hσ⟩
        exact ⟨σ₁, σ₂,
          ExW.mk hs₁ (ExWits.to_compS_left h₁₂ hw hsub₁ hs₁) hb₁ hnm₁ hσ₁,
          ExW.mk hs₂ (ExWits.to_compS_right h₁₂ hw hsub₂ hs₂) hb₂ hnm₂ hσ₂,
          hσc⟩
  · -- Both operands' walks are defined and compose: assemble the composite's
    -- index set, family and fold, then run the same two exchanges backwards.
    rintro ⟨σ₁, σ₂, h₁, h₂, hc⟩
    cases h₁ with
    | mk hs₁ hw₁ hb₁ hnm₁ hσ₁ =>
        rename_i u₁
        cases h₂ with
        | mk hs₂ hw₂ hb₂ hnm₂ hσ₂ =>
            rename_i u₂
            -- The printed fourth line, read right to left.
            obtain ⟨nm, b, hnmc, hbc, hσ⟩ :=
              (ResU.CompS.exchange₄ _ _ _ _ w).mpr ⟨σ₁, σ₂, hσ₁, hσ₂, hc⟩
            -- The printed third line, read right to left; the two composites it
            -- produces are `ρ₁₂|own` and `ρ₁₂|mut` by single-valuedness of `●`.
            obtain ⟨O, M, hO, hM, hOM⟩ :=
              (ResU.CompS.exchange₄ _ _ _ _ nm).mpr ⟨_, _, hnm₁, hnm₂, hnmc⟩
            obtain rfl : O = ρ₁₂.restrict Kind.own := ResU.CompS.functional hO hown
            obtain rfl : M = ρ₁₂.restrict Kind.mut := ResU.CompS.functional hM hmut
            refine ExW.mk (w := u₁ ++ u₂) ?_
              (ExWits.append (ExWits.of_compS_left h₁₂ hw₁)
                (ExWits.of_compS_right h₁₂ hw₂)) ?_ hOM hσ
            · rw [List.map_append]
              exact ResU.Sites.append_of_compS h₁₂ Kind.mut_ne_imm hs₁ hs₂
            · rw [List.map_append]
              exact (BigComp.append hR ResU.compLawsS).mpr ⟨_, _, hb₁, hb₂, hbc⟩

/-! `[about ours]` — what the Lean of Lemma 6.7 needs; the paper prints nothing here. -/
/-- The mirror of `AgWitsM.of_compS_left`. -/
theorem AgWitsM.of_compS_right {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w : List (Loc × ResU Loc Val)} (hw : AgWitsM ρ₂ w) : AgWitsM ρ w :=
  AgWitsM.of_compS_left (ResU.CompS.comm h) hw

/-- The mirror of `AgWitsI.of_compS_left`. -/
theorem AgWitsI.of_compS_right {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w : List (Loc × ResU Loc Val)} (hw : AgWitsI ρ₂ w) : AgWitsI ρ w :=
  AgWitsI.of_compS_left (ResU.CompS.comm h) hw

/-- The mirror of `AgWitsM.to_compS_left`. -/
theorem AgWitsM.to_compS_right {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w w₂ : List (Loc × ResU Loc Val)} (hw : AgWitsM ρ w)
    (hsub : ∀ p ∈ w₂, p ∈ w) (hs₂ : ρ₂.Sites Kind.mut (w₂.map Prod.fst)) :
    AgWitsM ρ₂ w₂ :=
  AgWitsM.to_compS_left (ResU.CompS.comm h) hw hsub hs₂

/-- The mirror of `AgWitsI.to_compS_left`. -/
theorem AgWitsI.to_compS_right {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w w₂ : List (Loc × ResU Loc Val)} (hw : AgWitsI ρ w)
    (hsub : ∀ p ∈ w₂, p ∈ w) (hs₂ : ρ₂.Sites Kind.imm (w₂.map Prod.fst)) :
    AgWitsI ρ₂ w₂ :=
  AgWitsI.to_compS_left (ResU.CompS.comm h) hw hsub hs₂

/-- **The value the `imm` half pairs with a location depends only on the cell's
witness.**  This is what makes [TR] 6.20's `ρ₁ ∩ ρ₂` term *one* term rather than
two: the entry `ex(ρ′)_○ ○ ag(ρ′)` is the same on either side of the overlap, so
Lemma 6.19 can duplicate it.  `ExR.functional` and `AgW.functional` fix
the two halves, and `ResU.CompR.functional` their composite.
`[about ours: `AgWitsI` is the family relation; the printed 6.19 is
`ResU.flatR_idem`]` -/
theorem AgWitsI.value_functional {ρ ρ' : ResU Loc Val}
    {w w' : List (Loc × ResU Loc Val)} (h : AgWitsI ρ w) (h' : AgWitsI ρ' w')
    {p q : Loc × ResU Loc Val} (hp : p ∈ w) (hq : q ∈ w')
    {ψ χ : CellU Loc Val} (hψ : ρ.get p.1 = some ψ) (hχ : ρ'.get q.1 = some χ)
    (hwit : ψ.wit = χ.wit) : p.2 = q.2 := by
  obtain ⟨ψ₀, g, -, e, a, hex, hag, hc⟩ := AgWitsI.iff_mem.mp h p hp
  obtain ⟨χ₀, g', -, e', a', hex', hag', hc'⟩ := AgWitsI.iff_mem.mp h' q hq
  rw [hψ] at g; obtain rfl := Option.some.inj g
  rw [hχ] at g'; obtain rfl := Option.some.inj g'
  have hee : e = e' := ExR.functional hex (by rw [← hwit] at hex'; exact hex')
  have haa : a = a' := AgW.functional hag (by rw [← hwit] at hag'; exact hag')
  exact ResU.CompR.functional hc (hee ▸ haa ▸ hc')

/-- **The `imm` locations of `ρ₁ ● ρ₂` are the union of those of `ρ₁` and
`ρ₂`.**  Union, not disjoint union: both disjuncts can hold at once, and that is
the whole difference between 6.20 and 6.18.
`[about ours: the printed `▶◀` and `●` read at the `imm` tag; no printed row
states it]` -/
theorem ResU.CompS.imm_site_iff {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    (l : Loc) :
    (∃ ψ, ρ.get l = some ψ ∧ ψ.kind = Kind.imm) ↔
      ((∃ ψ, ρ₁.get l = some ψ ∧ ψ.kind = Kind.imm) ∨
        (∃ ψ, ρ₂.get l = some ψ ∧ ψ.kind = Kind.imm)) := by
  constructor
  · rintro ⟨ψ, g, gk⟩
    rcases ResU.Comp.get h l with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
        ⟨χ₁, χ₂, χ, f₁, -, -, hC⟩
    · rw [g] at f; exact absurd f (by simp)
    · obtain rfl : ψ = χ := Option.some.inj (g.symm.trans f)
      exact Or.inl ⟨ψ, f₁, gk⟩
    · obtain rfl : ψ = χ := Option.some.inj (g.symm.trans f)
      exact Or.inr ⟨ψ, f₂, gk⟩
    · exact Or.inl ⟨χ₁, f₁, (CellU.CompatS.kinds (CellU.CompS.compat hC)).1⟩
  · rintro (⟨ψ, g, gk⟩ | ⟨ψ, g, gk⟩)
    · obtain ⟨χ, f, fk, -⟩ := ResU.CompS.get_left h g
      exact ⟨χ, f, fk.trans gk⟩
    · obtain ⟨χ, f, fk, -⟩ := ResU.CompS.get_right h g
      exact ⟨χ, f, fk.trans gk⟩

/-- **A family over the `imm` sites of `ρ₁ ● ρ₂` cuts into three blocks** — over
`ρ₁` alone, over `ρ₂` alone, and over both — with `ρ₁`'s own index set the first
block together with the third, and `ρ₂`'s the second with the third.  This is
[TR] 6.20's inclusion-exclusion, at the index sets.
`[about ours: `ResU.Sites` is convention G6's index set; this is 6.20's
inclusion-exclusion read at the index sets]` -/
theorem ResU.Sites.split_pairs_imm {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {A : Type} {w : List (Loc × A)} (hs : ρ.Sites Kind.imm (w.map Prod.fst)) :
    ∃ wa wb wc : List (Loc × A), w.Perm (wa ++ (wb ++ wc)) ∧
      ρ₁.Sites Kind.imm ((wa ++ wc).map Prod.fst) ∧
      ρ₂.Sites Kind.imm ((wb ++ wc).map Prod.fst) ∧
      (∀ p ∈ wa, p ∈ w) ∧ (∀ p ∈ wb, p ∈ w) ∧ (∀ p ∈ wc, p ∈ w) := by
  classical
  -- `u` is the part of `w` lying over `ρ₁` and `wb` the rest; `u` then splits by
  -- whether the location lies over `ρ₂` as well.
  obtain ⟨u, wb, hpu, hmu, hmb⟩ :=
    List.split_by_key (fun l => ∃ ψ, ρ₁.get l = some ψ ∧ ψ.kind = Kind.imm) w
  obtain ⟨wc, wa, hpc, hmc, hma⟩ :=
    List.split_by_key (fun l => ∃ ψ, ρ₂.get l = some ψ ∧ ψ.kind = Kind.imm) u
  have hperm : w.Perm (wa ++ (wb ++ wc)) := by
    refine hpu.trans ((hpc.append_right wb).trans ?_)
    rw [List.append_assoc, ← List.append_assoc wa wb wc]
    exact List.perm_append_comm
  have hsubw : ∀ p ∈ u, p ∈ w := fun p hp => ((hmu p).mp hp).1
  have hsuba : ∀ p ∈ wa, p ∈ w := fun p hp => hsubw p ((hma p).mp hp).1
  have hsubb : ∀ p ∈ wb, p ∈ w := fun p hp => ((hmb p).mp hp).1
  have hsubc : ∀ p ∈ wc, p ∈ w := fun p hp => hsubw p ((hmc p).mp hp).1
  -- Duplicate-freeness of the three key blocks, and their pairwise
  -- disjointness, travel from `hs` along the permutation.
  have hkeys : (w.map Prod.fst).Perm
      ((wa.map Prod.fst) ++ ((wb.map Prod.fst) ++ (wc.map Prod.fst))) := by
    have hm := hperm.map Prod.fst
    rwa [List.map_append, List.map_append] at hm
  obtain ⟨nda, ndbc, hdis⟩ := List.nodup_append.mp (hkeys.nodup hs.1)
  obtain ⟨ndb, ndc, hdbc⟩ := List.nodup_append.mp ndbc
  have hcov : ∀ p ∈ w, (∃ ψ, ρ₁.get p.1 = some ψ ∧ ψ.kind = Kind.imm) ∨
      (∃ ψ, ρ₂.get p.1 = some ψ ∧ ψ.kind = Kind.imm) := fun p hp =>
    (ResU.CompS.imm_site_iff h p.1).mp ((hs.2 p.1).mp (List.mem_map.mpr ⟨p, hp, rfl⟩))
  refine ⟨wa, wb, wc, hperm, ⟨?_, fun l => ⟨?_, ?_⟩⟩, ⟨?_, fun l => ⟨?_, ?_⟩⟩,
    hsuba, hsubb, hsubc⟩
  · rw [List.map_append]
    exact List.nodup_append.mpr ⟨nda, ndc, fun a ha b hb =>
      hdis a ha b (List.mem_append.mpr (Or.inr hb))⟩
  · intro hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
    rcases List.mem_append.mp hp with hp | hp
    · exact ((hmu p).mp ((hma p).mp hp).1).2
    · exact ((hmu p).mp ((hmc p).mp hp).1).2
  · intro hl
    obtain ⟨p, hp, hp1⟩ :=
      List.mem_map.mp ((hs.2 l).mpr ((ResU.CompS.imm_site_iff h l).mpr (Or.inl hl)))
    have hpu' : p ∈ u := (hmu p).mpr ⟨hp, hp1 ▸ hl⟩
    refine List.mem_map.mpr ⟨p, ?_, hp1⟩
    by_cases hq : ∃ ψ, ρ₂.get p.1 = some ψ ∧ ψ.kind = Kind.imm
    · exact List.mem_append.mpr (Or.inr ((hmc p).mpr ⟨hpu', hq⟩))
    · exact List.mem_append.mpr (Or.inl ((hma p).mpr ⟨hpu', hq⟩))
  · rw [List.map_append]
    exact List.nodup_append.mpr ⟨ndb, ndc, hdbc⟩
  · intro hl
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨hpw, hnq⟩ := (hmb p).mp hp
      exact (hcov p hpw).resolve_left hnq
    · exact ((hmc p).mp hp).2
  · intro hl
    obtain ⟨p, hp, hp1⟩ :=
      List.mem_map.mp ((hs.2 l).mpr ((ResU.CompS.imm_site_iff h l).mpr (Or.inr hl)))
    refine List.mem_map.mpr ⟨p, ?_, hp1⟩
    by_cases hq : ∃ ψ, ρ₁.get l = some ψ ∧ ψ.kind = Kind.imm
    · exact List.mem_append.mpr (Or.inr ((hmc p).mpr ⟨(hmu p).mpr ⟨hp, hp1 ▸ hq⟩, hp1 ▸ hl⟩))
    · exact List.mem_append.mpr (Or.inl ((hmb p).mpr ⟨hp, hp1 ▸ hq⟩))

/-- **`⨀(l ++ (m ++ m)) = ⨀(l ++ m)` at `○`** — a repeated block folds to what
one copy folds to.  At `○` this needs no hypothesis: `ResU.compR_self` says
`ρ ○ ρ = ρ` for every `ρ`, which is clause (1) of `○` read pointwise, and [TR]
Lemma 6.19 is its instance at `⦇ρ⦈_○`.
`[about ours: `BigComp` is the fold shape; the printed 6.19 is
`ResU.flatR_idem`, and this is the fold-level fact 6.20 spends it on]` -/
theorem BigComp.dupR {l m : List (ResU Loc Val)} {x : ResU Loc Val} :
    BigComp CellU.CompatR CellU.CompR (l ++ (m ++ m)) x ↔
      BigComp CellU.CompatR CellU.CompR (l ++ m) x := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  rw [BigComp.append hR ResU.compLawsR, BigComp.append hR ResU.compLawsR]
  refine ⟨fun ⟨L, Y, hL, hY, hx⟩ => ?_, fun ⟨L, M, hL, hM, hx⟩ => ?_⟩
  · obtain ⟨M₁, M₂, hM₁, hM₂, hMc⟩ := (BigComp.append hR ResU.compLawsR).mp hY
    obtain rfl : M₁ = M₂ := BigComp.functional ResU.compLawsR hM₁ hM₂
    obtain rfl : Y = M₁ := ResU.CompR.functional hMc (ResU.compR_self M₁)
    exact ⟨L, Y, hL, hM₁, hx⟩
  · exact ⟨L, M, hL,
      (BigComp.append hR ResU.compLawsR).mpr ⟨M, M, hM, hM, ResU.compR_self M⟩, hx⟩

/-- **A block already present may be appended again**, at `○`: if `d` is, up to
order, one of the blocks of `l`, then `⨀(l ++ d) = ⨀l`.  This is
`BigComp.dupR` with the repetition located inside a larger fold, which is the
shape [TR] 6.20's converse takes — only the `ρ₁ ∩ ρ₂` block is doubled, not the
whole composite.
`[about ours: `BigComp` is the fold shape; the printed 6.19 is
`ResU.flatR_idem`]` -/
theorem BigComp.dup_of_perm {l m d : List (ResU Loc Val)} (hp : l.Perm (m ++ d))
    {x : ResU Loc Val} :
    BigComp CellU.CompatR CellU.CompR (l ++ d) x ↔
      BigComp CellU.CompatR CellU.CompR l x := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  have h₁ : (l ++ d).Perm (m ++ (d ++ d)) := by
    rw [← List.append_assoc]
    exact hp.append_right d
  constructor
  · intro h
    exact BigComp.of_perm hR ResU.compLawsR hp.symm
      (BigComp.dupR.mp (BigComp.of_perm hR ResU.compLawsR h₁ h))
  · intro h
    exact BigComp.of_perm hR ResU.compLawsR h₁.symm
      (BigComp.dupR.mpr (BigComp.of_perm hR ResU.compLawsR hp h))

/-- The exchange of the middle two factors at `○`, which is the one [TR] 6.20
uses.
`[about ours: `ResU.Comp.exchange₄` instantiated at `○`]` -/
theorem ResU.CompR.exchange₄ (a₁ a₂ b₁ b₂ x : ResU Loc Val) :
    (∃ A B, ResU.CompR a₁ a₂ A ∧ ResU.CompR b₁ b₂ B ∧ ResU.CompR A B x) ↔
      (∃ S₁ S₂, ResU.CompR a₁ b₁ S₁ ∧ ResU.CompR a₂ b₂ S₂ ∧ ResU.CompR S₁ S₂ x) :=
  ResU.Comp.exchange₄ (fun _ _ ψ hc => ⟨ψ, hc⟩) ResU.compLawsR a₁ a₂ b₁ b₂ x

/-- **The composite's `imm` family, assembled from the two operands'.**  `w₂a`
is the part of `ρ₂`'s family at locations `ρ₁` does not carry, `w₂c` the part it
does, and `w₁c` the block of `ρ₁`'s family sitting over the same locations —
which `w₂c` permutes, so `⨀` cannot tell them apart.  `w₁ ++ w₂a` is then a
family for `ρ₁₂` over its whole `imm` index set.
`[about ours: `ResU.Sites` is convention G6's index set and `AgWitsI`
the family; this is 6.20's inclusion-exclusion read in the assembling
direction]` -/
theorem AgWitsI.assemble {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {w₁ w₂ : List (Loc × ResU Loc Val)}
    (hs₁ : ρ₁.Sites Kind.imm (w₁.map Prod.fst)) (hw₁ : AgWitsI ρ₁ w₁)
    (hs₂ : ρ₂.Sites Kind.imm (w₂.map Prod.fst)) (hw₂ : AgWitsI ρ₂ w₂) :
    ∃ w₂a w₂c w₁r w₁c : List (Loc × ResU Loc Val),
      w₂.Perm (w₂a ++ w₂c) ∧ w₁.Perm (w₁r ++ w₁c) ∧ w₁c.Perm w₂c ∧
      ρ.Sites Kind.imm ((w₁ ++ w₂a).map Prod.fst) ∧
      AgWitsI ρ (w₁ ++ w₂a) := by
  classical
  -- `w₂c` is the shared block of `ρ₂`'s family, `w₁c` the matching block of
  -- `ρ₁`'s.  Each is cut by asking whether the *other* operand is `imm` there.
  obtain ⟨w₂c, w₂a, hp2, hm2c, hm2a⟩ :=
    List.split_by_key (fun l => ∃ ψ, ρ₁.get l = some ψ ∧ ψ.kind = Kind.imm) w₂
  obtain ⟨w₁c, w₁r, hp1, hm1c, -⟩ :=
    List.split_by_key (fun l => ∃ ψ, ρ₂.get l = some ψ ∧ ψ.kind = Kind.imm) w₁
  have hperm2 : w₂.Perm (w₂a ++ w₂c) := hp2.trans List.perm_append_comm
  have hperm1 : w₁.Perm (w₁r ++ w₁c) := hp1.trans List.perm_append_comm
  have hsub2a : ∀ p ∈ w₂a, p ∈ w₂ := fun p hp => ((hm2a p).mp hp).1
  -- Key lists inherit duplicate-freeness from the two `ResU.Sites`.
  have hk2 : ((w₂a.map Prod.fst) ++ (w₂c.map Prod.fst)).Nodup := by
    rw [← List.map_append]
    exact ((hperm2.map Prod.fst)).nodup hs₂.1
  obtain ⟨nd2a, nd2c, -⟩ := List.nodup_append.mp hk2
  have hk1 : ((w₁r.map Prod.fst) ++ (w₁c.map Prod.fst)).Nodup := by
    rw [← List.map_append]
    exact ((hperm1.map Prod.fst)).nodup hs₁.1
  obtain ⟨-, nd1c, -⟩ := List.nodup_append.mp hk1
  -- Both shared blocks are indexed by the locations `imm` in *both* operands.
  have hkey : ∀ l, l ∈ w₁c.map Prod.fst ↔ l ∈ w₂c.map Prod.fst := by
    intro l
    constructor
    · intro hl
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
      obtain ⟨hp1, hq2⟩ := (hm1c p).mp hp
      obtain ⟨q, hq, hq1⟩ := List.mem_map.mp ((hs₂.2 p.1).mpr hq2)
      exact List.mem_map.mpr ⟨q, (hm2c q).mpr ⟨hq, hq1 ▸
        (hs₁.2 p.1).mp (List.mem_map.mpr ⟨p, hp1, rfl⟩)⟩, hq1⟩
    · intro hl
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
      obtain ⟨hq2, hp1⟩ := (hm2c q).mp hq
      obtain ⟨p, hp, hp1'⟩ := List.mem_map.mp ((hs₁.2 q.1).mpr hp1)
      exact List.mem_map.mpr ⟨p, (hm1c p).mpr ⟨hp, hp1' ▸
        (hs₂.2 q.1).mp (List.mem_map.mpr ⟨q, hq2, rfl⟩)⟩, hp1'⟩
  -- At a shared location the two cells have one witness, so the two families
  -- pair the same value with it.
  have hval : ∀ p ∈ w₁c, ∀ q ∈ w₂c, p.1 = q.1 → p.2 = q.2 := by
    intro p hp q hq hpq
    obtain ⟨hp1, -⟩ := (hm1c p).mp hp
    obtain ⟨hq2, -⟩ := (hm2c q).mp hq
    obtain ⟨ψ₁, g₁, -⟩ := (hs₁.2 p.1).mp (List.mem_map.mpr ⟨p, hp1, rfl⟩)
    obtain ⟨ψ₂, g₂, -⟩ := (hs₂.2 q.1).mp (List.mem_map.mpr ⟨q, hq2, rfl⟩)
    exact AgWitsI.value_functional hw₁ hw₂ hp1 hq2 g₁ g₂
      (ResU.CompatS.wit_of_overlap h.1 g₁ (hpq ▸ g₂))
  refine ⟨w₂a, w₂c, w₁r, w₁c, hperm2, hperm1,
    List.perm_of_keys_mem nd1c nd2c hkey hval, ⟨?_, fun l => ⟨?_, ?_⟩⟩, ?_⟩
  · -- `w₁`'s keys and `w₂a`'s are disjoint: every `w₁` key is `imm` in `ρ₁`,
    -- and no `w₂a` key is.
    rw [List.map_append]
    refine List.nodup_append.mpr ⟨hs₁.1, nd2a, fun a ha b hb hab => ?_⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
    exact ((hm2a q).mp hq).2 (hab ▸ (hs₁.2 a).mp ha)
  · intro hl
    rw [List.map_append] at hl
    rcases List.mem_append.mp hl with hl | hl
    · exact (ResU.CompS.imm_site_iff h l).mpr (Or.inl ((hs₁.2 l).mp hl))
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
      exact (ResU.CompS.imm_site_iff h q.1).mpr
        (Or.inr ((hs₂.2 q.1).mp (List.mem_map.mpr ⟨q, hsub2a q hq, rfl⟩)))
  · intro hl
    rw [List.map_append]
    rcases (ResU.CompS.imm_site_iff h l).mp hl with hq | hq
    · exact List.mem_append.mpr (Or.inl ((hs₁.2 l).mpr hq))
    · by_cases hq₁ : ∃ ψ, ρ₁.get l = some ψ ∧ ψ.kind = Kind.imm
      · exact List.mem_append.mpr (Or.inl ((hs₁.2 l).mpr hq₁))
      · obtain ⟨q, hq', hq1⟩ := List.mem_map.mp ((hs₂.2 l).mpr hq)
        exact List.mem_append.mpr (Or.inr
          (List.mem_map.mpr ⟨q, (hm2a q).mpr ⟨hq', hq1 ▸ hq₁⟩, hq1⟩))
  · exact AgWitsI.append (AgWitsI.of_compS_left h hw₁)
      (AgWitsI.of_compS_right h (AgWitsI.subset hw₂ hsub2a))

/-- **The exchange when one factor is shared**, at `○`:

    A ◐ (B ◐ C)  =  (A ◐ C) ◐ (B ◐ C),

as a Kleene equality.  `C` occurs once on the left and twice on the right; at
`○` that costs nothing, because a repeated block folds to one copy
(`BigComp.dup_of_perm`, whose printed row is Lemma 6.19).  This is the whole
content of [TR] 6.20's inclusion-exclusion once the index sets have been cut.
`[about ours: the rearrangement 6.20's proof performs on the `imm` families;
the printed rows behind it are 6.2, 6.3 and 6.19]` -/
theorem ResU.CompR.exchange₃dup (A B C x : ResU Loc Val) :
    (∃ Y, ResU.CompR B C Y ∧ ResU.CompR A Y x) ↔
      (∃ S₁ S₂, ResU.CompR A C S₁ ∧ ResU.CompR B C S₂ ∧ ResU.CompR S₁ S₂ x) := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  have hleft : (∃ Y, ResU.CompR B C Y ∧ ResU.CompR A Y x) ↔
      BigComp CellU.CompatR CellU.CompR [A, B, C] x := by
    constructor
    · rintro ⟨Y, hY, hx⟩
      exact BigComp.cons (BigComp.pair ResU.compLawsR |>.mpr hY) hx
    · intro h
      cases h with
      | cons ht hx => exact ⟨_, BigComp.pair ResU.compLawsR |>.mp ht, hx⟩
  have hright : (∃ S₁ S₂, ResU.CompR A C S₁ ∧ ResU.CompR B C S₂ ∧ ResU.CompR S₁ S₂ x) ↔
      BigComp CellU.CompatR CellU.CompR [A, C, B, C] x := by
    rw [show ([A, C, B, C] : List (ResU Loc Val)) = [A, C] ++ [B, C] from rfl,
      BigComp.append hR ResU.compLawsR]
    exact ⟨fun ⟨S₁, S₂, h₁, h₂, hx⟩ =>
        ⟨S₁, S₂, BigComp.pair ResU.compLawsR |>.mpr h₁,
          BigComp.pair ResU.compLawsR |>.mpr h₂, hx⟩,
      fun ⟨S₁, S₂, h₁, h₂, hx⟩ =>
        ⟨S₁, S₂, BigComp.pair ResU.compLawsR |>.mp h₁,
          BigComp.pair ResU.compLawsR |>.mp h₂, hx⟩⟩
  -- `[A, C, B, C]` is `[A, B, C]` with its own last entry appended again.
  have hp : ([A, C, B, C] : List (ResU Loc Val)).Perm ([A, B, C] ++ [C]) :=
    List.Perm.cons A (List.Perm.swap B C [C])
  have hd : BigComp CellU.CompatR CellU.CompR ([A, B, C] ++ [C]) x ↔
      BigComp CellU.CompatR CellU.CompR [A, B, C] x :=
    BigComp.dup_of_perm (m := [A, B]) (List.Perm.refl _)
  rw [hleft, hright]
  exact ⟨fun h => BigComp.of_perm hR ResU.compLawsR hp.symm (hd.mpr h),
    fun h => hd.mp (BigComp.of_perm hR ResU.compLawsR hp h)⟩

/-!
### Lemma 6.20's declaration, ahead of its subsection

`[TR]` prints Lemma 6.20 in §6.2 (p. 9).  The Lean of Lemmas 6.7, 6.8, 6.10, 6.11 and 6.15 in this file needs it, so it is declared here; its statement, printed proof and alias are in `Paper/S6_2_NonStandardLemmas/Lemmas.lean`.
-/
/-- **`[TR]` Lemma 6.20** (p. 9): if `ρ₁ ▸◂ ρ₂` then `ag(ρ₁ ● ρ₂)` and
`ag(ρ₁) ○ ag(ρ₂)` are Kleene-equal.  The hypothesis is at `●` and the
conclusion composes at `○`, as printed.  `[as printed]` (as a graph — G4) -/
theorem AgW.split {ρ₁ ρ₂ ρ₁₂ w : ResU Loc Val} (h₁₂ : ResU.CompS ρ₁ ρ₂ ρ₁₂) :
    AgW ρ₁₂ w ↔ ∃ σ₁ σ₂, AgW ρ₁ σ₁ ∧ AgW ρ₂ σ₂ ∧ ResU.CompR σ₁ σ₂ w := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  have himm : ResU.CompR (ρ₁.restrict Kind.imm) (ρ₂.restrict Kind.imm)
      (ρ₁₂.restrict Kind.imm) := ResU.CompS.restrictR h₁₂ Kind.imm
  constructor
  · intro h
    cases h with
    | mk hsm hsi hwm hwi hbm hbi ha hσ =>
        rename_i wm wi
        -- The `mut` index set is cut in two, as in 6.18.
        obtain ⟨wm₁, wm₂, hpm, hsm₁, hsm₂, hsubm₁, hsubm₂⟩ :=
          ResU.Sites.split_pairs h₁₂ Kind.mut_ne_imm hsm
        have hpm' : (wm.map Prod.snd).Perm (wm₁.map Prod.snd ++ wm₂.map Prod.snd) := by
          rw [← List.map_append]
          exact hpm.map Prod.snd
        obtain ⟨bm₁, bm₂, hbm₁, hbm₂, hbmc⟩ :=
          (BigComp.append hR ResU.compLawsR).mp
            (BigComp.of_perm hR ResU.compLawsR hpm' hbm)
        -- The `imm` index set is cut in three: `ρ₁` alone, `ρ₂` alone, shared.
        obtain ⟨wa, wb, wc, hpi, hsi₁, hsi₂, hsuba, hsubb, hsubc⟩ :=
          ResU.Sites.split_pairs_imm h₁₂ hsi
        have hpi' : (wi.map Prod.snd).Perm
            (wa.map Prod.snd ++ (wb.map Prod.snd ++ wc.map Prod.snd)) := by
          rw [← List.map_append, ← List.map_append]
          exact hpi.map Prod.snd
        obtain ⟨A, X, hA, hX, hAX⟩ :=
          (BigComp.append hR ResU.compLawsR).mp
            (BigComp.of_perm hR ResU.compLawsR hpi' hbi)
        obtain ⟨B, Cc, hB, hCc, hBC⟩ := (BigComp.append hR ResU.compLawsR).mp hX
        -- The shared block is handed to both sides; this is 6.19's step.
        obtain ⟨bi₁, bi₂, hS₁, hS₂, hbic⟩ :=
          (ResU.CompR.exchange₃dup A B Cc _).mp ⟨X, hBC, hAX⟩
        have hbi₁ : BigComp CellU.CompatR CellU.CompR ((wa ++ wc).map Prod.snd) bi₁ := by
          rw [List.map_append]
          exact (BigComp.append hR ResU.compLawsR).mpr ⟨A, Cc, hA, hCc, hS₁⟩
        have hbi₂ : BigComp CellU.CompatR CellU.CompR ((wb ++ wc).map Prod.snd) bi₂ := by
          rw [List.map_append]
          exact (BigComp.append hR ResU.compLawsR).mpr ⟨B, Cc, hB, hCc, hS₂⟩
        -- The two exchanges of the print's final regrouping.
        obtain ⟨a₁, a₂, ha₁, ha₂, hac⟩ :=
          (ResU.CompR.exchange₄ _ _ _ _ _).mp ⟨_, _, himm, hbmc, ha⟩
        obtain ⟨σ₁, σ₂, hσ₁, hσ₂, hσc⟩ :=
          (ResU.CompR.exchange₄ a₁ a₂ bi₁ bi₂ w).mp ⟨_, _, hac, hbic, hσ⟩
        refine ⟨σ₁, σ₂,
          AgW.mk hsm₁ hsi₁ (AgWitsM.to_compS_left h₁₂ hwm hsubm₁ hsm₁)
            (AgWitsI.to_compS_left h₁₂ hwi ?_ hsi₁) hbm₁ hbi₁ ha₁ hσ₁,
          AgW.mk hsm₂ hsi₂ (AgWitsM.to_compS_right h₁₂ hwm hsubm₂ hsm₂)
            (AgWitsI.to_compS_right h₁₂ hwi ?_ hsi₂) hbm₂ hbi₂ ha₂ hσ₂,
          hσc⟩
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hsuba p hp
          · exact hsubc p hp
        · intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hsubb p hp
          · exact hsubc p hp
  · rintro ⟨σ₁, σ₂, h₁, h₂, hc⟩
    cases h₁ with
    | mk hsm₁ hsi₁ hwm₁ hwi₁ hbm₁ hbi₁ ha₁ hσ₁ =>
        rename_i wm₁ wi₁
        cases h₂ with
        | mk hsm₂ hsi₂ hwm₂ hwi₂ hbm₂ hbi₂ ha₂ hσ₂ =>
            rename_i wm₂ wi₂
            -- The two exchanges, read right to left.
            obtain ⟨a, bi, hac, hbic, hσ⟩ :=
              (ResU.CompR.exchange₄ _ _ _ _ w).mpr ⟨σ₁, σ₂, hσ₁, hσ₂, hc⟩
            obtain ⟨I, bm, hI, hbmc, ha⟩ :=
              (ResU.CompR.exchange₄ _ _ _ _ a).mpr ⟨_, _, ha₁, ha₂, hac⟩
            obtain rfl : I = ρ₁₂.restrict Kind.imm := ResU.CompR.functional hI himm
            -- The composite's `imm` family, assembled with its shared block named.
            obtain ⟨w₂a, w₂c, w₁r, w₁c, hperm2, hperm1, hcperm, hsi, hwi⟩ :=
              AgWitsI.assemble h₁₂ hsi₁ hwi₁ hsi₂ hwi₂
            refine AgW.mk (wm := wm₁ ++ wm₂) (wi := wi₁ ++ w₂a) ?_ hsi
              (AgWitsM.append (AgWitsM.of_compS_left h₁₂ hwm₁)
                (AgWitsM.of_compS_right h₁₂ hwm₂)) hwi ?_ ?_ ha hσ
            · rw [List.map_append]
              exact ResU.Sites.append_of_compS h₁₂ Kind.mut_ne_imm hsm₁ hsm₂
            · rw [List.map_append]
              exact (BigComp.append hR ResU.compLawsR).mpr ⟨_, _, hbm₁, hbm₂, hbmc⟩
            · -- `wi₁ ++ w₂a` folds to `bi` because the block `w₂c` that `ρ₂`'s
              -- family adds is, entry for entry, the block `w₁c` of `ρ₁`'s.
              have hsplit : (wi₁ ++ w₂a).Perm ((w₁r ++ w₂a) ++ w₂c) := by
                refine (hperm1.append_right w₂a).trans ?_
                refine ((hcperm.append_left w₁r).append_right w₂a).trans ?_
                rw [List.append_assoc, List.append_assoc]
                exact List.Perm.append_left w₁r List.perm_append_comm
              have hdup : ((wi₁ ++ w₂a).map Prod.snd).Perm
                  (((w₁r ++ w₂a).map Prod.snd) ++ (w₂c.map Prod.snd)) := by
                rw [← List.map_append]
                exact hsplit.map Prod.snd
              refine BigComp.dup_of_perm hdup |>.mp ?_
              rw [List.map_append, List.append_assoc, ← List.map_append]
              exact (BigComp.append hR ResU.compLawsR).mpr ⟨_, _, hbi₁,
                BigComp.of_perm hR ResU.compLawsR (hperm2.map Prod.snd) hbi₂, hbic⟩

/-! `[about ours]` — what the Lean of Lemma 6.7 needs; the paper prints nothing here. -/
/-- **`⦇ρ₁ ● ρ₂⦈ = ex(ρ₁)_● ● ex(ρ₂)_● ● (ag(ρ₁) ○ ag(ρ₂))`**, as a Kleene
equality — the expansion [TR] 6.15's proof (p. 8) opens with, obtained from 6.18
and 6.20 exactly as printed.  The mixed operators are the print's: the two
exclusive walks compose at `●` and the two aliasable walks at `○`.
`[about ours: the equation [TR] 6.15's proof obtains from 6.18 and 6.20; it
carries no numbered row of its own]` -/
theorem ResU.Flat.split {ρ₁ ρ₂ ρ₁₂ σ : ResU Loc Val} (h₁₂ : ResU.CompS ρ₁ ρ₂ ρ₁₂) :
    ResU.Flat ρ₁₂ σ ↔ ∃ e₁ e₂ e a₁ a₂ a,
      ExS ρ₁ e₁ ∧ ExS ρ₂ e₂ ∧ ResU.CompS e₁ e₂ e ∧
      AgW ρ₁ a₁ ∧ AgW ρ₂ a₂ ∧ ResU.CompR a₁ a₂ a ∧ ResU.CompS e a σ := by
  constructor
  · rintro ⟨e, a, he, ha, hc⟩
    obtain ⟨e₁, e₂, he₁, he₂, hec⟩ := (ExS.split h₁₂).mp he
    obtain ⟨a₁, a₂, ha₁, ha₂, hac⟩ := (AgW.split h₁₂).mp ha
    exact ⟨e₁, e₂, e, a₁, a₂, a, he₁, he₂, hec, ha₁, ha₂, hac, hc⟩
  · rintro ⟨e₁, e₂, e, a₁, a₂, a, he₁, he₂, hec, ha₁, ha₂, hac, hc⟩
    exact ⟨e, a, (ExS.split h₁₂).mpr ⟨e₁, e₂, he₁, he₂, hec⟩,
      (AgW.split h₁₂).mpr ⟨a₁, a₂, ha₁, ha₂, hac⟩, hc⟩

/-!
### Row 5.67's theorem `BoCa.Fig16.ResU.CompatS.disjoint_of_immFree`, ahead of its file

A remark on a printed definition of `[TR]` §5; its proof uses results of §6, and the Lean of Lemmas 6.7, 6.8, 6.10, 6.11 and 6.15 in this file needs it, so it is declared here.  The row is recorded in `Paper/S5_Model/Remarks.lean`.
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

/-!
### Lemma 6.30's declaration, ahead of its subsection

`[TR]` prints Lemma 6.30 in §6.2 (p. 11).  The Lean of Lemmas 6.7, 6.8, 6.10, 6.11 and 6.15 in this file needs it, so it is declared here; its statement, printed proof and alias are in `Paper/S6_2_NonStandardLemmas/Lemmas.lean`.
-/
/-- **`[TR]` Lemma 6.30** (p. 11): if `ρ ▸◂ (ρ₁ ○ ρ₂)` and `ρ|imm = ∅` then
`ρ ▸◂ ρ₁` and `ρ ▸◂ ρ₂`.  The proof is the print's: `ρ|imm = ∅` turns the
hypothesis into disjointness from the composite, the composite's domain is the
union of the operands' domains, so `ρ` is disjoint from each operand, and
disjoint resources are compatible.  `ρ|imm = ∅` is carried literally, as
`ResU.restrict` against `PMap.empty`; `ResU.restrict_imm_empty_iff` turns
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

/-! `[about ours]` — what the Lean of Lemma 6.7 needs; the paper prints nothing here. -/
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
`ResU.Flat.split` — together with the two composites
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

/-- **One half of `[TR]` Lemma 6.7** (p. 7): if `⟦ρ₁ ● ρ₂⟧` is defined then so
are `⟦ρ₁⟧` and `⟦ρ₂⟧`, and it is their union.  This half needs no `#` — a
lowering of `ρ₁ ● ρ₂` carries `✓(ρ₁ ● ρ₂)` inside it already — so the printed
hypothesis is not assumed here; `ResU.Lower.split` puts it back.

The proof is the print's case analysis.  `ResU.Flat.split_factors` supplies
`⦇ρ₁ ● ρ₂⦈ = ex(ρ₁)_● ● ex(ρ₂)_● ● (ag(ρ₁) ○ ag(ρ₂))` and, with it, the two
factorisations `⦇ρᵢ⦈ = ex(ρᵢ)_● ● ag(ρᵢ)`.  By 6.36 the exclusive part is
`imm`-free, hence disjoint from the aliasable part, so every location falls on
one side of the split the print opens with:

* off `dom(ex(ρ₁)_● ● ex(ρ₂)_●)`, all three flattenings are their aliasable
  parts, and the location's cells compose by `○` — the overlap case is the
  print's closing sentence, `⟦ag(ρ₁)(ℓ)⟧ = ⟦ag(ρ₂)(ℓ)⟧`;
* off `dom(ag(ρ₁) ○ ag(ρ₂))`, all three are their exclusive parts, and the
  cells compose by `●`.

Both are `optUnion_map_erase`, since `●` and `○` alike compose over one value.
`[restricted: the definedness-and-value half of the printed 6.7's Kleene
equality, with the printed `ρ₁ # ρ₂` weakened to `⟦ρ₁ ● ρ₂⟧` being defined]` -/
theorem ResU.Lower.split_left {ρ₁ ρ₂ ρ₁₂ : ResU Loc Val} {m : Loc → Option Val}
    (h : ResU.CompS ρ₁ ρ₂ ρ₁₂) (hm : ResU.Lower ρ₁₂ m) :
    ∃ m₁ m₂, ResU.Lower ρ₁ m₁ ∧ ResU.Lower ρ₂ m₂ ∧ MemUnion m₁ m₂ m := by
  obtain ⟨σ, hσ, hval⟩ := hm
  obtain ⟨e₁, e₂, e, a₁, a₂, a, σ₁, σ₂, he₁, he₂, hec, ha₁, ha₂, hac, hc, hσ₁, hσ₂⟩ :=
    ResU.Flat.split_factors h hσ
  have himm : e.ImmFree := ResU.ImmFree.compS hec (ExS.immFree he₁) (ExS.immFree he₂)
  -- The exclusive part and the aliasable part never meet.
  have hdisj := ResU.CompatS.disjoint_of_immFree himm hc.1
  refine ⟨fun l => (σ₁.get l).map CellU.erase, fun l => (σ₂.get l).map CellU.erase,
    ⟨σ₁, ⟨e₁, a₁, he₁, ha₁, hσ₁⟩, fun _ => rfl⟩,
    ⟨σ₂, ⟨e₂, a₂, he₂, ha₂, hσ₂⟩, fun _ => rfl⟩, ?_⟩
  intro l
  show OptUnion ((σ₁.get l).map CellU.erase) ((σ₂.get l).map CellU.erase) (m l)
  rcases hdisj l with hnoE | hnoA
  · obtain ⟨he₁l, he₂l⟩ := (ResU.Comp.eq_none_iff hec l).mp hnoE
    rw [hval l, ResU.Comp.get_of_left_none hc hnoE,
      ResU.Comp.get_of_left_none hσ₁ he₁l, ResU.Comp.get_of_left_none hσ₂ he₂l]
    exact optUnion_map_erase (fun _ _ _ hr => CellU.CompR.erase hr) (hac.2 l)
  · obtain ⟨ha₁l, ha₂l⟩ := (ResU.Comp.eq_none_iff hac l).mp hnoA
    rw [hval l, ResU.Comp.get_of_right_none hc hnoA,
      ResU.Comp.get_of_right_none hσ₁ ha₁l, ResU.Comp.get_of_right_none hσ₂ ha₂l]
    refine optUnion_map_erase (fun _ _ _ hs => ⟨?_, (CellU.CompS.erase hs).1⟩) (hec.2 l)
    exact (CellU.CompS.erase hs).1.symm.trans (CellU.CompS.erase hs).2

/-!
## Lemma 6.7 · `[TR]` p. 7 · `proved`

> If ρ₁ # ρ₂ then ⟦ρ₁ ● ρ₂⟧ = ⟦ρ₁⟧ ∪ ⟦ρ₂⟧.

**Printed proof, transcribed.** By Lemmas 6.20 and 6.18 with Lemma 6.36, every `ℓ ∈ dom(⟦ρ₁ ● ρ₂⟧)` is in `dom(ex(ρ₁)_●)`, in `dom(ex(ρ₂)_●)`, or in `dom(ag(ρ₁) ○ ag(ρ₂))`.  In the first two cases we are done; in the third we are done unless `ℓ ∈ dom(ag(ρ₁)) ∩ dom(ag(ρ₂))`, and then the definition of `○` gives `⟦ag(ρ₁)(ℓ)⟧ = ⟦ag(ρ₂)(ℓ)⟧`.

**Lean.** `BoCa.Fig16.ResU.Lower.split`, alias `TR.lemma_6_7`, tag `[as printed]`.

**Note.** `Fig16.ResU.Lower.split`, on the printed carrier, as one Kleene equality: both sides are partial terms, so the printed `=` is the `↔` between the two graphs at an arbitrary common result `m`, the shape of 6.18 and 6.20. `∪` is `Fig16.MemUnion`, the union of two partial maps written in `OptComp`'s shape, whose overlap clause `v₁ = v₂ ∧ o = some v₁` **asserts** the agreement the printed proof's last sentence establishes — a reading that left the overlap open would be weaker than the print. The hypotheses are the print's: `Fig16.ResU.Hash ρ₁ ρ₂` verbatim, and `Fig16.ResU.CompS ρ₁ ρ₂ ρ₁₂` naming `ρ₁ ● ρ₂` (G4), whose first conjunct is `#`'s own `▸◂`. The forward half needs no `#` and is carved out as `Fig16.ResU.Lower.split_left`, tagged `[restricted: …]`. `Fig16.LowerExample.split_overlap` runs the lemma on a `#`-pair that genuinely shares a location, so the row is not vacuous at the case the printed proof spends its last sentence on.
-/
/-- **`[TR]` Lemma 6.7** (p. 7): if `ρ₁ # ρ₂` then `⟦ρ₁ ● ρ₂⟧ = ⟦ρ₁⟧ ∪ ⟦ρ₂⟧`.
Both sides are partial terms, so — as with 6.18 and 6.20 — the printed
`=` is the Kleene equality of the two, which is this `↔` at an arbitrary common
result `m`: the left-hand side is defined with value `m` exactly when the right
is.  `MemUnion` is the union of partial maps on the right, and its overlap
clause carries the agreement the printed proof's last sentence establishes.
The forward half is
`ResU.Lower.split_left`, which needs no `#`; the printed `#` is spent on the
converse, where `✓(ρ₁ ● ρ₂)` — `#`'s second conjunct — is what makes the
left-hand side defined at all.
`[as printed]` (as a Kleene equality between graphs — G4; the printed
`ρ₁ ● ρ₂` is `ResU.CompS ρ₁ ρ₂ ρ₁₂`, whose own first conjunct is `#`'s `▸◂`) -/
theorem ResU.Lower.split {ρ₁ ρ₂ ρ₁₂ : ResU Loc Val} {m : Loc → Option Val}
    (h : ResU.CompS ρ₁ ρ₂ ρ₁₂) (hh : ResU.Hash ρ₁ ρ₂) :
    ResU.Lower ρ₁₂ m ↔
      ∃ m₁ m₂, ResU.Lower ρ₁ m₁ ∧ ResU.Lower ρ₂ m₂ ∧ MemUnion m₁ m₂ m := by
  refine ⟨ResU.Lower.split_left h, ?_⟩
  rintro ⟨m₁, m₂, k₁, k₂, ku⟩
  obtain ⟨-, ρ, hρ, σ, hσ⟩ := hh
  cases ResU.CompS.functional hρ h
  have hlow : ResU.Lower ρ₁₂ (fun l => (σ.get l).map CellU.erase) :=
    ⟨σ, hσ, fun _ => rfl⟩
  obtain ⟨n₁, n₂, j₁, j₂, ju⟩ := ResU.Lower.split_left h hlow
  cases ResU.Lower.functional j₁ k₁
  cases ResU.Lower.functional j₂ k₂
  cases MemUnion.functional ju ku
  exact hlow

end BoCa.Fig16

alias TR.lemma_6_7 := BoCa.Fig16.ResU.Lower.split

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.8 · `[TR]` p. 7 · `proved`

> If ⟦ρ₂⟧ = ⟦ρ₃⟧ and ρ₁ # ρ₂ and ρ₁ # ρ₃ then ⟦ρ₁ ● ρ₂⟧ = ⟦ρ₁ ● ρ₃⟧

**Printed proof, transcribed.** Immediate by Lemma 6.7, rewriting with `⟦ρ₂⟧ = ⟦ρ₃⟧`.

**Lean.** `BoCa.Fig16.ResU.Lower.congr`, alias `TR.lemma_6_8`, tag `[as printed]`.

**Note.** `Fig16.ResU.Lower.congr`, on the printed carrier, off 6.7 exactly as the print takes it — "immediate by lemma 6.7, and rewriting with `⟦ρ₂⟧ = ⟦ρ₃⟧`", the rewriting being `Fig16.ResU.Lower.functional`. The printed hypothesis `⟦ρ₂⟧ = ⟦ρ₃⟧` is an equation between partial terms and is carried as one: both lowerings are related to the same memory, which says they are defined and equal, and under the printed `#`s they are defined anyway (`Fig16.ResU.Valid.split`), so no case of it is lost. The conclusion is likewise the Kleene equality of its two sides. Nothing constrains `ρ₁`, `ρ₂`, `ρ₃` beyond the print.
-/
/-- **`[TR]` Lemma 6.8** (p. 7): if `⟦ρ₂⟧ = ⟦ρ₃⟧` and `ρ₁ # ρ₂` and `ρ₁ # ρ₃`
then `⟦ρ₁ ● ρ₂⟧ = ⟦ρ₁ ● ρ₃⟧`.  The printed hypothesis `⟦ρ₂⟧ = ⟦ρ₃⟧` is an
equation between two partial terms and is carried as one: both lowerings are
related to the **same** memory `m`, which says they are defined and equal, and
under the printed `#`s they are defined anyway (`ResU.Valid.split`), so no case
of the printed equation is lost.  The conclusion is likewise the Kleene equality
of its two sides.  The proof is the print's — "immediate by lemma 6.7, and
rewriting with `⟦ρ₂⟧ = ⟦ρ₃⟧`" — with `ResU.Lower.functional` as the
rewriting step.
`[as printed]` (as Kleene equalities between graphs — G4) -/
theorem ResU.Lower.congr {ρ₁ ρ₂ ρ₃ ρ₁₂ ρ₁₃ : ResU Loc Val} {m w : Loc → Option Val}
    (hm₂ : ResU.Lower ρ₂ m) (hm₃ : ResU.Lower ρ₃ m)
    (h₁₂ : ResU.CompS ρ₁ ρ₂ ρ₁₂) (hh₂ : ResU.Hash ρ₁ ρ₂)
    (h₁₃ : ResU.CompS ρ₁ ρ₃ ρ₁₃) (hh₃ : ResU.Hash ρ₁ ρ₃) :
    ResU.Lower ρ₁₂ w ↔ ResU.Lower ρ₁₃ w := by
  refine Iff.trans (ResU.Lower.split h₁₂ hh₂)
    (Iff.trans ?_ (ResU.Lower.split h₁₃ hh₃).symm)
  constructor
  · rintro ⟨n₁, n₂, k₁, k₂, ku⟩
    cases ResU.Lower.functional k₂ hm₂
    exact ⟨n₁, m, k₁, hm₃, ku⟩
  · rintro ⟨n₁, n₂, k₁, k₂, ku⟩
    cases ResU.Lower.functional k₂ hm₃
    exact ⟨n₁, m, k₁, hm₂, ku⟩

end BoCa.Fig16

alias TR.lemma_6_8 := BoCa.Fig16.ResU.Lower.congr

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.10 · `[TR]` p. 7 · `proved`

> If ✓(ρ₁ ● ρ₂) then ✓ρ₁ and ✓ρ₂

**Printed proof, transcribed.** By unfolding and applying Lemmas 6.18 and 6.20.

**Lean.** `BoCa.Fig16.ResU.Valid.split`, alias `TR.lemma_6_10`, tag `[as printed]`.

**Note.** `Fig16.ResU.Valid.split`, on the printed carrier, `[as printed]` — the **same declaration as 6.35**, because p. 5's own table has the row `✓ρ ≜ ⦇ρ⦈ defined` and `Fig16.ResU.Valid ρ` *is* `∃ σ, Fig16.ResU.Flat ρ σ`. Two hypotheses, both printed: `Fig16.ResU.CompS ρ₁ ρ₂ ρ` names `ρ₁ ● ρ₂` (G4) and its first conjunct is the print's `▸◂` presupposition; `ρ.Valid` is the printed `✓(ρ₁ ● ρ₂)`. The proof written is 6.35's, the longer of the two printed ones, through `Fig16.ResU.Flat.split_factors`.
-/
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

end BoCa.Fig16

alias TR.lemma_6_10 := BoCa.Fig16.ResU.Valid.split

namespace BoCa.Fig16
variable {Loc Val : Type}

/-! `[about ours]` — what the Lean of Lemma 6.11 needs; the paper prints nothing here. -/
/-- `[TR]` Lemma 6.3 at `●`.  `[as printed]` -/
theorem ResU.CompS.assoc (ρ₁ ρ₂ ρ₃ w : ResU Loc Val) :
    (∃ x, ResU.CompS ρ₂ ρ₃ x ∧ ResU.CompS ρ₁ x w) ↔
    (∃ y, ResU.CompS ρ₁ ρ₂ y ∧ ResU.CompS y ρ₃ w) :=
  ResU.Comp.assoc (fun _ _ _ h => CellU.CompS.compat h)
    (fun ψ₁ ψ₂ ψ₃ ω => CellU.compS_assoc ψ₁ ψ₂ ψ₃ ω) ρ₁ ρ₂ ρ₃ w

/-!
## Lemma 6.11 · `[TR]` p. 7 · `proved`

> If ρ₁ ● ρ₂ # ρ₃ then ρ₁ # ρ₃ and ρ₂ # ρ₃

**Printed proof, transcribed.** Definedness of `ρ₁ ● ρ₃` and `ρ₂ ● ρ₃` follows from unfolding definitions; `✓(ρ₁ ● ρ₃)` and `✓(ρ₂ ● ρ₃)` follow from Lemma 6.10 applied to `✓(ρ₁ ● ρ₂ ● ρ₃)`.

**Lean.** `BoCa.Fig16.ResU.Hash.split`, alias `TR.lemma_6_11`, tag `[as printed]`.

**Note.** `Fig16.ResU.Hash.split`, on the printed carrier, at the print's own operand order — `(ρ₁ ● ρ₂) # ρ₃` in the hypothesis, both conclusions in one statement, no mirroring. The printed proof is carried step for step: 6.3 (`Fig16.ResU.CompS.assoc`) and 6.2 regroup the one composite `(ρ₁ ● ρ₂) ● ρ₃` as `ρ₁ ● (ρ₂ ● ρ₃)` and as `ρ₂ ● (ρ₁ ● ρ₃)`, which is "definedness … from unfolding definitions", and 6.10 (`Fig16.ResU.Valid.split`) at each regrouping is "✓(ρ₁ ● ρ₃) and ✓(ρ₂ ● ρ₃) follow from theorem 6.10".
-/
/-- **`[TR]` Lemma 6.11** (p. 7): if `ρ₁ ● ρ₂ # ρ₃` then `ρ₁ # ρ₃` and
`ρ₂ # ρ₃`.  The print's two halves are the two conjuncts of `#`.  "Definedness
of `ρ₁ ● ρ₃` and `ρ₂ ● ρ₃` follow from unfolding definitions" is 6.3
(`ResU.CompS.assoc`) regrouping `(ρ₁ ● ρ₂) ● ρ₃` as `ρ₁ ● (ρ₂ ● ρ₃)` and —
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

alias TR.lemma_6_11 := BoCa.Fig16.ResU.Hash.split

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.12 · `[TR]` p. 7 · `proved`

> If ρ₁ ● ρ₂ and ρ₁ ● ρ₃ and ρ₂ ○ ρ₃ are all defined, then so is ρ₁ ● (ρ₂ ○ ρ₃).

**Printed proof, transcribed.** The own-or-mut cells of `ρ₁` are disjoint from those of `ρ₂` and `ρ₃`, hence from those of `ρ₂ ○ ρ₃`, because `○` introduces no new own-or-mut cells.  At a location where `(ρ₂ ○ ρ₃)(ℓ)` is an `imm` cell, either (1) both operands are `imm` cells over one value and one witness, `imm(α₁, v, ρ)` and `imm(α₂, v, ρ)`, so the composite is `imm(α₁ ∪ α₂, v, ρ)` and is composable with `ρ₁(ℓ)` by `ρ₁ ▸◂ ρ₂`; or (2) one operand is `imm` and the other own-or-mut (without loss of generality `ρ₂`'s), so `ℓ ∉ dom(ρ₁)` and `ℓ` is not in the overlap.  So the `imm` cells of `ρ₁` agree on overlap with those of `ρ₂ ○ ρ₃` up to lifetimes.

**Lean.** `BoCa.Fig16.ResU.compatS_of_compR`, alias `TR.lemma_6_12`, tag `[as printed]`.

**Note.** `Fig16.ResU.compatS_of_compR`, on the printed carrier.  "`ρ₁ ● ρ₂` is defined" is `▶◀` by Lemma 6.9 and "`ρ₂ ○ ρ₃` is defined" is `⋈` by its `○` twin, so the hypotheses are the print's. The imm case turns on `Fig16.CellU.compatS_iff`, which reads `▶◀` off a cell's tag, value and witness
-/
/-- **`[TR]` Lemma 6.12** (p. 7): if `ρ₁ ● ρ₂` and `ρ₁ ● ρ₃` and `ρ₂ ○ ρ₃` are
all defined then so is `ρ₁ ● (ρ₂ ○ ρ₃)`.  Stated, as 6.13 is, as "`ρ₁` is
compatible with the composite", which by Lemma 6.9 (`ResU.compS_defined_iff`) is definedness of `ρ₁ ● (ρ₂ ○ ρ₃)`.

The proof is the print's, at one location of the overlap.  Where only one of
`ρ₂`, `ρ₃` is defined, `◐`'s outer pieces make the composite that operand and
the corresponding hypothesis is the whole of it — that is the print's "`○` does
not introduce new own-or-mut cells".  Where both are defined, `ρ₁ ▸◂ ρ₂` already
says `ρ₂(ℓ)` is an `imm` cell over `ρ₁(ℓ)`'s value and witness, which is the
print's case (1); its case (2) is the same fact contrapositively — an
own-or-mut `ρ₂(ℓ)` puts `ℓ` outside `dom(ρ₁)`, so no obligation arises there.
`CellU.CompatS.of_compR_left` is what closes case (1).
`[as printed]` (the printed `ρ₂ ○ ρ₃` appears as its graph — G4) -/
theorem ResU.compatS_of_compR {ρ₁ ρ₂ ρ₃ r : ResU Loc Val}
    (h₁₂ : ResU.CompatS ρ₁ ρ₂) (h₁₃ : ResU.CompatS ρ₁ ρ₃)
    (h₂₃ : ResU.CompR ρ₂ ρ₃ r) : ResU.CompatS ρ₁ r := by
  intro l ψ₁ χ e₁ e
  rcases h₂₃.get l with ⟨-, -, e₀⟩ | ⟨ψ, f₁, -, e₀⟩ | ⟨ψ, -, f₂, e₀⟩ |
      ⟨ψ₂, ψ₃, ψ, f₁, f₂, e₀, hC⟩
  · rw [e₀] at e; exact absurd e (by simp)
  · rw [e₀] at e; cases Option.some.inj e; exact h₁₂ l _ _ e₁ f₁
  · rw [e₀] at e; cases Option.some.inj e; exact h₁₃ l _ _ e₁ f₂
  · rw [e₀] at e
    cases Option.some.inj e
    exact CellU.CompatS.of_compR_left (h₁₂ l _ _ e₁ f₁) hC

end BoCa.Fig16

alias TR.lemma_6_12 := BoCa.Fig16.ResU.compatS_of_compR

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
## Lemma 6.13 · `[TR]` p. 7 · `proved`

> If ρ₁ ● ρ₂ and ρ₁ ● ρ₃ and ρ₂ ● ρ₃ are all defined, then so is ρ₁ ● ρ₂ ● ρ₃.

**Printed proof, transcribed.** The own-or-mut cells of `ρ₁, ρ₂, ρ₃` are pairwise disjoint, hence mutually disjoint, and the `imm` cells pairwise agree up to lifetimes, hence mutually agree up to lifetimes.

**Lean.** `BoCa.Fig16.ResU.compatS_of_pairwise`, alias `TR.lemma_6_13`, tag `[as printed]`.

**Note.** `Fig16.ResU.compatS_of_pairwise`, on the printed carrier: from `ρ₁ ● ρ₂` and pairwise `▶◀` it produces `(ρ₁ ● ρ₂) ▶◀ ρ₃`, which by 6.9 is definedness of the triple composite.
-/
/-- **`[TR]` Lemma 6.13** (p. 7): if `ρ₁ ● ρ₂`, `ρ₁ ● ρ₃` and `ρ₂ ● ρ₃` are all
defined then so is `ρ₁ ● ρ₂ ● ρ₃`.  Stated as "the composite is compatible with
the third", which by Lemma 6.9 (`ResU.compS_defined_iff`) is definedness of
the triple composite.  `[as printed]` -/
theorem ResU.compatS_of_pairwise {ρ₁ ρ₂ ρ₃ σ : ResU Loc Val}
    (h₁₂ : ResU.CompS ρ₁ ρ₂ σ) (h₁₃ : ResU.CompatS ρ₁ ρ₃)
    (h₂₃ : ResU.CompatS ρ₂ ρ₃) : ResU.CompatS σ ρ₃ := by
  intro l χ ψ₃ hχ h₃
  rcases h₁₂.get l with ⟨-, -, e⟩ | ⟨ψ, e₁, -, e⟩ | ⟨ψ, -, e₂, e⟩ |
      ⟨ψ₁, ψ₂, ψ, e₁, e₂, e, hC⟩
  · rw [e] at hχ; exact absurd hχ (by simp)
  · rw [e] at hχ; cases Option.some.inj hχ; exact h₁₃ l _ _ e₁ h₃
  · rw [e] at hχ; cases Option.some.inj hχ; exact h₂₃ l _ _ e₂ h₃
  · rw [e] at hχ
    cases Option.some.inj hχ
    obtain ⟨s₁, s₂, v, τ, k₁, k₂, k₃, f₁, f₂, f₃⟩ := hC
    obtain ⟨t₁, t₃, w, τ', m₁, m₃, g₁, g₃⟩ := h₁₃ l _ _ e₁ h₃
    obtain ⟨-, hv, hρ⟩ := CellU.immOf_inj (f₁.symm.trans g₁)
    subst hv; subst hρ
    exact ⟨s₁ ∪ s₂, t₃, _, _, k₃, m₃, f₃, g₃⟩

end BoCa.Fig16

alias TR.lemma_6_13 := BoCa.Fig16.ResU.compatS_of_pairwise

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### Row 5.67's theorem `BoCa.Fig16.CellU.compatR_iff`, ahead of its file

A remark on a printed definition of `[TR]` §5; its proof uses results of §6, and the Lean of Lemmas 6.14 and 6.15 in this file needs it, so it is declared here.  The row is recorded in `Paper/S5_Model/Remarks.lean`.
-/
/-- **`⋈` is exactly "a common value, and a common witness wherever there is one
to share".**  Left to right is `CellU.CompR.erase` and `CellU.CompR.wit`;
right to left is the case analysis over the two tags that p. 5's five clauses
decide, one clause per pair of tags — `own` against anything is (1), (4) or (5),
two `imm` cells over one witness are (2), two `mut` cells over one witness are
(3), and an `imm` against a `mut` over one witness is (5).

The second conjunct is the wrinkle `[TR]` Lemma 6.14's proof names, and the
right-to-left direction is what that proof spends: `○` merges an `imm` cell with
an own-or-mut cell "only when the given own-or-mut cell has the same value and
subresource inside of it", and here that condition is not merely necessary but
sufficient, so a composite that inherits it is `⋈` whatever the operand was.
`[about ours: the `⋈`, which is `[TR]` p. 5's printed second disjunct on the
reading argued there, in the projections `CellU.rep` and `CellU.erase`]` -/
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

/-! `[about ours]` — what the Lean of Lemma 6.14 needs; the paper prints nothing here. -/
/-- **The cell level of `[TR]` Lemma 6.14.**  The value of a `○` is `⋈` a third
cell whenever both operands are.  The value passes through by
`CellU.CompR.erase`; for the witness, `CellU.CompR.wit_of_ne_own` names the
operand the composite took its witness from, and that operand's `⋈` with the
third cell is the one to use.  Both steps read `⋈` through
`CellU.compatR_iff` — including its right-to-left half, which is the printed
"it only does so when the given own-or-mut cell has the same value and
subresource inside of it".
`[about ours: the cell-level step `[TR]` Lemma 6.14's proof takes at a location
where both `ρ₁` and `ρ₂` are defined]` -/
theorem CellU.CompatR.of_compR {ψ₁ ψ₂ ψ ψ₃ : CellU Loc Val}
    (h : CellU.CompR ψ₁ ψ₂ ψ) (k₁ : ψ₁.CompatR ψ₃) (k₂ : ψ₂.CompatR ψ₃) :
    ψ.CompatR ψ₃ := by
  rw [CellU.compatR_iff] at k₁ k₂ ⊢
  refine ⟨(CellU.CompR.erase h).2.trans k₁.1, fun hψ h₃ => ?_⟩
  rcases h.wit_of_ne_own hψ with ⟨hn, he⟩ | ⟨hn, he⟩
  · exact he.trans (k₁.2 hn h₃)
  · exact he.trans (k₂.2 hn h₃)

/-!
## Lemma 6.14 · `[TR]` p. 8 · `proved`

> If ρ₁ ○ ρ₂ and ρ₁ ○ ρ₃ and ρ₂ ○ ρ₃ are all defined, then so is ρ₁ ○ ρ₂ ○ ρ₃.

**Printed proof, transcribed.** Analogous to Lemma 6.13.  The only wrinkle is that `○`, unlike `●`, merges `imm` cells with `own` and `mut` cells; but it does so only when the own-or-mut cell has the same value and subresource inside it, so the composites still agree on overlapping `imm` cells up to lifetimes.

**Lean.** `BoCa.Fig16.ResU.compatR_of_pairwise`, alias `TR.lemma_6_14`, tag `[as printed]`.

**Note.** `Fig16.ResU.compatR_of_pairwise`, on the printed carrier — 6.13's `○` analogue, which needs its own proof since 6.13 is stated at `●`. The print's wrinkle (`○` merges an `imm` cell with an own-or-mut one *only when the value and subresource agree*, the subresource conjunct having its referent at the `mut` member of p. 5's clause (5) — the member that has one, `[CONF]` p. 415:24's "already has a witness resource" — since `own(Val)` carries no `ρ` field and clause (5) shares `ρ` between the `imm` and `mut` members only) is `Fig16.CellU.compatR_iff`, proved in **both** directions; the right-to-left half is what produces the conclusion, so the wrinkle is spent, not assumed
-/
/-- **`[TR]` Lemma 6.14** (p. 8): if `ρ₁ ○ ρ₂` and `ρ₁ ○ ρ₃` and `ρ₂ ○ ρ₃` are
all defined then so is `ρ₁ ○ ρ₂ ○ ρ₃`.  As with 6.13, "so is the triple
composite" is stated as `⋈` between the first composite and the third operand,
which by `ResU.compR_defined_iff` (the `○` twin of Lemma 6.9) is that
definedness.

The proof is the print's "analogous to theorem 6.13", run at one location: the
two cases where only one operand is defined are the corresponding hypotheses,
and the case where both are is `CellU.CompatR.of_compR` — which is the printed
wrinkle, `○` merging an `imm` cell with an own-or-mut one only when the value
and the witness inside it already agree.
`[as printed]` (the printed `ρ₁ ○ ρ₂` appears as its graph — G4) -/
theorem ResU.compatR_of_pairwise {ρ₁ ρ₂ ρ₃ σ : ResU Loc Val}
    (h₁₂ : ResU.CompR ρ₁ ρ₂ σ) (h₁₃ : ResU.CompatR ρ₁ ρ₃)
    (h₂₃ : ResU.CompatR ρ₂ ρ₃) : ResU.CompatR σ ρ₃ := by
  intro l χ ψ₃ hχ h₃
  rcases h₁₂.get l with ⟨-, -, e⟩ | ⟨ψ, e₁, -, e⟩ | ⟨ψ, -, e₂, e⟩ |
      ⟨ψ₁, ψ₂, ψ, e₁, e₂, e, hC⟩
  · rw [e] at hχ; exact absurd hχ (by simp)
  · rw [e] at hχ; cases Option.some.inj hχ; exact h₁₃ l _ _ e₁ h₃
  · rw [e] at hχ; cases Option.some.inj hχ; exact h₂₃ l _ _ e₂ h₃
  · rw [e] at hχ
    cases Option.some.inj hχ
    exact CellU.CompatR.of_compR hC (h₁₃ l _ _ e₁ h₃) (h₂₃ l _ _ e₂ h₃)

end BoCa.Fig16

alias TR.lemma_6_14 := BoCa.Fig16.ResU.compatR_of_pairwise

namespace BoCa.Fig16
variable {Loc Val : Type}

/-! `[about ours]` — what the Lean of Lemma 6.15 needs; the paper prints nothing here. -/
/-- **The composability constraints one `#` puts on its operands' walks.**
`[TR]` Lemma 6.15's proof reads them off the display
`⦇ρ₁ ● ρ₂⦈ = ex(ρ₁)_● ● ex(ρ₂)_● ● (ag(ρ₁) ○ ag(ρ₂))` — `ResU.Flat.split`,
which is Lemmas 6.18 and 6.20 — as "`ex(ρ₁)_●`, `ex(ρ₂)_●` are
pairwise-composable with respect to `●`" and "`ag(ρ₁)`, `ag(ρ₂)` are
pairwise-composable with respect to `○`".  The four mixed constraints are
Lemma 6.30 (`ResU.CompatS.of_compR_left`) applied to `ag(ρ₁) ○ ag(ρ₂)` and
then `ResU.CompatS.of_compS_left_immFree` down each exclusive factor — the same
two steps `ResU.Flat.split_factors` takes, kept at all four pairs rather than at
the diagonal.
`[about ours: the constraints `[TR]` Lemmas 6.15 and 6.35 read off the display,
collected at named walks]` -/
theorem ResU.Hash.walks {ρ₁ ρ₂ : ResU Loc Val} (h : ResU.Hash ρ₁ ρ₂)
    {e₁ e₂ a₁ a₂ : ResU Loc Val}
    (he₁ : ExS ρ₁ e₁) (he₂ : ExS ρ₂ e₂) (ha₁ : AgW ρ₁ a₁) (ha₂ : AgW ρ₂ a₂) :
    ResU.CompatS e₁ e₂ ∧ ResU.CompatR a₁ a₂ ∧
      ResU.CompatS e₁ a₁ ∧ ResU.CompatS e₁ a₂ ∧
      ResU.CompatS e₂ a₁ ∧ ResU.CompatS e₂ a₂ := by
  obtain ⟨-, ρ, hρ, σ, hσ⟩ := h
  obtain ⟨f₁, f₂, e, b₁, b₂, a, hf₁, hf₂, hec, hb₁, hb₂, hac, hc⟩ :=
    (ResU.Flat.split hρ).mp hσ
  cases ExS.functional hf₁ he₁
  cases ExS.functional hf₂ he₂
  cases AgW.functional hb₁ ha₁
  cases AgW.functional hb₂ ha₂
  have himm : e.ImmFree := ResU.ImmFree.compS hec (ExS.immFree he₁) (ExS.immFree he₂)
  obtain ⟨hca₁, hca₂⟩ :=
    ResU.CompatS.of_compR_left ((ResU.restrict_imm_empty_iff e).mpr himm) hac hc.1
  obtain ⟨d₁₁, d₂₁⟩ := ResU.CompatS.of_compS_left_immFree himm hec hca₁
  obtain ⟨d₁₂, d₂₂⟩ := ResU.CompatS.of_compS_left_immFree himm hec hca₂
  exact ⟨hec.1, hac.1, d₁₁, d₁₂, d₂₁, d₂₂⟩

/-!
## Lemma 6.15 · `[TR]` p. 8 · `proved`

> If ρ₁ # ρ₂ and ρ₂ # ρ₃ and ρ₁ # ρ₃ then ρ₁ # ρ₂ ● ρ₃.

**Printed proof, transcribed.** The composite `ρ₁ ● ρ₂ ● ρ₃` is defined by Lemma 6.13, so it remains to show `✓(ρ₁ ● ρ₂ ● ρ₃)`, which by Lemmas 6.18 and 6.20 is definedness of `ex(ρ₁)_● ● ex(ρ₂)_● ● ex(ρ₃)_● ● (ag(ρ₁) ○ ag(ρ₂) ○ ag(ρ₃))`.  By assumption the three flattenings `⦇ρᵢ ● ρⱼ⦈ = ex(ρᵢ)_● ● ex(ρⱼ)_● ● (ag(ρᵢ) ○ ag(ρⱼ))` are defined, so the `ex(ρᵢ)_●` are pairwise `●`-composable and the `ag(ρᵢ)` pairwise `○`-composable, and Lemmas 6.13 and 6.14 give the two triple composites.  By two applications of Lemma 6.12 it remains that `ex(ρ₁)_● ● ex(ρ₂)_● ● ex(ρ₃)_● ● ag(ρᵢ)` is defined for each `i`; for `i = 1`, `ex(ρ₁)_●`, `ex(ρ₂)_● ● ex(ρ₃)_●` and `ag(ρ₁)` are pairwise composable by assumption, so Lemma 6.13 applies, and the other two are analogous.

**Lean.** `BoCa.Fig16.ResU.hash_of_pairwise`, alias `TR.lemma_6_15`, tag `[as printed]`.

**Note.** `Fig16.ResU.hash_of_pairwise`, on the printed carrier. The print's proof opens by unfolding `✓(ρ₁ ● ρ₂ ● ρ₃)` through 6.18 and 6.20; `Fig16.ResU.Flat.split` is that equation.
-/
/-- **`[TR]` Lemma 6.15** (p. 8): if `ρ₁ # ρ₂` and `ρ₂ # ρ₃` and `ρ₁ # ρ₃` then
`ρ₁ # ρ₂ ● ρ₃`.  Both conjuncts of `#` are produced, in the print's order:
`ρ₁ ▸◂ ρ₂ ● ρ₃` by 6.13, and `✓(ρ₁ ● (ρ₂ ● ρ₃))` by the walk bookkeeping the
print sets out, with the walks grouped as `ex(ρ₁)_● ● (ex(ρ₂)_● ● ex(ρ₃)_●)` so
that `ResU.Flat.split` applies at `ρ₁` against `ρ₂ ● ρ₃`.

The composite `ρ₂ ● ρ₃` is named by its graph, which carries the `▸◂` the
printed expression presupposes; naming it adds nothing, `●` being single-valued.
The six walks exist because each operand is valid — `[TR]` Lemma 6.10
(`ResU.Valid.split`) applied to the hypotheses — and they are the same six
in all three displays because `ex` and `ag` are functions.
`[as printed]` (the printed `ρ₂ ● ρ₃` appears as its graph — G4) -/
theorem ResU.hash_of_pairwise {ρ₁ ρ₂ ρ₃ ρ₂₃ : ResU Loc Val}
    (h₁₂ : ResU.Hash ρ₁ ρ₂) (h₂₃ : ResU.Hash ρ₂ ρ₃) (h₁₃ : ResU.Hash ρ₁ ρ₃)
    (h : ResU.CompS ρ₂ ρ₃ ρ₂₃) : ResU.Hash ρ₁ ρ₂₃ := by
  -- `ρ₁ ▸◂ ρ₂ ● ρ₃`, by 6.13, and the composite 6.9 then names.
  have hcompat : ResU.CompatS ρ₁ ρ₂₃ :=
    (ResU.compatS_of_pairwise h h₁₂.1.symm h₁₃.1.symm).symm
  obtain ⟨ρ, hρ⟩ := (ResU.compS_defined_iff ρ₁ ρ₂₃).mpr hcompat
  refine ⟨hcompat, ρ, hρ, ?_⟩
  -- One pair of walks per operand: `✓ρᵢ` is 6.10, and the walks are functions.
  obtain ⟨x₁₂, hx₁₂, hv₁₂⟩ := h₁₂.2
  obtain ⟨x₂₃, hx₂₃, hv₂₃⟩ := h₂₃.2
  obtain ⟨hV₁, hV₂⟩ := ResU.Valid.split hx₁₂ hv₁₂
  obtain ⟨-, hV₃⟩ := ResU.Valid.split hx₂₃ hv₂₃
  obtain ⟨-, e₁, a₁, he₁, ha₁, -⟩ := hV₁
  obtain ⟨-, e₂, a₂, he₂, ha₂, -⟩ := hV₂
  obtain ⟨-, e₃, a₃, he₃, ha₃, -⟩ := hV₃
  -- The constraints the print takes "by assumption", at the three printed pairs.
  obtain ⟨g₁₂, r₁₂, c₁₁, c₁₂, c₂₁, c₂₂⟩ := h₁₂.walks he₁ he₂ ha₁ ha₂
  obtain ⟨g₂₃, r₂₃, -, c₂₃, c₃₂, c₃₃⟩ := h₂₃.walks he₂ he₃ ha₂ ha₃
  obtain ⟨g₁₃, r₁₃, -, c₁₃, c₃₁, -⟩ := h₁₃.walks he₁ he₃ ha₁ ha₃
  -- The walks of `ρ₂ ● ρ₃`, by 6.18 and 6.20.
  obtain ⟨e₂₃, hE₂₃⟩ := (ResU.compS_defined_iff e₂ e₃).mpr g₂₃
  obtain ⟨a₂₃, hA₂₃⟩ := (ResU.compR_defined_iff a₂ a₃).mpr r₂₃
  have hex : ExS ρ₂₃ e₂₃ := (ExS.split h).mpr ⟨e₂, e₃, he₂, he₃, hE₂₃⟩
  have hag : AgW ρ₂₃ a₂₃ := (AgW.split h).mpr ⟨a₂, a₃, ha₂, ha₃, hA₂₃⟩
  -- The triple exclusive composite, by 6.13; the triple aliasable one, by 6.14.
  obtain ⟨E, hE⟩ := (ResU.compS_defined_iff e₁ e₂₃).mpr
    (ResU.compatS_of_pairwise hE₂₃ g₁₂.symm g₁₃.symm).symm
  obtain ⟨A, hA⟩ := (ResU.compR_defined_iff a₁ a₂₃).mpr
    (ResU.compatR_of_pairwise hA₂₃ r₁₂.symm r₁₃.symm).symm
  -- The print's three displayed composites `E ▸◂ ag(ρⱼ)`, each 6.13 twice.
  have hEa₁ : ResU.CompatS E a₁ :=
    ResU.compatS_of_pairwise hE c₁₁ (ResU.compatS_of_pairwise hE₂₃ c₂₁ c₃₁)
  have hEa₂ : ResU.CompatS E a₂ :=
    ResU.compatS_of_pairwise hE c₁₂ (ResU.compatS_of_pairwise hE₂₃ c₂₂ c₃₂)
  have hEa₃ : ResU.CompatS E a₃ :=
    ResU.compatS_of_pairwise hE c₁₃ (ResU.compatS_of_pairwise hE₂₃ c₂₃ c₃₃)
  -- "By two applications of theorem 6.12", `E ▸◂ ag(ρ₁) ○ ag(ρ₂) ○ ag(ρ₃)`.
  obtain ⟨σ, hσ⟩ := (ResU.compS_defined_iff E A).mpr
    (ResU.compatS_of_compR hEa₁ (ResU.compatS_of_compR hEa₂ hEa₃ hA₂₃) hA)
  exact ⟨σ, (ResU.Flat.split hρ).mpr
    ⟨e₁, e₂₃, E, a₁, a₂₃, A, he₁, hex, hE, ha₁, hag, hA, hσ⟩⟩

end BoCa.Fig16

alias TR.lemma_6_15 := BoCa.Fig16.ResU.hash_of_pairwise

end
