import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S4_LogicalRelation.Definitions
import Paper.S5_Model.Definitions
import Support.LogicalRelation.ClosingSubstitutions
import Support.LogicalRelation.Facts

/-!
# Literal readings — [TR] §4

Declarations that measure a printed definition read literally, where the
library uses a repaired one.  They are kept so the adjudication can be checked,
and nothing in the paper tree depends on them.

* `MutImmGap` (row 4.17): the cell and lifetime set at which, under the literal
  `α ⊑ ⊔β̄` of `ℓ ↦ Imm α P̂`, `𝒱⟦Mut @a (Imm @b 1)⟧` is empty.

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

namespace BoCa.Fig16.LogRel.MutImmGap
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
### 4.17 · — no printed counterpart — · [TR] p. 4 · `[repair]`

An `imm` cell recording `{α₀, β}`, outside `Res_β`; with the connective at `⊓β̄` (row 5.30) it is in `𝒱⟦Imm @b 1⟧δ` only where `@bδ ⊑ α₀ ⊓ β`, and `BoCa.Fig16.LogRel.MutImmGap.inRel_same` is the case `β = α₀`. Adjudicated at `BoCa/Fig16LogRel.lean` §3b and `docs/boca-rules.md` §12.67(a): at the literal `⊔β̄` this cell emptied `𝒱⟦Mut @a (Imm @b 1)⟧δ`, and the declarations that measured that reading are removed
-/
/-- `β̄ = {α₀, β}`. -/
def lset (α₀ β : Life) : LSet := (LSet.singleton α₀).union (LSet.singleton β)

/-!
Row 4.17, continued.
-/
/-- The cell: an immutable borrow whose recorded set is `{α₀, β}`. -/
noncomputable def cell (α₀ β : Life) : WRes :=
  ResU.single 0 (CellU.immOf (lset α₀ β) .unit PMap.empty
    (empty_inStratum (lset α₀ β).join))

/-! `[about ours]` — what the Lean of row 4.17's theorem needs; the paper prints nothing here. -/
theorem lset_meet (α₀ β : Life) : (lset α₀ β).meet = α₀ ⊓ β := rfl

/-!
Row 4.17, continued.
-/
/-- At `β = α₀` the cell is in `𝒱⟦Imm @b 1⟧δ`, `@bδ = α₀`. -/
theorem inRel_same {δ : LSub} {b : Lifetime.Life} {α₀ : Life} (hb : b.interp δ = some α₀) :
    vDen (.imm b .unit) δ (.loc 0) (cell α₀ α₀) := by
  refine ⟨α₀, hb, 0, pure_sep_mk rfl ?_⟩
  exact ⟨lset α₀ α₀, .unit, PMap.empty, empty_inStratum _, rfl, ⟨rfl, rfl⟩,
    by rw [lset_meet, inf_idem]⟩

end BoCa.Fig16.LogRel.MutImmGap

namespace BoCa.Fig16.LogRel.MutGapClosed
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
Row 4.17, continued.
-/
/-- `LogRel.MutGap.Tgap`: `Mut ⊤ (Imm 'x 1)`, whose PAYLOAD mentions the
substituted variable.  `LogRel.MutGap` is the machine-checked refutation of
`𝒱⟦T[⊤/'x]⟧δ = 𝒱⟦T⟧_{δ['x↦⊤]}` at this type over `ResI`. -/
def Tgap : Ty := .mut .top (.imm (.var 0) .unit)

end BoCa.Fig16.LogRel.MutGapClosed

end
