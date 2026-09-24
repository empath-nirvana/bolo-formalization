import Paper.S5_Model.Definitions
import Paper.S6_2_NonStandardLemmas.Lemmas
import Support.Model.Notation

/-!
# Support — Model — Strata

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
every resource lies in some stratum: `Res = ⋃_α Res_α`.
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- **Every resource lies in some stratum** — the second thing finiteness buys.
`Res_α` for `α = ↓@ρ` contains `ρ`; a resource whose cells had unboundedly
short lifetimes would lie in no `Res_α` at all, and Fig. 16's rows 2 and 7
would then not be related by inclusion.
`[about ours: `Res_α ⊆ Res` is the printed shape; that the inclusions exhaust
`Res` is the statement here]` -/
theorem ResU.exists_stratum (ρ : ResU Loc Val) : ∃ α, ρ.InStratum α := by
  obtain ⟨a, ha⟩ := ρ.exists_atLife
  refine ⟨↓a, fun l ψ e => ?_⟩
  have hle : a ⊑ ψ.at := ha.1 l ψ e
  cases ψ with
  | own v => exact trivial
  | imm i => exact lt_of_lt_of_le (Life.down_sqsubset a) hle
  | «mut» m => exact lt_of_lt_of_le (Life.down_sqsubset a) hle

end BoCa.Fig16

end
