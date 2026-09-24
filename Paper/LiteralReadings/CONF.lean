import Paper.LiteralReadings.S6_7_WeakestPreconditionRules
import Paper.S1_Syntax.Definitions
import Paper.S3_Dynamics.Definitions
import Support.Dynamics.Machine

/-!
# Literal readings — [CONF] §3

* Corollary 3.3: `TR3.corThree_unreachable` — the closed term `free (alloc ()); ()`,
  typed at `1` by `[TR]` p. 2, has no run to `()` on `[TR]` §3's printed machine.
  Over that machine `TR3.wp_seq_false` refuses the corollary's semantic hypothesis at
  the same term, so what this measures is the composite with Lemma 3.1.

**How this file reads.**  Each run opens with the result it measures and says where
that result's record is.  Each declaration carries its tag; an
`[about ours: …]` tag names what is measured.  Nothing in the paper tree depends on
this file.
-/

noncomputable section

namespace BoCa.TR3
open BoCa.Fig16
open BoCa.BoLo (Heap)
open BoCa.Fig16.BoLo (Entails sep wand all box top ptoOwn ptoMut ptoImm outlives_comp NoOwn noOwn_empty noOwn_compS hash_lower hash_valid hash_valid_comp hash_shift updV_compS_own hash_compS_own lower_compS_own_inv lower_get_own lower_eq_none_iff get_eq_none_of_flat get_eq_none_of_compatS_own compatS_single_of_get_none loc_infinite compS_reassoc compS_reassoc' compS_exch compS_lcomm updV_frame updV_outlives)
open BoCa.Lifetime

/-!
### Corollary 3.3 (Adequacy at 1) — literal reading

The printed statement, the printed proof and the adjudication are in `Paper/CONF/Results.lean`, under the record of Corollary 3.3 (Adequacy at 1).
-/
/-- **Corollary 3.3's conclusion is unreachable here**, at a closed term `[TR]`
p. 2 types at `1`: no run of the printed machine from `wSeq` ends at `()`, from
any heap to any heap.  `derives_wSeq` types it and `stuck_wSeq` stops it.
`[about ours: `[CONF]` Corollary 3.3's conclusion at `[TR]` §3's machine]` -/
theorem corThree_unreachable {μ μ' : Heap} (h : Steps μ wSeq μ' (.val .unit)) :
    False :=
  (stuck_wSeq μ).2 μ' Val.unit h

end BoCa.TR3

end
