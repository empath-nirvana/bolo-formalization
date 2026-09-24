import Challenge.Paper.S1_Syntax.Definitions
import Challenge.Support.Syntax.Terms
import Challenge.Support.Lifetimes.Terms
import Challenge.Support.Lifetimes.Substitution
import Challenge.Support.Statics.Contexts
import Challenge.Paper.S3_Dynamics.Definitions
import Challenge.Paper.S2_Statics.Definitions
import Challenge.Support.Statics.Presupposed
import Challenge.Support.Dynamics.Machine
import Challenge.Support.LogicalRelation.Adequacy

/-!
# The comparator challenge

The statement of the end-to-end adequacy theorem,
`BoCa.Fig16.LogRel.Typed.adequacy` (`Paper/CONF/Results.lean`), with a `sorry`
body.  A solution passes iff it provides a theorem of this name whose statement
is identical to this one, every declaration the statement reaches is identical
to the one here (type and, for a definition or theorem, value), and its proof
uses no axiom outside `propext`, `Classical.choice`, `Quot.sound`.

This module imports neither `Paper` nor `Support`.  The modules under
`Challenge/` replicate, verbatim, the declarations the statement reaches:
the syntax ([TR] §1), the typing judgment `DerivesWf` and what it uses ([TR] §2
as the library reads it), and the machine `BoLo.Steps` with the empty memory
([TR] §3).  Each is copied from the file its path names, under the same
namespaces, `open`s and names; `Challenge/X/Y.lean` holds the declarations of
`X/Y.lean`.  Nothing of the model ([TR] §§4–6: the logical relation,
resources, `wp`, the typed world) is here, so a pass trusts none of its repairs.

The copies keep the library's module boundaries because Lean reuses
pattern-matching auxiliaries (`f.match_1`) across definitions of the same shape
within a module; with the same boundaries the values agree constant for
constant.  For the same reason `Lifetime.Life.depth` and `Ty.wfB`, which the
statement does not reach, are copied: `Life.mentions` and `Ty.scopedB` reuse
their auxiliaries.

The `sorry` below is comparator's convention for a challenge statement.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Typed
open BoCa
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- A closed program that `DerivesWf` types at `1` runs from the empty memory to `()`
and the empty memory. -/
theorem adequacy (e : Expr) (hD : DerivesWf LifeCtx.empty ([] : Ctx Ty) e Ty.unit) :
    BoCa.BoLo.Steps Adequacy.emptyMem e Adequacy.emptyMem (.val .unit) := by
  sorry

end BoCa.Fig16.LogRel.Typed

end
