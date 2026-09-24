import Paper
/-!
The axiom audit CI diffs against `scripts/axioms.expected`:

    lake env lean scripts/AxiomCheck.lean > axioms.out
    diff axioms.out scripts/axioms.expected

`#print axioms` of the headline results and of `[CONF]`'s numbered results, of
adequacy at the closed programs of `Paper/Examples/Programs.lean`, then of every
`TR.lemma_*` alias, enumerated from the environment so that the list
follows the library.  `scripts/CheckAxioms.lean` checks every declaration
against the three standard axioms; this file records, per headline result, what
it depends on.
-/
open Lean Elab Command

#print axioms BoCa.Fig16.LogRel.Typed.fundamentalProperty
#print axioms BoCa.Fig16.LogRel.Typed.adequacy
#print axioms BoCa.Fig16.LogRel.Typed.theorem32
#print axioms BoCa.Fig16.LogRel.Typed.corollary33
#print axioms CONF.lemma_3_1
#print axioms CONF.theorem_3_2
#print axioms CONF.corollary_3_3
#print axioms BoCa.Programs.allocFree_runs
#print axioms BoCa.Programs.fig2c_runs
#print axioms BoCa.Programs.immBorrow_runs
#print axioms BoCa.Programs.mutBorrow_runs
#print axioms BoCa.Programs.loadClosure_runs
#print axioms BoCa.Programs.aliasLoad_runs
#print axioms BoCa.Programs.swapTwo_runs
#print axioms BoCa.Programs.greetProg_runs
#print axioms BoCa.Programs.allocFree_steps

run_cmd do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc n _ =>
    match n with
    | .str (.str .anonymous "TR") s => if s.startsWith "lemma_" then acc.push n else acc
    | _ => acc
  for n in names.qsort (·.toString < ·.toString) do
    elabCommand (← `(#print axioms $(mkIdent n)))
