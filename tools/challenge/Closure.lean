import Lean
/-!
The constants the statement of `BoCa.Fig16.LogRel.Typed.adequacy` reaches, as
comparator's crawl reaches them (`Comparator.runForUsedConsts`): the type, the
value of a definition or theorem, the constructors and mutual block of an
inductive, the inductive of a constructor, the rules of a recursor.  One
`<module> <name>` line per constant, sorted.

    lake env lean --run tools/challenge/Closure.lean
-/
open Lean

def used (ci : ConstantInfo) : Array Name := Id.run do
  let mut cs := ci.type.getUsedConstants
  if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants
  match ci with
  | .inductInfo i => cs := cs ++ i.ctors.toArray ++ i.all.toArray
  | .ctorInfo c => cs := cs.push c.induct
  | .recInfo r => for rl in r.rules do cs := (cs.push rl.ctor) ++ rl.rhs.getUsedConstants
  | _ => pure ()
  return cs

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `Paper }] {} 0 (loadExts := true)
  let some ci := env.find? `BoCa.Fig16.LogRel.Typed.adequacy
    | throw (IO.userError "BoCa.Fig16.LogRel.Typed.adequacy not found")
  let mut work := ci.type.getUsedConstants
  let mut seen : NameSet := {}
  while !work.isEmpty do
    let n := work.back!
    work := work.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some c := env.find? n | continue
    for m in used c do
      unless seen.contains m do work := work.push m
  let lines := seen.toList.map fun n =>
    let mod := (env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!)
    s!"{mod.getD `none} {n}"
  for l in lines.toArray.qsort (· < ·) do IO.println l
