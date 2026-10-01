import Lean
/-!
`#print axioms` for every declaration of `Views.*` (`Extensions/Views/`) at
once, as `scripts/CheckAxioms.lean` does for `Paper.*` and `Support.*`.  Fails
unless every one is among `propext`, `Classical.choice` and `Quot.sound`.

    lake build Views
    lake env lean --run scripts/CheckAxiomsViews.lean
-/
open Lean

partial def reach (env : Environment) (n : Name) (seen : IO.Ref NameSet) (axs : IO.Ref NameSet) : IO Unit := do
  if (← seen.get).contains n then return
  seen.modify (·.insert n)
  let some ci := env.find? n | return
  if let .axiomInfo _ := ci then axs.modify (·.insert n)
  let v := match ci with
    | .defnInfo d => d.value.getUsedConstants
    | .thmInfo t => t.value.getUsedConstants
    | .opaqueInfo o => o.value.getUsedConstants
    | _ => #[]
  for c in ci.type.getUsedConstants ++ v do reach env c seen axs

unsafe def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `Views }] {} 0 (loadExts := true)
  let ok : NameSet := NameSet.empty |>.insert ``propext |>.insert ``Classical.choice |>.insert ``Quot.sound
  let mut count := 0
  let mut bad := 0
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`Views).isPrefixOf mod do continue
    let axs ← IO.mkRef NameSet.empty
    let s ← IO.mkRef NameSet.empty
    reach env n s axs
    count := count + 1
    for a in (← axs.get).toList do
      unless ok.contains a do
        IO.println s!"{n} depends on axiom {a}"
        bad := bad + 1
  IO.println s!"{count} declarations checked; {bad} depend on an axiom outside [propext, Classical.choice, Quot.sound]."
  return (if bad == 0 then 0 else 1)
