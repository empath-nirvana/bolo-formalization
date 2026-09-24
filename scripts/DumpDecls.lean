import Lean
/-!
Prints, for every declaration of the modules whose names start with one of the
prefixes in `$BRIDGE_PREFIXES` (comma-separated), a line

    name <TAB> kind <TAB> type <TAB> value

to the file `$BRIDGE_OUT`, where `type` and `value` are the raw printed
expressions (`value` only for definitions).  The module list to import is given
by `$BRIDGE_IMPORTS`.  `scripts/check-bridge.py` runs it once over this
repository and once over the source repository and compares the two outputs.
-/
open Lean

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

def oneLine (s : String) : String := s.replace "\n" " " |>.replace "\t" " "

unsafe def main : IO Unit := do
  let imps := ((← IO.getEnv "BRIDGE_IMPORTS").getD "").splitOn ","
  let pres := ((← IO.getEnv "BRIDGE_PREFIXES").getD "").splitOn ","
  let out := (← IO.getEnv "BRIDGE_OUT").getD "bridge.tsv"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (imps.toArray.map fun m => { module := m.toName }) {} 0 (loadExts := true)
  let h ← IO.FS.Handle.mk out .write
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := (env.header.moduleNames[idx.toNat]!).toString
    unless pres.any (fun p => mod.startsWith p) do continue
    let v := match ci with
      | .defnInfo d => oneLine (toString d.value)
      | _ => ""
    h.putStrLn s!"{n}\t{kindOf ci}\t{oneLine (toString ci.type)}\t{v}"
