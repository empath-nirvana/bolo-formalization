import BoCa
import Lean
open Lean Meta

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

run_meta do
  let env ← getEnv
  let h ← IO.FS.Handle.mk ((← IO.getEnv "EXTRACT_DUMP").getD "dump.tsv") .write
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`BoCa).isPrefixOf mod do continue
    let deps := (ci.type.getUsedConstants ++ (match ci with | .thmInfo t => t.value.getUsedConstants | .defnInfo d => d.value.getUsedConstants | .opaqueInfo d => d.value.getUsedConstants | _ => #[]))
    let deps := match ci with
      | .inductInfo ii => deps ++ ii.ctors.toArray
      | _ => deps
    let deps := deps.toList.eraseDups.filter (· != n)
    let rng ← findDeclarationRanges? n
    let r := match rng with
      | some r => s!"{r.range.pos.line}:{r.range.pos.column}\t{r.range.endPos.line}:{r.range.endPos.column}\t{r.selectionRange.pos.line}"
      | none => "-\t-\t-"
    h.putStrLn s!"{n}\t{mod}\t{kindOf ci}\t{isPrivateName n}\t{r}\t{",".intercalate (deps.map toString)}"
