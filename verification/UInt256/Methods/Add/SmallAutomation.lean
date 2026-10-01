import UInt256.Methods.Add.Automation
import UInt256.Methods.Add.Small

open Lean Meta Elab Tactic CIL UInt256Model

namespace UInt256Proof

elab "cil_small_call" : tactic => withMainContext do
  unless (← getEnv).contains (Name.mkSimple "Extracted" |>.str "addScalarUInt64Index") do
    throwError "No extracted summary candidate"
  let mut selected : Option Expr := none
  for candidate in collectRuns (← getMainTarget) do
    if candidate.hasLooseBVars then continue
    let args := candidate.getAppArgs
    if (← isDefEq args[2]! (mkConst (Name.mkSimple "Extracted" |>.str "addScalarUInt64Index"))) &&
        (← isDefEq args[3]! (mkNatLit 0)) then
      selected := some candidate
      break
  let some candidate := selected | throwError "No applicable proved small-add helper call"
  let call := candidate.getAppArgs
  let values ← listTerms call[4]!
  unless values.size == 3 do throwError "Small-add helper argument count changed"
  let base ← PrettyPrinter.delab (← constructorArg ``CIL.Value.object values[0]!)
  let word ← PrettyPrinter.delab (← constructorArg ``CIL.Value.i64 values[1]!)
  let out ← PrettyPrinter.delab (← constructorArg ``CIL.Value.object values[2]!)
  let memory ← PrettyPrinter.delab call[7]!
  let frame ← PrettyPrinter.delab call[5]!
  let fuel ← PrettyPrinter.delab call[1]!
  let final := mkIdent (← mkFreshUserName `smallMemory)
  let flag := mkIdent (← mkFreshUserName `smallFlag)
  let hr := mkIdent (← mkFreshUserName `smallRun)
  let hb := mkIdent (← mkFreshUserName `smallBytes)
  evalTactic (← `(tactic|
    obtain ⟨$final:ident, $flag:ident, $hr:ident, $hb:ident⟩ :=
      execute_small_words_at $memory $base $out $frame $fuel _ $word
        (by intro i; simp_all [initLocals]; all_goals rfl)
        (by simp [cil_code]; all_goals omega)))
  evalTactic (← `(tactic| simp [cil_code, initLocals] at $hr:ident))
  evalTactic (← `(tactic| rw [$hr:ident]))
  evalTactic (← `(tactic| simp only [Option.bind_some]))

end UInt256Proof
