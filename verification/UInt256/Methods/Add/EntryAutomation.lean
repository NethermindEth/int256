import UInt256.Methods.Add.Execution

open Lean Meta Elab Tactic CIL UInt256Model

namespace UInt256Proof

elab "cil_scalar_call" : tactic => withMainContext do
  unless (← getEnv).contains (Name.mkSimple "Extracted" |>.str "addScalarIndex") &&
      (← getEnv).contains (Name.mkSimple "UInt256Proof" |>.str "execute_scalar_words_at") do
    throwError "No proved summary available"
  let mut selected : Option Expr := none
  for candidate in collectRuns (← getMainTarget) do
    if candidate.hasLooseBVars then continue
    let args := candidate.getAppArgs
    if (← isDefEq args[2]! (mkConst (Name.mkSimple "Extracted" |>.str "addScalarIndex"))) &&
        (← isDefEq args[3]! (mkNatLit 0)) then
      selected := some candidate
      break
  let some candidate := selected | throwError "No applicable proved scalar-add helper call"
  let call := candidate.getAppArgs
  let values ← listTerms call[4]!
  unless values.size == 4 do throwError "Scalar-add helper argument count changed"
  let left ← PrettyPrinter.delab (← constructorArg ``CIL.Value.object values[0]!)
  let right ← PrettyPrinter.delab (← constructorArg ``CIL.Value.object values[1]!)
  unless ← isDefEq values[3]! (← elabTerm (← `(Value.i32 0)) none) do
    throwError "Scalar contract requires a false initial flag"
  let out ← PrettyPrinter.delab (← constructorArg ``CIL.Value.object values[2]!)
  let memory ← PrettyPrinter.delab call[7]!
  let frame ← PrettyPrinter.delab call[5]!
  let fuel ← PrettyPrinter.delab call[1]!
  let final := mkIdent (← mkFreshUserName `scalarMemory)
  let flag := mkIdent (← mkFreshUserName `scalarFlag)
  let hr := mkIdent (← mkFreshUserName `scalarRun)
  let hb := mkIdent (← mkFreshUserName `scalarBytes)
  evalTactic (← `(tactic|
    obtain ⟨$final:ident, $flag:ident, $hr:ident, $hb:ident⟩ :=
      execute_scalar_words_at $memory $left $right $out $frame $fuel _ _
        (by intro i; simp_all [initLocals]; all_goals rfl)
        (by intro i; simp_all [initLocals]; all_goals rfl)
        (by simp [cil_code]; all_goals omega)))
  evalTactic (← `(tactic| simp [cil_code, initLocals] at $hr:ident))
  evalTactic (← `(tactic| rw [$hr:ident]))
  evalTactic (← `(tactic| simp only [Option.bind_some]))

end UInt256Proof
