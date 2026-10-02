import UInt256.Methods.Add.Execution
import UInt256.Methods.Add.SIMD128ARM
import UInt256.Methods.Add.SIMD128SSE
import UInt256.Methods.Add.SIMD256

open Lean Meta Elab Tactic CIL UInt256Model

namespace UInt256Proof

elab "cil_scalar_call" : tactic => withMainContext do
  let (call, values) ← provedCall `Extracted.addScalarIndex
    `UInt256Proof.execute_scalar_words_at "scalar-add" 4
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
  rewriteHelperRun hr

elab "cil_vector128_call" : tactic => withMainContext do
  let isArm ← isDefEq (mkApp (mkConst ``FeatureProfile.advSimd) (mkConst `Extracted.profile))
    (mkConst ``Bool.true)
  let summary := if isArm then `UInt256Proof.SIMD.execute_arm128_words_at
    else `UInt256Proof.SIMD.execute_sse128_words_at
  let summaryTerm := mkIdent summary
  let (call, values) ← provedCall `Extracted.addVector128Index summary "vector128-add" 4
  let left ← PrettyPrinter.delab (← constructorArg ``CIL.Value.object values[0]!)
  let right ← PrettyPrinter.delab (← constructorArg ``CIL.Value.object values[1]!)
  unless ← isDefEq values[3]! (← elabTerm (← `(Value.i32 0)) none) do
    throwError "Vector contract requires a false initial flag"
  let out ← PrettyPrinter.delab (← constructorArg ``CIL.Value.object values[2]!)
  let memory ← PrettyPrinter.delab call[7]!
  let frame ← PrettyPrinter.delab call[5]!
  let fuel ← PrettyPrinter.delab call[1]!
  let final := mkIdent (← mkFreshUserName `vectorMemory)
  let flag := mkIdent (← mkFreshUserName `vectorFlag)
  let hr := mkIdent (← mkFreshUserName `vectorRun)
  let hb := mkIdent (← mkFreshUserName `vectorBytes)
  evalTactic (← `(tactic|
    obtain ⟨$final:ident, $flag:ident, $hr:ident, $hb:ident⟩ :=
      $summaryTerm:ident $memory $left $right $out $frame $fuel _ _
        (by intro i; simp_all [initLocals]; all_goals rfl)
        (by intro i; simp_all [initLocals]; all_goals rfl)
        (by decide)
        (by simp [cil_code]; all_goals omega)))
  rewriteHelperRun hr

end UInt256Proof
