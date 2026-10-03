import UInt256.Methods.Reporting.SmallAdd
import UInt256.Methods.Reporting.ScalarAdd
import UInt256.Methods.Reporting.SIMD128Add

open Lean Meta Elab Tactic CIL UInt256Model

namespace UInt256Proof.Reporting

elab "cil_reporting_add128_call" a:ident b:ident : tactic => withMainContext do
  let (call, values) ← provedCall `Extracted.addVector128Index
    `UInt256Proof.Reporting.execute_reporting128_at "reporting 128-bit addition" 4
  let detection ← constructorArg ``CIL.Value.i32 values[3]!
  unless ← isDefEq detection (← elabTerm (← `(BitVec.ofNat 32 1)) none) do
    throwError "reporting addition requires overflow detection"
  let left ← PrettyPrinter.delab (← constructorArg ``CIL.Value.object values[0]!)
  let right ← PrettyPrinter.delab (← constructorArg ``CIL.Value.object values[1]!)
  let out ← PrettyPrinter.delab (← constructorArg ``CIL.Value.object values[2]!)
  let memory ← PrettyPrinter.delab call[7]!
  let frame ← PrettyPrinter.delab call[5]!
  let fuel ← PrettyPrinter.delab call[1]!
  let final := mkIdent (← mkFreshUserName `vectorMemory)
  let hr := mkIdent (← mkFreshUserName `vectorRun)
  let hb := mkIdent (← mkFreshUserName `vectorBytes)
  evalTactic (← `(tactic|
    obtain ⟨$final:ident, $hr:ident, $hb:ident⟩ :=
      UInt256Proof.Reporting.execute_reporting128_at $memory $left $right $out $frame $fuel $a:ident $b:ident
        (by
          intro i
          rcases i with ⟨i, hi⟩
          have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
          rcases hc with h | h | h | h
          all_goals subst i; simp [*, write, initLocals]; all_goals rfl)
        (by
          intro i
          rcases i with ⟨i, hi⟩
          have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
          rcases hc with h | h | h | h
          all_goals subst i; simp [*, write, initLocals]; all_goals rfl)
        (by simp [cil_code]; all_goals omega)))
  rewriteHelperRun hr


elab "cil_reporting_small_call" : tactic => withMainContext do
  let (call, values) ← provedCall `Extracted.addScalarUInt64Index
    `UInt256Proof.Reporting.execute_small_report_at "small reporting add" 3
  let base ← PrettyPrinter.delab (← constructorArg ``CIL.Value.object values[0]!)
  let word ← PrettyPrinter.delab (← constructorArg ``CIL.Value.i64 values[1]!)
  let out ← PrettyPrinter.delab (← constructorArg ``CIL.Value.object values[2]!)
  let memory ← PrettyPrinter.delab call[7]!
  let frame ← PrettyPrinter.delab call[5]!
  let fuel ← PrettyPrinter.delab call[1]!
  let final := mkIdent (← mkFreshUserName `smallMemory)
  let hr := mkIdent (← mkFreshUserName `smallRun)
  let hb := mkIdent (← mkFreshUserName `smallBytes)
  evalTactic (← `(tactic|
    obtain ⟨$final:ident, $hr:ident, $hb:ident⟩ :=
      UInt256Proof.Reporting.execute_small_report_at $memory $base $out $frame $fuel _ $word
        (by intro i; simp_all [initLocals]; all_goals rfl)
        (by simp [cil_code]; all_goals omega)))
  rewriteHelperRun hr

end UInt256Proof.Reporting
