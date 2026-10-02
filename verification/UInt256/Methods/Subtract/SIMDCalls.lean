import UInt256.Methods.Subtract.SIMD128
import UInt256.Methods.Subtract.SIMD256

open Lean Meta Elab Tactic CIL UInt256Model

namespace UInt256Proof

private def subtractVectorCall (index theoremName : Name) (label : String)
    (a b : TSyntax `ident) : TacticM Unit := withMainContext do
  let (call, values) ← provedCall index theoremName label 3
  let theoremSyntax := mkIdent theoremName
  let left ← PrettyPrinter.delab (← constructorArg ``CIL.Value.object values[0]!)
  let right ← PrettyPrinter.delab (← constructorArg ``CIL.Value.object values[1]!)
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
      $theoremSyntax:ident $memory $left $right $out $frame $fuel $a:ident $b:ident
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

elab "cil_subtract128_call" a:ident b:ident : tactic =>
  subtractVectorCall `Extracted.subtractVector128Index
    `UInt256Proof.execute_subtract128_at "128-bit subtraction" a b

elab "cil_subtract256_call" a:ident b:ident : tactic =>
  subtractVectorCall `Extracted.subtractVector256Index
    `UInt256Proof.execute_subtract256_at "256-bit subtraction" a b

end UInt256Proof
