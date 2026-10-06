import UInt256.Methods.Add.ScalarChecked
import CIL.Safety.ArgumentEquivalence
import UInt256.Methods.Add.OverflowEntrySafety

namespace UInt256Proof.Safety
open CIL.Safety UInt256Model.Safety

/-- The actual scalar body does not read detectOverflow. Its previously checked
    result already includes the mathematical carry out for every operand pair. -/
theorem overflow_scalar_checked (memory : CIL.Safety.Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ fuel final values,
      invoke Extracted.program fuel Extracted.addScalarIndex (overflowScalarArguments left right output) memory =
        .ok (final, values) ∧ AddResult memory final values left right output := by
  obtain ⟨fuel, final, values, invoked, result⟩ := scalar_checked memory left right output call
  have lookup : Extracted.program[Extracted.addScalarIndex]? = some Extracted.addScalarBody := by
    simp only [cil_code]
  have indices : ∀ index, CIL.Op.arg index ∈ Extracted.addScalarBody.code → index < 3 := by
    intro index member
    conv at member in Extracted.addScalarBody.code => cbv
    simp at member
    omega
  have agreement : ∀ index, CIL.Op.arg index ∈ Extracted.addScalarBody.code →
      (scalarArguments left right output)[index]? = (overflowScalarArguments left right output)[index]? := by
    intro index member
    have bound := indices index member
    have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases cases with rfl | rfl | rfl <;> rfl
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  have checked (flag : BitVec 32) :
      (binaryArguments left right output ++ [Value.scalar (.i32 flag)]).mapM (checkedValue memory) =
        .ok (binaryArguments left right output ++ [Value.scalar (.i32 flag)]) := by
    simp [binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have homes : Extracted.addScalarBody.aggregateArgs = [] := by rfl
  have setup : enterFrame Extracted.addScalarBody (scalarArguments left right output) memory =
      enterFrame Extracted.addScalarBody (overflowScalarArguments left right output) memory := by
    simp only [enterFrame, homes, makeArgumentHomes]
  have same := invoke_arguments_eq Extracted.program Extracted.addScalarIndex Extracted.addScalarBody
    lookup (scalarArguments left right output) (overflowScalarArguments left right output) agreement
    fuel memory (checked 0) (checked 1) setup
  exact ⟨fuel, final, values, same.symm.trans invoked, result⟩

#print axioms overflow_scalar_checked
end UInt256Proof.Safety
