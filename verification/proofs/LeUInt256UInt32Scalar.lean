import UInt256.Methods.Compare.PrimitiveSafetyWrapper32
import UInt256.Safety.ScalarOperatorResult

namespace UInt256Proof.Compare.LeUInt256UInt32
open UInt256Model.Safety UInt256Proof.Compare.PrimitiveSafety

/-- Exact comparison of the initial UInt256 and scalar values, with checked
    finite return and preservation of caller memory. -/
theorem scalar_correctness : ScalarOperatorContract false false CIL.Value.i32
    (fun input word => decide ((input.toNat : Int) ≤ (word.toNat : Int)))
    Extracted.program Extracted.entryIndex := by
  have meaning (input : BitVec 256) (word : BitVec 32) :
      (predicate leafSigned leafScalarFirst input (widen32 word) != wrapperNegate) =
        decide ((input.toNat : Int) ≤ (word.toNat : Int)) := by
    simp [show leafSigned = true from rfl,
      show leafScalarFirst = true from rfl,
      show wrapperNegate = true from rfl, predicate, show wrapperSigned32 = false from rfl, widen32, UInt256Proof.Compare.zeroExtend32_toInt]
    <;> (by_cases ordered : (input.toNat : Int) ≤ (word.toNat : Int) <;> simp_all <;> omega)
  simpa only [show wrapperScalarFirst = false from rfl] using
    ScalarOperatorContract.result_congr meaning checked32

#print axioms scalar_correctness
end UInt256Proof.Compare.LeUInt256UInt32
