import UInt256.Methods.Compare.PrimitiveSafetyWrapper32
import UInt256.Safety.ScalarOperatorResult

namespace UInt256Proof.Compare.GeInt32UInt256
open UInt256Model.Safety UInt256Proof.Compare.PrimitiveSafety

/-- Exact comparison of the initial UInt256 and scalar values, with checked
    finite return and preservation of caller memory. -/
theorem scalar_correctness : ScalarOperatorContract true false CIL.Value.i32
    (fun input word => decide (word.toInt ≥ (input.toNat : Int)))
    Extracted.program Extracted.entryIndex := by
  have meaning (input : BitVec 256) (word : BitVec 32) :
      (predicate leafSigned leafScalarFirst input (widen32 word) != wrapperNegate) =
        decide (word.toInt ≥ (input.toNat : Int)) := by
    simp [show leafSigned = true from rfl,
      show leafScalarFirst = true from rfl,
      show wrapperNegate = true from rfl, predicate, show wrapperSigned32 = true from rfl, widen32, BitVec.toInt_signExtend_of_le (by decide : 32 ≤ 64)]
    <;> (by_cases ordered : word.toInt ≥ (input.toNat : Int) <;> simp_all <;> omega)
  simpa only [show wrapperScalarFirst = true from rfl] using
    ScalarOperatorContract.result_congr meaning checked32

#print axioms scalar_correctness
end UInt256Proof.Compare.GeInt32UInt256
