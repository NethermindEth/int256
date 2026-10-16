import UInt256.Methods.Compare.PrimitiveSafetyWrapper64
import UInt256.Safety.ScalarOperatorResult

namespace UInt256Proof.Compare.GtUInt256Int64
open UInt256Model.Safety UInt256Proof.Compare.PrimitiveSafety

/-- Exact comparison of the initial UInt256 and scalar values, with checked
    finite return and preservation of caller memory. -/
theorem scalar_correctness : ScalarOperatorContract false false CIL.Value.i64
    (fun input word => decide ((input.toNat : Int) > word.toInt))
    Extracted.program Extracted.entryIndex := by
  have meaning (input : BitVec 256) (word : BitVec 64) :
      (predicate leafSigned leafScalarFirst input word != wrapperNegate) =
        decide ((input.toNat : Int) > word.toInt) := by
    simp [show leafSigned = true from rfl,
      show leafScalarFirst = true from rfl,
      show wrapperNegate = false from rfl, predicate]
    <;> (by_cases ordered : (input.toNat : Int) > word.toInt <;> simp_all <;> omega)
  simpa only [show wrapperScalarFirst = false from rfl] using
    ScalarOperatorContract.result_congr meaning checked64

#print axioms scalar_correctness
end UInt256Proof.Compare.GtUInt256Int64
