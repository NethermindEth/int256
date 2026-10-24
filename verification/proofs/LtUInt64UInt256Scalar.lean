import UInt256.Methods.Compare.PrimitiveSafetyWrapper64
import UInt256.Safety.ScalarOperatorResult

namespace UInt256Proof.Compare.LtUInt64UInt256
open UInt256Model.Safety UInt256Proof.Compare.PrimitiveSafety

/-- Exact comparison of the initial UInt256 and scalar values, with checked
    finite return and preservation of caller memory. -/
theorem scalar_correctness : ScalarOperatorContract true false CIL.Value.i64
    (fun input word => decide ((word.toNat : Int) < (input.toNat : Int)))
    Extracted.program Extracted.entryIndex := by
  have meaning (input : BitVec 256) (word : BitVec 64) :
      (predicate leafSigned leafScalarFirst input word != wrapperNegate) =
        decide ((word.toNat : Int) < (input.toNat : Int)) := by
    simp [show leafSigned = false from rfl,
      show leafScalarFirst = true from rfl,
      show wrapperNegate = false from rfl, predicate]
    <;> (by_cases ordered : (word.toNat : Int) < (input.toNat : Int) <;> simp_all <;> omega)
  simpa only [show wrapperScalarFirst = true from rfl] using
    ScalarOperatorContract.result_congr meaning checked64

#print axioms scalar_correctness
end UInt256Proof.Compare.LtUInt64UInt256
