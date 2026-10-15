import UInt256.Methods.Compare.PrimitiveLeafContract
import UInt256.Methods.Compare.PrimitiveArithmetic
import UInt256.Methods.Compare.PrimitiveSafetyLeaf
import UInt256.Safety.CallerSetup


namespace UInt256Proof.Compare.PrimitiveSafety
open CIL.Safety UInt256Model.Safety

theorem leaf_result_math (memory : Memory) (input : Reference) (word : BitVec 64) :
    leafResult memory input word =
      if predicate leafSigned leafScalarFirst (inputValue memory input) word then 1 else 0 := by
  have same : UInt256Model.value (inputLimb memory input) = inputValue memory input :=
    UInt256Proof.input_value (fun offset => (memory.cells input.allocation offset).bits) input.offset
  have result := limbs_result_math leafSigned leafScalarFirst (inputLimb memory input) word
  rw [same] at result
  exact result

theorem leaf_checked : ScalarOperatorContract leafScalarFirst false CIL.Value.i64
    (predicate leafSigned leafScalarFirst) Extracted.program leafIndex :=
  PrimitiveLeaf.checked_template leafSigned leafScalarFirst Extracted.program leafIndex (by rfl)

#print axioms leaf_result_math
#print axioms leaf_checked
end UInt256Proof.Compare.PrimitiveSafety
