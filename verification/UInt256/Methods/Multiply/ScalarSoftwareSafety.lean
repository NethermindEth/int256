import UInt256.Methods.Multiply.ScalarSafety
import UInt256.Methods.Multiply.WordSoftwareSafety

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

/-- The software path discharges the widening-call contract using the actual
    extracted helper execution proof. No helper correctness premise remains. -/
theorem software_scalar_invoke (memory : Memory) (input output : Reference)
    (word : BitVec 64) (call : CallingConditions Extracted.program memory [input] [output]) :
    ∃ fuel final,
      invoke Extracted.program fuel scalarIndex (scalarArgs input word output) memory = .ok (final, []) ∧
      ScalarResult memory final input output word [] :=
  scalar_invoke software_word_invoke memory input output word call

#print axioms software_scalar_invoke
end UInt256Proof.Multiply.Safety
