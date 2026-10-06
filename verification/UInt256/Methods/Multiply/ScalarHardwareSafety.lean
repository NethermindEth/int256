import UInt256.Methods.Multiply.ScalarSafety
import UInt256.Methods.Multiply.WordHardwareAudit

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

/-- The hardware profile is checked, and each widening call is justified by
    the extracted hardware helper's execution theorem. -/
theorem hardware_scalar_invoke (memory : Memory) (input output : Reference)
    (word : BitVec 64) (call : CallingConditions Extracted.program memory [input] [output]) :
    ∃ fuel final,
      invoke Extracted.program fuel scalarIndex (scalarArgs input word output) memory = .ok (final, []) ∧
      ScalarResult memory final input output word [] :=
  scalar_invoke (fun memory a b output wf writable =>
    hardware_word_invoke memory a b output wf writable hardware_profile_supported)
    memory input output word call

#print axioms hardware_scalar_invoke
end UInt256Proof.Multiply.Safety
