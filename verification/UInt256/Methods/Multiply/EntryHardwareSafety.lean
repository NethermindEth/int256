import UInt256.Methods.Multiply.EntrySafetyInvoke
import UInt256.Methods.Multiply.FullSafetyScalarTop
import UInt256.Methods.Multiply.WordHardwareAudit

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem hardware_multiply_scalar_invoke (memory : Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ fuel final,
      invoke Extracted.program fuel multiplyIndex (productArgs left right output) memory = .ok (final, []) ∧
      ProductResult memory final left right output [] :=
  multiply_invoke (fun memory a b output wf writable =>
    hardware_word_invoke memory a b output wf writable hardware_profile_supported)
    full_scalar_top memory left right output call

#print axioms hardware_multiply_scalar_invoke
end UInt256Proof.Multiply.Safety
