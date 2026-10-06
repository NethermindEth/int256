import Extracted
import UInt256.Safety.Calling

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

/-- For the selected Add extraction, every reachable helper has compatible
    locals and no by-value aggregate argument homes. Names/counts are not fixed. -/
theorem program_frames_fit (args : List Value) :
    ∀ body ∈ Extracted.program, FrameSetupFits body args := by
  simp [Extracted.program, cil_code, FrameSetupFits, InitializersFit, InitializerFits, AggregateArgumentsFit]

/-- Kernel-check compatibility of the current extracted local metadata.
    This is an entry-setup checkpoint, not the combined Add certificate. -/
theorem entry_frame_fits (left right output : Reference) :
    FrameSetupFits Extracted.entryBody (binaryArguments left right output) := by
  simp [cil_code, FrameSetupFits, InitializersFit, InitializerFits, AggregateArgumentsFit]

theorem checked_entry_setup : ∀ (memory : Memory) (left right output : Reference),
    CallingConditions Extracted.program memory [left, right] [output] →
    ∃ frame entered,
      enterFrame Extracted.entryBody (binaryArguments left right output) memory = .ok (frame, entered) ∧
      LiveState Extracted.program (binaryArguments left right output) frame [] entered := by
  intro memory left right output call
  exact call.binary_setup_succeeds (entry_frame_fits left right output)

#print axioms entry_frame_fits
#print axioms checked_entry_setup
#print axioms program_frames_fit

end UInt256Proof.Safety
