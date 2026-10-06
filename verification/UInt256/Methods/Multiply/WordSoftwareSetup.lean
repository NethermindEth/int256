import UInt256.Methods.Multiply.WordSafety
import CIL.Safety.UnknownHomes

namespace UInt256Proof.Multiply.Safety
open CIL.Safety

/-- The software helper may write all six private homes. No initialized read
    is granted by setup: each subsequent read requires its preceding store. -/
theorem word_unknown_homes (memory : Memory) (args : List Value) (wf : memory.WellFormed) :
    ∃ frame entered,
      enterFrame wordBody args memory = .ok (frame, entered) ∧
      WritableHomes entered memory.nextIdentity wordBody.localKinds frame.locals ∧
      MemoryBelow memory.nextIdentity memory entered ∧ entered.WellFormed := by
  apply unknown_frame_setup wordBody (by rfl) ?_ (by rfl) memory args wf
  have kinds : wordBody.localKinds = [.word32, .word32, .word32, .word64, .word64, .word64] := by rfl
  simp [kinds]

#print axioms word_unknown_homes
end UInt256Proof.Multiply.Safety
