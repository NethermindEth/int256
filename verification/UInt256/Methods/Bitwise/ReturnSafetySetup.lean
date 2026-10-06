import Extracted
import UInt256.Safety.BinaryReturnSetup

namespace UInt256Proof.Bitwise.Safety
open CIL.Safety UInt256Model.Safety

abbrev resultSpecs := binaryResultSpecs

theorem return_setup (memory : Memory) (left right : Reference)
    (call : CallingConditions Extracted.program memory [left, right] []) :
    ∃ frame entered temporary,
      enterFrame Extracted.entryBody (readOnlyArguments [left, right]) memory = .ok (frame, entered) ∧
      frame.locals = [.bytes .vector256 temporary] ∧
      memory.nextIdentity ≤ temporary.allocation ∧
      CallingConditions Extracted.program entered [left, right] [temporary] ∧
      MemoryBelow memory.nextIdentity memory entered :=
  binary_return_setup Extracted.program Extracted.entryBody (by rfl) (by rfl) (by rfl)
    memory left right call

#print axioms return_setup
end UInt256Proof.Bitwise.Safety
