import CIL.ExecutionLemmas
import UInt256.Representation

open CIL

namespace UInt256Model

-- Observable contract: initial-input modular sum, normal return, and preservation
-- of caller bytes outside the output, including arbitrary overlapping ranges.
def Contract (p : Program) (entry : Nat) (initial : Bytes) (left right out : Nat) : Prop :=
  ∃ fuel final, invoke p fuel entry [.object left, .object right, .object out]
      (byteMemory initial) = some (final, []) ∧
    ∀ address, final (.byte address) =
      (writeBytes (byteMemory initial) out
        (byteValue initial left + byteValue initial right).toNat 32) (.byte address)

end UInt256Model
