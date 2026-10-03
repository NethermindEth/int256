import CIL.Semantics
import UInt256.Representation

open CIL UInt256Model

namespace UInt256Proof.Multiply

/-- Wrapping multiplication of the initial values, finite normal return,
    arbitrary overlap and the exact 32-byte output update. -/
def Contract (program : Program) (entry : Nat) (initial : Bytes) (left right out : Nat) : Prop :=
  ∃ fuel final,
    invoke program fuel entry [.object left, .object right, .object out]
      (byteMemory initial) = some (final, []) ∧
    ∀ address, final (.byte address) =
      (writeBytes (byteMemory initial) out
        (byteValue initial left * byteValue initial right).toNat 32) (.byte address)

end UInt256Proof.Multiply
