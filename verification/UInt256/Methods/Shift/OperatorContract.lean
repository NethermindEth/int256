import UInt256.Methods.Shift.Contract

open CIL UInt256Model

namespace UInt256Proof.Shift

/-- Shift operators return the mathematical value and preserve every caller byte.
    Their output temporary belongs to the private execution frame. -/
def OperatorContract (direction : Direction) (program : Program) (entry : Nat)
    (initial : Bytes) (input : Nat) (count : W32) : Prop :=
  ∃ fuel final,
    invoke program fuel entry [.object input, .i32 count] (byteMemory initial) =
      some (final, [.v256 (result direction (byteValue initial input) count)]) ∧
    ∀ address, final (.byte address) = byteMemory initial (.byte address)

end UInt256Proof.Shift
