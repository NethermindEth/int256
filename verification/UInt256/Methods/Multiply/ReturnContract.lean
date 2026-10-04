import UInt256.Methods.Multiply.Contract
open CIL UInt256Model
namespace UInt256Proof.Multiply

/-- A returned wrapping product preserves every caller byte. -/
def ReturnContract (program : Program) (entry : Nat) (initial : Bytes) (left right : Nat) : Prop :=
  ∃ fuel final, invoke program fuel entry [.object left, .object right] (byteMemory initial) =
      some (final, [.v256 (byteValue initial left * byteValue initial right)]) ∧
    ∀ address, final (.byte address) = byteMemory initial (.byte address)

def ScalarReturnContract (program : Program) (entry width : Nat) (wordLeft : Bool)
    (initial : Bytes) (input : Nat) (word : BitVec width) : Prop :=
  let argument := if width = 32 then Value.i32 (word.setWidth 32) else Value.i64 (word.setWidth 64)
  let arguments := if wordLeft then [argument, Value.object input] else [Value.object input, argument]
  ∃ fuel final, invoke program fuel entry arguments (byteMemory initial) =
      some (final, [.v256 (byteValue initial input * BitVec.ofNat 256 word.toNat)]) ∧
    ∀ address, final (.byte address) = byteMemory initial (.byte address)

end UInt256Proof.Multiply
