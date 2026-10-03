import CIL.ExecutionLemmas
import UInt256.Representation

open CIL UInt256Model
namespace UInt256Model.Bitwise

inductive Binary where
  | and | or | xor
  deriving DecidableEq

def applyBinary (operation : Binary) (left right : BitVec 256) : BitVec 256 :=
  match operation with
  | .and => left &&& right
  | .or => left ||| right
  | .xor => left ^^^ right

def Contract (p : Program) (entry : Nat) (operation : Binary)
    (initial : Bytes) (left right out : Nat) : Prop :=
  ∃ fuel final, invoke p fuel entry [.object left, .object right, .object out]
      (byteMemory initial) = some (final, []) ∧
    ∀ address, final (.byte address) = (writeBytes (byteMemory initial) out
      (applyBinary operation (byteValue initial left) (byteValue initial right)).toNat
      32) (.byte address)

def NotContract (p : Program) (entry : Nat) (initial : Bytes) (input out : Nat) : Prop :=
  ∃ fuel final, invoke p fuel entry [.object input, .object out]
      (byteMemory initial) = some (final, []) ∧
    ∀ address, final (.byte address) = (writeBytes (byteMemory initial) out
      (~~~byteValue initial input).toNat 32) (.byte address)

def ReturnContract (p : Program) (entry : Nat) (operation : Binary)
    (initial : Bytes) (left right : Nat) : Prop :=
  ∃ fuel final, invoke p fuel entry [.object left, .object right] (byteMemory initial) =
      some (final, [.v256 (applyBinary operation (byteValue initial left)
        (byteValue initial right))]) ∧
    ∀ address, final (.byte address) = (byteMemory initial) (.byte address)

def NotReturnContract (p : Program) (entry : Nat) (initial : Bytes) (input : Nat) : Prop :=
  ∃ fuel final, invoke p fuel entry [.object input] (byteMemory initial) =
      some (final, [.v256 (~~~byteValue initial input)]) ∧
    ∀ address, final (.byte address) = (byteMemory initial) (.byte address)

end UInt256Model.Bitwise
