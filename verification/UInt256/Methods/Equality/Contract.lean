import CIL.ExecutionLemmas
import UInt256.Representation

open CIL UInt256Model
namespace UInt256Model.Equality

def booleanWord (b : Bool) : W32 := if b then 1 else 0

/-- Pure observable return and preservation of every caller byte. -/
def ResultContract (p : Program) (entry : Nat) (args : List Value)
    (initial : Bytes) (expected : Bool) : Prop :=
  ∃ fuel final, invoke p fuel entry args (byteMemory initial) =
      some (final, [.i32 (booleanWord expected)]) ∧
    ∀ address, final (.byte address) = (byteMemory initial) (.byte address)

def Contract (p : Program) (entry : Nat) (initial : Bytes) (left right : Nat) : Prop :=
  ResultContract p entry [.object left, .object right] initial
    (decide (byteValue initial left = byteValue initial right))

def InequalityContract (p : Program) (entry : Nat) (initial : Bytes)
    (left right : Nat) : Prop :=
  ResultContract p entry [.object left, .object right] initial
    (decide (byteValue initial left ≠ byteValue initial right))

def SnapshotContract (p : Program) (entry : Nat) (initial : Bytes)
    (left : Nat) (right : BitVec 256) : Prop :=
  ResultContract p entry [.object left, .v256 right] initial
    (decide (byteValue initial left = right))

/-- Signedness belongs to the declared primitive operand, not the UInt256. -/
inductive Scalar where
  | u32 (bits : W32) | u64 (bits : W64)
  | s32 (bits : W32) | s64 (bits : W64)

def Scalar.argument : Scalar → Value
  | .u32 bits | .s32 bits => .i32 bits
  | .u64 bits | .s64 bits => .i64 bits

def Scalar.number : Scalar → Int
  | .u32 bits => bits.toNat
  | .u64 bits => bits.toNat
  | .s32 bits => bits.toInt
  | .s64 bits => bits.toInt

def ScalarContract (p : Program) (entry : Nat) (initial : Bytes)
    (input : Nat) (scalar : Scalar) (scalarFirst : Bool) (negateResult : Bool := false) : Prop :=
  ResultContract p entry (if scalarFirst then [scalar.argument, .object input]
    else [.object input, scalar.argument]) initial
    ((decide (((byteValue initial input).toNat : Int) = scalar.number)) != negateResult)

end UInt256Model.Equality
