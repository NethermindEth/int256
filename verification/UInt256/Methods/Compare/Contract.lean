import UInt256.Methods.Equality.Contract

open CIL UInt256Model
namespace UInt256Model.Compare

inductive Relation where
  | less | lessEqual | greater | greaterEqual
  deriving DecidableEq

def holds (relation : Relation) (left right : Int) : Bool :=
  match relation with
  | .less => decide (left < right)
  | .lessEqual => decide (left ≤ right)
  | .greater => decide (left > right)
  | .greaterEqual => decide (left ≥ right)

def Contract (p : Program) (entry : Nat) (relation : Relation)
    (initial : Bytes) (left right : Nat) : Prop :=
  Equality.ResultContract p entry [.object left, .object right] initial
    (holds relation (byteValue initial left).toNat (byteValue initial right).toNat)

def ScalarContract (p : Program) (entry : Nat) (relation : Relation)
    (initial : Bytes) (input : Nat) (scalar : Equality.Scalar) (scalarFirst : Bool) : Prop :=
  Equality.ResultContract p entry
    (if scalarFirst then [scalar.argument, .object input] else [.object input, scalar.argument])
    initial (if scalarFirst then holds relation scalar.number (byteValue initial input).toNat
      else holds relation (byteValue initial input).toNat scalar.number)

/-- The declared ulong/UInt256 <= overload passes its UInt256 operand by value. -/
def ScalarSnapshotContract (p : Program) (entry : Nat) (relation : Relation)
    (initial : Bytes) (scalar : Equality.Scalar) (right : BitVec 256) : Prop :=
  Equality.ResultContract p entry [scalar.argument, .v256 right] initial
    (holds relation scalar.number right.toNat)

/-- Exact values supplied by the current three-way comparison API. -/
def compareWord (left right : Nat) : W32 :=
  if left < right then BitVec.ofInt 32 (-1) else if left = right then 0 else 1

/-- IComparable promises ordering by sign, not particular nonzero magnitudes. -/
def signAgreement (result : W32) (left right : Nat) : Prop :=
  (result.toInt < 0 ↔ left < right) ∧
  (result.toInt = 0 ↔ left = right) ∧
  (0 < result.toInt ↔ right < left)

def ThreeWayContract (p : Program) (entry : Nat) (initial : Bytes)
    (left right : Nat) : Prop :=
  ∃ fuel final result, invoke p fuel entry [.object left, .object right] (byteMemory initial) =
      some (final, [.i32 result]) ∧
    signAgreement result (byteValue initial left).toNat (byteValue initial right).toNat ∧
    ∀ address, final (.byte address) = (byteMemory initial) (.byte address)

def ThreeWaySnapshotContract (p : Program) (entry : Nat) (initial : Bytes)
    (left : Nat) (right : BitVec 256) : Prop :=
  ∃ fuel final result, invoke p fuel entry [.object left, .v256 right] (byteMemory initial) =
      some (final, [.i32 result]) ∧
    signAgreement result (byteValue initial left).toNat right.toNat ∧
    ∀ address, final (.byte address) = (byteMemory initial) (.byte address)

/-- A stronger implementation fact, never a prerequisite for the public gate. -/
def ExactThreeWayContract (p : Program) (entry : Nat) (initial : Bytes)
    (left right : Nat) : Prop :=
  ∃ fuel final, invoke p fuel entry [.object left, .object right] (byteMemory initial) =
      some (final, [.i32 (compareWord (byteValue initial left).toNat
        (byteValue initial right).toNat)]) ∧
    ∀ address, final (.byte address) = (byteMemory initial) (.byte address)

end UInt256Model.Compare
