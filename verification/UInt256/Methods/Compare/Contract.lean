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

/-- Exact values supplied by the current three-way comparison API. -/
def compareWord (left right : Nat) : W32 :=
  if left < right then BitVec.ofInt 32 (-1) else if left = right then 0 else 1

/-- IComparable promises ordering by sign, not particular nonzero magnitudes. -/
def signAgreement (result : W32) (left right : Nat) : Prop :=
  (result.toInt < 0 ↔ left < right) ∧
  (result.toInt = 0 ↔ left = right) ∧
  (0 < result.toInt ↔ right < left)

end UInt256Model.Compare
