import CIL.ExecutionLemmas
import UInt256.Representation

open CIL UInt256Model

namespace UInt256Proof.Reporting

inductive Operation where
  | add | subtract
  deriving DecidableEq, Repr

def result (operation : Operation) (a b : BitVec 256) : BitVec 256 :=
  match operation with
  | .add => a + b
  | .subtract => a - b

def flag (operation : Operation) (a b : BitVec 256) : Bool :=
  match operation with
  | .add => decide (2 ^ 256 ≤ a.toNat + b.toNat)
  | .subtract => decide (a.toNat < b.toNat)

theorem add_flag_iff (a b : BitVec 256) :
    flag .add a b = true ↔ 2 ^ 256 ≤ a.toNat + b.toNat := by
  simp only [flag, decide_eq_true_eq]

theorem subtract_flag_iff (a b : BitVec 256) :
    flag .subtract a b = true ↔ a.toNat < b.toNat := by
  simp only [flag, decide_eq_true_eq]

end UInt256Proof.Reporting
