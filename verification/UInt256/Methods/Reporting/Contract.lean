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

/-- Both the initial-operand result and the exact returned Boolean are required.
    Every caller byte is specified, permitting arbitrary overlap of the operands
    and the single 32-byte output. No helper or instruction identity occurs here. -/
def Contract (operation : Operation) (program : Program) (entry : Nat)
    (initial : Bytes) (left right out : Nat) : Prop :=
  ∃ fuel final,
    invoke program fuel entry [.object left, .object right, .object out]
      (byteMemory initial) = some (final,
        [.i32 (if flag operation (byteValue initial left) (byteValue initial right) then 1 else 0)]) ∧
    ∀ address, final (.byte address) =
      (writeBytes (byteMemory initial) out
        (result operation (byteValue initial left) (byteValue initial right)).toNat 32) (.byte address)

theorem add_flag_iff (a b : BitVec 256) :
    flag .add a b = true ↔ 2 ^ 256 ≤ a.toNat + b.toNat := by
  simp only [flag, decide_eq_true_eq]

theorem subtract_flag_iff (a b : BitVec 256) :
    flag .subtract a b = true ↔ a.toNat < b.toNat := by
  simp only [flag, decide_eq_true_eq]

end UInt256Proof.Reporting

#print axioms UInt256Proof.Reporting.add_flag_iff
#print axioms UInt256Proof.Reporting.subtract_flag_iff
