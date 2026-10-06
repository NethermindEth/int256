import UInt256.Safety.LocalCallSafety
import UInt256.Methods.Multiply.WordCallSafety
import UInt256.Methods.Multiply.CountSafety

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem widening_local_effect (contract : WordContract) (current : Memory) (a b : BitVec 64)
    (wf : current.WellFormed) (reference : Reference)
    (ready : access current reference 8 1 true = .ok ()) :
    ∃ fuel after,
      invoke Extracted.program fuel wordIndex
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address reference)] current =
        .ok (after, [.scalar (.i64 (highProduct a b))]) ∧
      after.WellFormed ∧ read after reference 8 1 = .ok (numberBytes (lowProduct a b).toNat 8) ∧
      AccessBelow current.nextIdentity current after ∧
      (∀ id, id < current.nextIdentity → id ≠ reference.allocation → ∀ offset,
        after.cells id offset = current.cells id offset) := by
  obtain ⟨fuel, after, ran, valid, readback, access, outside⟩ := contract current a b reference wf ready
  exact ⟨fuel, after, ran, valid, readback, access, fun id old different offset =>
    outside id old offset (Or.inl different)⟩

theorem counting_local_effect {current : Memory} {frame : Frame} {known : Nat → Option (BitVec 64)}
    (snapshots : WordSnapshots current frame.locals known) (wf : current.WellFormed)
    (index : Nat) (a b count : BitVec 64) (initialized : known index = some count)
    (reference : Reference) (slot : frame.locals[index]? = some (.bytes .word64 reference))
    (ready : access current reference 8 1 true = .ok ()) :
    ∃ fuel after,
      invoke Extracted.program fuel Extracted.carryCountIndex
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address reference)] current =
        .ok (after, [.scalar (.i64 (a + b))]) ∧
      after.WellFormed ∧ read after reference 8 1 = .ok (numberBytes (countCarry a b count).toNat 8) ∧
      AccessBelow current.nextIdentity current after ∧
      (∀ id, id < current.nextIdentity → id ≠ reference.allocation → ∀ offset,
        after.cells id offset = current.cells id offset) := by
  obtain ⟨home, same, readable⟩ := snapshots index count initialized
  rw [slot] at same
  cases same
  obtain ⟨fuel, after, ran, valid, readback, access, outside⟩ := count_carry_invoke current a b count reference wf ready readable
  exact ⟨fuel, after, ran, valid, readback, access, fun id old different offset =>
    outside id old offset (Or.inl different)⟩

#print axioms widening_local_effect
#print axioms counting_local_effect
end UInt256Proof.Multiply.Safety
