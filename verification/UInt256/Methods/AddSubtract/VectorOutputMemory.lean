import UInt256.Methods.AddSubtract.VectorOperands
import UInt256.Safety.OutputAccess

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety

/-- Decode a completely initialized vector snapshot before executing a load. -/
theorem vector_load_snapshot (memory : Memory) (reference : Reference) (value : BitVec 256)
    (loaded : read memory reference 32 1 = .ok (numberBytes value.toNat 32)) :
    loadValue memory (.address reference) 32 = .ok (.v256 value) := by
  simp only [loadValue, dereference, loaded, checkedAt, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure, byteNumber_numberBytes]
  have bound : value.toNat < 256^32 := value.isLt
  rw [Nat.mod_eq_of_lt bound]
  simp

#print axioms vector_load_snapshot

/-- A complete output write initializes its bytes while retaining access authority
    and every callee-private snapshot. No input/output disjointness is required. -/
theorem vector_output_update (original entered current : Memory)
    (inputs outputs : List Reference) (output : Reference) (value : BitVec 256)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (outputMember : output ∈ outputs)
    (authority : AccessBelow entered.nextIdentity entered current) :
    ∃ after,
      write current output (numberBytes value.toNat 32) 1 = .ok after ∧
      read after output 32 1 = .ok (numberBytes value.toNat 32) ∧
      CallingConditions Extracted.program after inputs outputs ∧
      AccessBelow entered.nextIdentity entered after ∧
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = current.cells id offset) ∧
      (∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
        read current reference width alignment = .ok bytes → read after reference width alignment = .ok bytes) ∧
      current.nextIdentity ≤ after.nextIdentity := by
  have length : (numberBytes value.toNat 32).length = 32 := by simp [numberBytes]
  obtain ⟨after, written, afterCall, outside, readback⟩ := currentCall.write_output_slice
    outputMember 0 (numberBytes value.toNat 32) (by rw [length]; decide) (by rw [length]; decide)
  simp only [Nat.add_zero, length] at written readback
  have privateReads : ∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
      read current reference width alignment = .ok bytes → read after reference width alignment = .ok bytes := by
    intro reference width alignment bytes fresh loaded
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed outputMember)
    have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
    exact write_preserves_disjoint_read written loaded
      (Or.inl (Nat.ne_of_gt (Nat.lt_of_lt_of_le old fresh)))
  exact ⟨after, written, readback, afterCall,
    authority.trans (write_preserves_access_below written _), outside, privateReads,
    (write_extends_allocations _ _ _ _ _ written).next⟩

#print axioms vector_output_update
end UInt256Proof.AddSubtract.Safety
