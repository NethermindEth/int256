import UInt256.Safety.OutputAccess
import UInt256.Safety.CallerSetup
import CIL.Safety.AccessSlices
import CIL.Safety.AccessBelow

namespace UInt256Model.Safety
open CIL.Safety

theorem CallingConditions.output_half_address {program : CIL.Program}
    {memory : Memory} {inputs outputs : List Reference}
    (call : CallingConditions program memory inputs outputs) {output : Reference}
    (member : output ∈ outputs) (index : Fin 2) :
    add memory output 16 (BitVec.ofNat 64 index.val) =
      .ok { output with offset := output.offset + 16 * index.val } := by
  obtain ⟨allocation, ready⟩ := access_requirements
    (call.1.2.2 (wordView output) (List.mem_map.mpr ⟨output, member, rfl⟩))
  dsimp only [wordView] at ready
  exact ready.add_slice call.1.1 16 index.val 16 (by decide) (by omega)

/-- A half-output write initializes exactly its destination slice. Private
    snapshots remain readable even when the caller's input and output overlap. -/
theorem output_half_update (program : CIL.Program) (original entered current : Memory)
    (inputs outputs : List Reference) (output : Reference) (index : Fin 2) (value : BitVec 128)
    (call : CallingConditions program original inputs outputs)
    (currentCall : CallingConditions program current inputs outputs)
    (member : output ∈ outputs)
    (authority : AccessBelow entered.nextIdentity entered current) :
    ∃ after,
      write current { output with offset := output.offset + 16 * index.val }
        (numberBytes value.toNat 16) 1 = .ok after ∧
      read after { output with offset := output.offset + 16 * index.val } 16 1 =
        .ok (numberBytes value.toNat 16) ∧
      CallingConditions program after inputs outputs ∧
      AccessBelow entered.nextIdentity entered after ∧
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = current.cells id offset) ∧
      (∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
        read current reference width alignment = .ok bytes → read after reference width alignment = .ok bytes) ∧
      current.nextIdentity ≤ after.nextIdentity := by
  have length : (numberBytes value.toNat 16).length = 16 := by simp [numberBytes]
  obtain ⟨after, written, afterCall, outside, readback⟩ := currentCall.write_output_slice
    member (16 * index.val) (numberBytes value.toNat 16) (by rw [length]; decide) (by rw [length]; omega)
  rw [length] at readback
  have privateReads : ∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
      read current reference width alignment = .ok bytes → read after reference width alignment = .ok bytes := by
    intro reference width alignment bytes fresh loaded
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed member)
    have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
    exact write_preserves_disjoint_read written loaded
      (Or.inl (Nat.ne_of_gt (Nat.lt_of_lt_of_le old fresh)))
  exact ⟨after, written, readback, afterCall,
    authority.trans (write_preserves_access_below written _), outside, privateReads,
    (write_extends_allocations _ _ _ _ _ written).next⟩

/-- Two half writes retain both initialized result halves. The second write is
    disjoint from the first half within the same output allocation. -/
theorem output_halves_update (program : CIL.Program) (original entered current : Memory)
    (inputs outputs : List Reference) (output : Reference) (low high : BitVec 128)
    (call : CallingConditions program original inputs outputs)
    (currentCall : CallingConditions program current inputs outputs)
    (member : output ∈ outputs)
    (authority : AccessBelow entered.nextIdentity entered current) :
    ∃ middle after,
      write current output (numberBytes low.toNat 16) 1 = .ok middle ∧
      write middle { output with offset := output.offset + 16 } (numberBytes high.toNat 16) 1 = .ok after ∧
      read after output 16 1 = .ok (numberBytes low.toNat 16) ∧
      read after { output with offset := output.offset + 16 } 16 1 = .ok (numberBytes high.toNat 16) ∧
      CallingConditions program middle inputs outputs ∧
      CallingConditions program after inputs outputs ∧
      AccessBelow entered.nextIdentity entered after ∧
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = current.cells id offset) ∧
      (∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
        read current reference width alignment = .ok bytes →
        read middle reference width alignment = .ok bytes ∧ read after reference width alignment = .ok bytes) ∧
      current.nextIdentity ≤ after.nextIdentity := by
  obtain ⟨middle, firstWrite, firstRead, middleCall, middleAuthority, firstOutside, firstPrivate, firstNext⟩ :=
    output_half_update program original entered current inputs outputs output 0 low call currentCall member authority
  simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] at firstWrite firstRead
  obtain ⟨after, secondWrite, secondRead, afterCall, afterAuthority, secondOutside, secondPrivate, secondNext⟩ :=
    output_half_update program original entered middle inputs outputs output 1 high call middleCall member middleAuthority
  simp only [Fin.val_one, Nat.mul_one] at secondWrite secondRead
  have retained := write_preserves_disjoint_read secondWrite firstRead (Or.inr (Or.inl (by simp)))
  refine ⟨middle, after, firstWrite, secondWrite, retained, secondRead, middleCall, afterCall,
    afterAuthority, ?_, ?_, Nat.le_trans firstNext secondNext⟩
  · intro id offset outside
    rw [secondOutside id offset outside, firstOutside id offset outside]
  · intro reference width alignment bytes bound loaded
    have kept := firstPrivate reference width alignment bytes bound loaded
    exact ⟨kept, secondPrivate reference width alignment bytes bound kept⟩

#print axioms output_halves_update
#print axioms CallingConditions.output_half_address
#print axioms output_half_update
end UInt256Model.Safety
