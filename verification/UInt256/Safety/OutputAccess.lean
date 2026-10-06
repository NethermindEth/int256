import CIL.Safety.WriteEffects
import UInt256.Safety.Calling

namespace UInt256Model.Safety

open CIL.Safety

/-- The allocation and the API output footprint are separate. -/
def OutsideOutput (output : Reference) (id offset : Nat) : Prop :=
  id ≠ output.allocation ∨ offset < output.offset ∨ output.offset + 32 ≤ offset

/-- A checked write preserves input readability and output authority, even
    with overlap. It may change input values; no initial-value equality follows. -/
theorem CallingConditions.after_write {program : CIL.Program}
    {memory result : CIL.Safety.Memory} {inputs outputs : List Reference}
    {reference : Reference} {bytes : List (BitVec 8)} {alignment : Nat}
    (call : CallingConditions program memory inputs outputs)
    (written : write memory reference bytes alignment = .ok result) :
    CallingConditions program result inputs outputs := by
  refine ⟨⟨write_preserves_wellFormed _ _ _ _ _ call.1.1 written, ?_, ?_⟩,
    write_preserves_static_world _ _ _ _ _ _ call.2 written⟩
  · intro input member
    obtain ⟨old, readable⟩ := call.1.2.1 input member
    exact write_preserves_readability written readable
  · intro output member
    obtain ⟨allocation, ready⟩ := access_requirements (call.1.2.2 output member)
    exact (ready.after_write written).access

theorem CallingConditions.output_limb_address {program : CIL.Program}
    {memory : CIL.Safety.Memory} {inputs outputs : List Reference}
    (call : CallingConditions program memory inputs outputs) {output : Reference}
    (member : output ∈ outputs) (index : Fin 4) :
    add memory output 8 (BitVec.ofNat 64 index.val) =
      .ok { output with offset := output.offset + 8 * index.val } := by
  obtain ⟨allocation, ready⟩ := access_requirements
    (call.1.2.2 (wordView output) (List.mem_map.mpr ⟨output, member, rfl⟩))
  dsimp only [wordView] at ready
  exact ready.add_slice call.1.1 8 index.val 8 (by decide) (by omega)

theorem CallingConditions.output_limb_formed {program : CIL.Program}
    {memory : CIL.Safety.Memory} {inputs outputs : List Reference}
    (call : CallingConditions program memory inputs outputs) {output : Reference}
    (member : output ∈ outputs) (index : Fin 4) :
    form memory { output with offset := output.offset + 8 * index.val } =
      .ok { output with offset := output.offset + 8 * index.val } := by
  obtain ⟨allocation, ready⟩ := access_requirements
    (call.1.2.2 (wordView output) (List.mem_map.mpr ⟨output, member, rfl⟩))
  dsimp only [wordView] at ready
  exact access_reference_valid _ _ _ _ _
    (ready.slice call.1.1 (8 * index.val) 8 (by decide) (by omega)).access

theorem CallingConditions.write_output_slice {program : CIL.Program}
    {memory : CIL.Safety.Memory} {inputs outputs : List Reference}
    (call : CallingConditions program memory inputs outputs) {output : Reference}
    (member : output ∈ outputs) (start : Nat) (bytes : List (BitVec 8))
    (nonempty : 0 < bytes.length) (within : start + bytes.length ≤ 32) :
    ∃ result,
      write memory { output with offset := output.offset + start } bytes 1 = .ok result ∧
      CallingConditions program result inputs outputs ∧
      (∀ id offset, OutsideOutput output id offset → result.cells id offset = memory.cells id offset) ∧
      read result { output with offset := output.offset + start } bytes.length 1 = .ok bytes := by
  obtain ⟨allocation, ready⟩ := access_requirements
    (call.1.2.2 (wordView output) (List.mem_map.mpr ⟨output, member, rfl⟩))
  dsimp only [wordView] at ready
  obtain ⟨result, written⟩ := write_succeeds (ready.slice call.1.1 start bytes.length nonempty within).access
  refine ⟨result, written, call.after_write written, ?_, write_readback _ _ _ _ _ written⟩
  intro id offset outside
  apply write_outside _ _ _ _ _ _ _ written
  dsimp only
  unfold OutsideOutput at outside
  omega

theorem CallingConditions.output_field_instruction {program : CIL.Program}
    {memory : CIL.Safety.Memory} {inputs outputs : List Reference}
    (call : CallingConditions program memory inputs outputs) {output : Reference}
    (member : output ∈ outputs) (index : Fin 4) (value : BitVec 64) (rest : List CIL.Safety.Value) :
    ∃ result,
      instruction (.setField index) (.scalar (.i64 value) :: .reference (.address output) :: rest) memory =
        .ok (result, rest) ∧
      CallingConditions program result inputs outputs ∧
      (∀ id offset, OutsideOutput output id offset → result.cells id offset = memory.cells id offset) ∧
      read result { output with offset := output.offset + 8 * index.val } 8 1 =
        .ok (numberBytes value.toNat 8) := by
  have length : (numberBytes value.toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨result, written, retained, outside, readback⟩ :=
    call.write_output_slice member (8 * index.val) (numberBytes value.toNat 8)
      (by rw [length]; decide) (by rw [length]; omega)
  refine ⟨result, ?_, retained, outside, ?_⟩
  · simp [instruction, call.output_limb_address member index, storeValue, referenceAt, written,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · simpa only [length] using readback

#print axioms CallingConditions.after_write
#print axioms CallingConditions.output_limb_address
#print axioms CallingConditions.write_output_slice
#print axioms CallingConditions.output_field_instruction

end UInt256Model.Safety
