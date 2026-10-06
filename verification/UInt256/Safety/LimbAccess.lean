import CIL.Safety.AccessSlices
import UInt256.Safety.Calling

namespace UInt256Model.Safety

open CIL.Safety

def inputLimb (memory : CIL.Safety.Memory) (reference : Reference) (index : Fin 4) : BitVec 64 :=
  BitVec.ofNat 64 (UInt256Model.byteNumber
    (fun offset => (memory.cells reference.allocation offset).bits) (reference.offset + 8 * index.val) 8)

theorem CallingConditions.input_limb_address {program : CIL.Program}
    {memory : CIL.Safety.Memory} {inputs outputs : List Reference}
    (call : CallingConditions program memory inputs outputs) {reference : Reference}
    (member : reference ∈ inputs) (index : Fin 4) :
    add memory reference 8 (BitVec.ofNat 64 index.val) =
      .ok { reference with offset := reference.offset + 8 * index.val } := by
  have loaded := call.input_snapshot member
  have readable : access memory reference 32 1 false = .ok () := by
    unfold CIL.Safety.read at loaded
    cases h : access memory reference 32 1 false with
    | error fault => simp [h, Bind.bind, Except.bind] at loaded
    | ok value => cases value; rfl
  obtain ⟨allocation, ready⟩ := access_requirements readable
  exact ready.add_slice call.1.1 8 index.val 8 (by decide) (by omega)

theorem CallingConditions.input_limb_load {program : CIL.Program}
    {memory : CIL.Safety.Memory} {inputs outputs : List Reference}
    (call : CallingConditions program memory inputs outputs) {reference : Reference}
    (member : reference ∈ inputs) (index : Fin 4) :
    loadValue memory (.address { reference with offset := reference.offset + 8 * index.val }) 8 =
      .ok (.i64 (inputLimb memory reference index)) := by
  have loaded := read_slice call.1.1 (call.input_snapshot member) (8 * index.val) 8 (by decide) (by omega)
  simp only [loadValue, dereference, loaded, checkedAt, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [byteNumber_snapshot (fun offset => (memory.cells reference.allocation offset).bits)
    (reference.offset + 8 * index.val) 8]
  rfl

/-- The actual field instruction checks the intermediate address before loading
    its eight bytes. The rest of the stack and caller memory are unchanged. -/
theorem CallingConditions.input_field_instruction {program : CIL.Program}
    {memory : CIL.Safety.Memory} {inputs outputs : List Reference}
    (call : CallingConditions program memory inputs outputs) {reference : Reference}
    (member : reference ∈ inputs) (index : Fin 4) (rest : List CIL.Safety.Value) :
    instruction (.field index) (.reference (.address reference) :: rest) memory =
      .ok (memory, .scalar (.i64 (inputLimb memory reference index)) :: rest) := by
  simp [instruction, call.input_limb_address member index, call.input_limb_load member index,
    checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms CallingConditions.input_limb_address
#print axioms CallingConditions.input_limb_load
#print axioms CallingConditions.input_field_instruction

end UInt256Model.Safety
