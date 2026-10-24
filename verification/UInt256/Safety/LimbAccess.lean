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
    add memory reference 1 (BitVec.ofNat 64 (8 * index.val)) =
      .ok { reference with offset := reference.offset + 8 * index.val } := by
  obtain ⟨allocation, ready⟩ := access_requirements (read_access (call.input_snapshot member))
  simpa only [Nat.one_mul] using
    ready.add_slice call.1.1 1 (8 * index.val) 8 (by decide) (by omega)

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
    instruction (.fieldAt (8 * index.val) 8) (.reference (.address reference) :: rest) memory =
      .ok (memory, .scalar (.i64 (inputLimb memory reference index)) :: rest) := by
  show (checkedAt (.address reference) 0 (add memory reference 1 (BitVec.ofNat 64 (8 * index.val))) >>=
      fun address => loadValue memory (.address address) 8 false >>=
        fun value => pure (memory, .scalar value :: rest)) = _
  simp only [checkedAt, call.input_limb_address member index, Except.mapError, Bind.bind,
    Except.bind, call.input_limb_load member index, Pure.pure, Except.pure]

#print axioms CallingConditions.input_limb_address
#print axioms CallingConditions.input_limb_load
#print axioms CallingConditions.input_field_instruction

end UInt256Model.Safety
