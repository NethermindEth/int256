import CIL.Safety.AccessSlices
import UInt256.Safety.Calling

namespace UInt256Model.Safety

open CIL.Safety

def inputHalf (memory : CIL.Safety.Memory) (reference : Reference) (index : Fin 2) : BitVec 128 :=
  BitVec.ofNat 128 (UInt256Model.byteNumber
    (fun offset => (memory.cells reference.allocation offset).bits) (reference.offset + 16 * index.val) 16)

theorem CallingConditions.input_half_address {program : CIL.Program}
    {memory : CIL.Safety.Memory} {inputs outputs : List Reference}
    (call : CallingConditions program memory inputs outputs) {reference : Reference}
    (member : reference ∈ inputs) (index : Fin 2) :
    add memory reference 16 (BitVec.ofNat 64 index.val) =
      .ok { reference with offset := reference.offset + 16 * index.val } := by
  have loaded := call.input_snapshot member
  have readable : access memory reference 32 1 false = .ok () := by
    unfold CIL.Safety.read at loaded
    cases h : access memory reference 32 1 false with
    | error fault => simp [h, Bind.bind, Except.bind] at loaded
    | ok value => cases value; rfl
  obtain ⟨allocation, ready⟩ := access_requirements readable
  exact ready.add_slice call.1.1 16 index.val 16 (by decide) (by omega)

theorem CallingConditions.input_half_load {program : CIL.Program}
    {memory : CIL.Safety.Memory} {inputs outputs : List Reference}
    (call : CallingConditions program memory inputs outputs) {reference : Reference}
    (member : reference ∈ inputs) (index : Fin 2) :
    loadValue memory (.address { reference with offset := reference.offset + 16 * index.val }) 16 =
      .ok (.v128 (inputHalf memory reference index)) := by
  have loaded := read_slice call.1.1 (call.input_snapshot member) (16 * index.val) 16 (by decide) (by omega)
  simp only [loadValue, dereference, loaded, checkedAt, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [byteNumber_snapshot (fun offset => (memory.cells reference.allocation offset).bits)
    (reference.offset + 16 * index.val) 16]
  rfl

theorem CallingConditions.input_half_formed {program : CIL.Program}
    {memory : CIL.Safety.Memory} {inputs outputs : List Reference}
    (call : CallingConditions program memory inputs outputs) {reference : Reference}
    (member : reference ∈ inputs) (index : Fin 2) :
    form memory { reference with offset := reference.offset + 16 * index.val } =
      .ok { reference with offset := reference.offset + 16 * index.val } := by
  exact read_reference_valid _ _ _ _ _
    (read_slice call.1.1 (call.input_snapshot member) (16 * index.val) 16 (by decide) (by omega))

#print axioms CallingConditions.input_half_address
#print axioms CallingConditions.input_half_load
#print axioms CallingConditions.input_half_formed

end UInt256Model.Safety
