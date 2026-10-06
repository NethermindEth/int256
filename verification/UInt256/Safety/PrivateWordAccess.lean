import UInt256.Safety.PrivateWords

namespace UInt256Model.Safety
open CIL.Safety

theorem PrivateWords.input_field {program : CIL.Program} {original entered current : Memory}
    {inputs outputs : List Reference} {frame : Frame} {known : Nat → Option (BitVec 64)}
    (state : PrivateWords program original entered current inputs outputs frame known)
    (originalCall : CallingConditions program original inputs outputs)
    (input : Reference) (member : input ∈ inputs) (index : Fin 4) (rest : List Value) :
    instruction (.field index) (.reference (.address input) :: rest) current =
      .ok (current, .scalar (.i64 (inputLimb original input index)) :: rest) := by
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (originalCall.input_formed member)
  have bound := (originalCall.1.1.1 _ _ present).1
  have bytes : (fun offset => (current.cells input.allocation offset).bits) =
      (fun offset => (original.cells input.allocation offset).bits) := by
    funext offset
    rw [state.caller input.allocation bound offset]
  rw [state.call.input_field_instruction member]
  simp only [inputLimb, bytes]

theorem PrivateWords.home {program : CIL.Program} {original entered current : Memory}
    {inputs outputs : List Reference} {frame : Frame} {known : Nat → Option (BitVec 64)}
    {kinds : List CIL.LocalKind}
    (state : PrivateWords program original entered current inputs outputs frame known)
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity kinds frame.locals)
    (index : Nat) (specified : kinds[index]? = some .word64) :
    ∃ reference, frame.locals[index]? = some (.bytes .word64 reference) ∧
      access current reference 8 1 true = .ok () ∧ form current reference = .ok reference := by
  obtain ⟨reference, slot, _, ready⟩ := homes.home_at index .word64 specified
  obtain ⟨allocation, requirements⟩ := access_requirements ready
  have writable := state.authority.access ready (enteredWF.1 _ _ requirements.present).1
  exact ⟨reference, slot, writable, access_reference_valid _ _ _ _ _ writable⟩

#print axioms PrivateWords.input_field
#print axioms PrivateWords.home
end UInt256Model.Safety
