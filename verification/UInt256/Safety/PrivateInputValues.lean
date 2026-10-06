import UInt256.Safety.PrivateWordAccess

namespace UInt256Model.Safety
open CIL.Safety

theorem PrivateWords.input_bytes {program : CIL.Program} {original entered current : Memory}
    {inputs outputs : List Reference} {frame : Frame} {known : Nat → Option (BitVec 64)}
    (state : PrivateWords program original entered current inputs outputs frame known)
    (originalCall : CallingConditions program original inputs outputs)
    (input : Reference) (member : input ∈ inputs) :
    (fun offset => (current.cells input.allocation offset).bits) =
      (fun offset => (original.cells input.allocation offset).bits) := by
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (originalCall.input_formed member)
  have bound := (originalCall.1.1.1 _ _ present).1
  funext offset
  rw [state.caller input.allocation bound offset]

theorem PrivateWords.input_value {program : CIL.Program} {original entered current : Memory}
    {inputs outputs : List Reference} {frame : Frame} {known : Nat → Option (BitVec 64)}
    (state : PrivateWords program original entered current inputs outputs frame known)
    (originalCall : CallingConditions program original inputs outputs)
    (input : Reference) (member : input ∈ inputs) : inputValue current input = inputValue original input := by
  simp only [inputValue, state.input_bytes originalCall input member]

theorem PrivateWords.input_limb {program : CIL.Program} {original entered current : Memory}
    {inputs outputs : List Reference} {frame : Frame} {known : Nat → Option (BitVec 64)}
    (state : PrivateWords program original entered current inputs outputs frame known)
    (originalCall : CallingConditions program original inputs outputs)
    (input : Reference) (member : input ∈ inputs) (index : Fin 4) :
    inputLimb current input index = inputLimb original input index := by
  simp only [inputLimb, state.input_bytes originalCall input member]

#print axioms PrivateWords.input_value
#print axioms PrivateWords.input_limb
end UInt256Model.Safety
