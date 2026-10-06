import UInt256.Methods.Multiply.FullSafetyTopContract
import UInt256.Methods.Multiply.VectorProducts
import UInt256.Safety.PrivateVectorStore
import UInt256.Safety.HalfRepresentation

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem input_vector_snapshot {original entered current : Memory} {inputs outputs : List Reference}
    {frame : Frame} {known : Nat → Option (BitVec 64)}
    (state : PrivateWords Extracted.program original entered current inputs outputs frame known)
    (originalCall : CallingConditions Extracted.program original inputs outputs)
    (input : Reference) (member : input ∈ inputs) :
    loadValue current (.address input) 32 = .ok (.v256 (CIL.Vector.pack256
      (inputLimb original input 0) (inputLimb original input 1)
      (inputLimb original input 2) (inputLimb original input 3))) := by
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (originalCall.input_formed member)
  have bound := (originalCall.1.1.1 _ _ present).1
  have bytes : (fun offset => (current.cells input.allocation offset).bits) =
      (fun offset => (original.cells input.allocation offset).bits) := by
    funext offset
    rw [state.caller input.allocation bound offset]
  rw [state.call.input_load member, pack_limbs_value, input_limbs_value]
  simp only [inputValue, bytes]

#print axioms input_vector_snapshot
end UInt256Proof.Multiply.Safety
