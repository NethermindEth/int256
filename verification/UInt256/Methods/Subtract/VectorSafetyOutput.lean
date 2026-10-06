import UInt256.Methods.Subtract.VectorSafetyBorrow
import UInt256.Methods.AddSubtract.VectorOutput

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- The first output write may overlap either input. Saved private values remain
    readable, and only the caller's output bytes change. -/
theorem vector_early_output_checked (original entered current : Memory)
    (inputs outputs : List Reference) (output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (outputMember : output ∈ outputs)
    (authority : AccessBelow entered.nextIdentity entered current)
    (outputArgument : args[2]? = some (.reference (.address output)))
    (differenceHome incomingHome : Reference) (difference incoming : BitVec 256)
    (differenceSlot : frame.locals[2]? = some (.bytes .vector256 differenceHome))
    (incomingSlot : frame.locals[4]? = some (.bytes .vector256 incomingHome))
    (differenceRead : read current differenceHome 32 1 = .ok (numberBytes difference.toNat 32))
    (incomingRead : read current incomingHome 32 1 = .ok (numberBytes incoming.toNat 32))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      read after output 32 1 = .ok (numberBytes (CIL.Vector.zip256 (· + ·) difference incoming).toNat 32) →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = current.cells id offset) →
      (∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
        read current reference width alignment = .ok bytes → read after reference width alignment = .ok bytes) →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vectorIndex (vectorOutputStart + 8) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex vectorOutputStart args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have formed := currentCall.output_formed outputMember
  conv in vectorOutputStart => cbv
  iterate 2
    apply run_next_exists post found (by rfl)
    · simp [step, outputArgument, checkedValue, formValue, formed, checkedAt,
        instruction, staticInstruction, memoryInstruction, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  exact vector_output_checked original entered current inputs outputs output frame args
    call currentCall outputMember authority outputArgument (vectorOutputStart + 2) 2 4
    (.vector (.add64 256)) (CIL.Vector.zip256 (· + ·) difference incoming) (by rfl)
    differenceHome incomingHome difference incoming differenceSlot incomingSlot differenceRead incomingRead
    (by simp [CIL.Vector.intrinsic_add256]) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    post continuation

#print axioms vector_early_output_checked
end UInt256Proof.Subtract.Safety
