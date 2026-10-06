import UInt256.Methods.AddSubtract.VectorStore

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety

/-- Execute a fetched vector binary operation and caller-output store, preserving
    all private snapshots even when the output overlaps the original inputs. -/
theorem vector_output_checked (original entered current : Memory)
    (inputs outputs : List Reference) (output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (outputMember : output ∈ outputs)
    (authority : AccessBelow entered.nextIdentity entered current)
    (outputArgument : args[2]? = some (.reference (.address output)))
    (pc leftIndex rightIndex : Nat) (operation : CIL.Intrinsic) (value : BitVec 256)
    (available : operation.available vectorBody.profile = true)
    (differenceHome incomingHome : Reference) (difference incoming : BitVec 256)
    (differenceSlot : frame.locals[leftIndex]? = some (.bytes .vector256 differenceHome))
    (incomingSlot : frame.locals[rightIndex]? = some (.bytes .vector256 incomingHome))
    (differenceRead : read current differenceHome 32 1 = .ok (numberBytes difference.toNat 32))
    (incomingRead : read current incomingHome 32 1 = .ok (numberBytes incoming.toNat 32))
    (evaluated : CIL.evalIntrinsic operation [.v256 difference, .v256 incoming] = some (.v256 value))
    (fetchOutput : vectorBody.code[pc]? = some (.arg 2))
    (fetchRef : vectorBody.code[pc + 1]? = some (.memory .asRef))
    (fetchLeft : vectorBody.code[pc + 2]? = some (.local leftIndex))
    (fetchRight : vectorBody.code[pc + 3]? = some (.local rightIndex))
    (fetchOperation : vectorBody.code[pc + 4]? = some (.intrinsic operation 2))
    (fetchStore : vectorBody.code[pc + 5]? = some (.memory .store256))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      read after output 32 1 = .ok (numberBytes value.toNat 32) →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = current.cells id offset) →
      (∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
        read current reference width alignment = .ok bytes → read after reference width alignment = .ok bytes) →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vectorIndex (pc + 6) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex pc args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have formed := currentCall.output_formed outputMember
  apply run_next_exists (target := pc + 1) (values := [.reference (.address output)])
    (nextFrame := frame) (updated := current) post found fetchOutput
  · simp [step, outputArgument, checkedValue, formValue, formed, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  · apply run_next_exists (target := pc + 2) (values := [.reference (.address output)])
      (nextFrame := frame) (updated := current) post found fetchRef
    · simp [step, staticInstruction, memoryInstruction, referenceAt, formValue, formed,
        checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · exact vector_store_checked original entered current inputs outputs output frame args
        call currentCall outputMember authority (pc + 2) leftIndex rightIndex operation value available
        differenceHome incomingHome difference incoming differenceSlot incomingSlot differenceRead incomingRead
        evaluated fetchLeft fetchRight fetchOperation fetchStore post continuation

#print axioms vector_output_checked
end UInt256Proof.AddSubtract.Safety
