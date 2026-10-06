import UInt256.Methods.Add.VectorSafetyPrepared

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Execute SkipInit and the first caller-output store from initialized private
    sum and incoming-carry snapshots, without rereading either original input. -/
theorem vector_early_output_checked (original entered current : Memory)
    (inputs outputs : List Reference) (output sum incoming : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (outputMember : output ∈ outputs) (sumMember : sum ∈ outputs) (incomingMember : incoming ∈ outputs)
    (authority : AccessBelow entered.nextIdentity entered current)
    (outputArgument : args[2]? = some (.reference (.address output)))
    (sumArgument : args[3]? = some (.reference (.address sum)))
    (incomingArgument : args[5]? = some (.reference (.address incoming)))
    (sumValue incomingValue : BitVec 256)
    (sumRead : read current sum 32 1 = .ok (numberBytes sumValue.toNat 32))
    (incomingRead : read current incoming 32 1 = .ok (numberBytes incomingValue.toNat 32))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      write current output (numberBytes (CIL.Vector.zip256 (· - ·) sumValue incomingValue).toNat 32) 1 = .ok after →
      read after output 32 1 = .ok (numberBytes (CIL.Vector.zip256 (· - ·) sumValue incomingValue).toNat 32) →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = current.cells id offset) →
      (∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
        read current reference width alignment = .ok bytes → read after reference width alignment = .ok bytes) →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vectorIndex (vectorOutputStart + 10) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex vectorOutputStart args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨after, written, readback, afterCall, afterAuthority, outside, privateReads, advanced⟩ :=
    vector_output_update original entered current inputs outputs output
      (CIL.Vector.zip256 (· - ·) sumValue incomingValue) call currentCall outputMember authority
  have done := continuation after written readback afterCall afterAuthority outside privateReads advanced
  have outputFormed := currentCall.output_formed outputMember
  have sumFormed := currentCall.output_formed sumMember
  have incomingFormed := currentCall.output_formed incomingMember
  have loadSum := vector_load_snapshot current sum sumValue sumRead
  have loadIncoming := vector_load_snapshot current incoming incomingValue incomingRead
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have profile : vectorBody.profile = Extracted.profile := by rfl
  conv at done in vectorOutputStart => cbv
  conv in vectorOutputStart => cbv
  repeat' first
    | exact done
    | (apply run_next_exists post found (by rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, profile, cil_code, outputArgument, sumArgument, incomingArgument,
           outputFormed, sumFormed, incomingFormed, loadSum, loadIncoming,
           pureArity, scalars, CIL.step, CIL.Intrinsic.available, CIL.Vector.intrinsic_sub256,
           checkedValue, numericValue, formValue, instruction, staticInstruction, memoryInstruction,
           storeValue, referenceAt, written, checkedAt, Except.mapError,
           Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

#print axioms vector_early_output_checked
end UInt256Proof.Add.Safety
