import UInt256.Methods.Add.VectorSafetyCarry

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def incomingCarry (mask : BitVec 256) : BitVec 256 :=
  CIL.Vector.blend32 (CIL.Vector.permute4x64 mask (BitVec.ofNat 8 144))
    (BitVec.ofNat 256 0) (BitVec.ofNat 8 3)

theorem incomingCarry_packed (a b c d : BitVec 64) :
    incomingCarry (CIL.Vector.pack256 a b c d) = CIL.Vector.pack256 0 a b c := by
  change CIL.Vector.blend32 (CIL.Vector.permute4x64 (CIL.Vector.pack256 a b c d) 144) 0 3 = _
  rw [CIL.Vector.avx2_permute_incoming, CIL.Vector.avx2_blend_incoming]

theorem incomingCarry_align (mask : BitVec 256) :
    CIL.Vector.alignRight64 mask (BitVec.ofNat 256 0) 3 = incomingCarry mask := by
  have aligned : CIL.Vector.alignRight64 mask 0 3 = incomingCarry mask := by
    conv in mask => rw [← CIL.Vector.pack256_lanes mask]
    rw [CIL.Vector.avx512_incoming]
    rw [← CIL.Vector.pack256_lanes mask, incomingCarry_packed]
    simp only [CIL.Vector.pack256_lanes]
  exact aligned

#print axioms incomingCarry_align

/-- Shift the initialized carry mask by one lane, clear the low lane and store
    through the helper's incoming-carry argument. -/
theorem vector_incoming_checked (original entered current : Memory)
    (inputs outputs : List Reference) (mask incoming : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (maskMember : mask ∈ outputs) (incomingMember : incoming ∈ outputs)
    (authority : AccessBelow entered.nextIdentity entered current)
    (maskArgument : args[4]? = some (.reference (.address mask)))
    (incomingArgument : args[5]? = some (.reference (.address incoming)))
    (maskValue : BitVec 256)
    (maskRead : read current mask 32 1 = .ok (numberBytes maskValue.toNat 32))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      write current incoming (numberBytes (incomingCarry maskValue).toNat 32) 1 = .ok after →
      read after incoming 32 1 = .ok (numberBytes (incomingCarry maskValue).toNat 32) →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, OutsideOutput incoming id offset → after.cells id offset = current.cells id offset) →
      (∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
        read current reference width alignment = .ok bytes → read after reference width alignment = .ok bytes) →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vectorIndex vectorOutputStart args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex vectorIncomingStart args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨after, written, readback, afterCall, afterAuthority, outside, privateReads, advanced⟩ :=
    vector_output_update original entered current inputs outputs incoming (incomingCarry maskValue)
      call currentCall incomingMember authority
  have done := continuation after written readback afterCall afterAuthority outside privateReads advanced
  have alignedWritten := written
  rw [← incomingCarry_align] at alignedWritten
  simp only [incomingCarry] at written
  have maskFormed := currentCall.output_formed maskMember
  have incomingFormed := currentCall.output_formed incomingMember
  have reading := vector_load_snapshot current mask maskValue maskRead
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have profile : vectorBody.profile = Extracted.profile := by rfl
  conv at done in vectorOutputStart => cbv
  conv in vectorIncomingStart => cbv
  repeat' first
    | exact done
    | (apply run_next_exists post found (by rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, profile, cil_code, maskArgument, incomingArgument, maskFormed, incomingFormed, reading,
           pureArity, scalars, CIL.step, CIL.Intrinsic.available, incomingCarry,
           CIL.Vector.intrinsic_permute256, CIL.Vector.intrinsic_reinterpret256,
           CIL.Vector.intrinsic_zero256, CIL.Vector.intrinsic_blend256,
           CIL.Vector.intrinsic_align256, alignedWritten,
           checkedValue, numericValue, formValue, staticInstruction, memoryInstruction,
           storeValue, referenceAt, written, checkedAt, Except.mapError,
           Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

#print axioms incomingCarry_packed
#print axioms vector_incoming_checked
end UInt256Proof.Add.Safety
