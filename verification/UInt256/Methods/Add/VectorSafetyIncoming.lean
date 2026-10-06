import UInt256.Methods.Add.VectorSafetyPrefix
import CIL.SIMD.Evaluation256Lemmas
import UInt256.Arithmetic.SignMasks

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def generatedCarry (a b : BitVec 256) : BitVec 256 :=
  CIL.Vector.zip256 (fun sum left => CIL.Vector.mask64 (sum.ult left))
    (CIL.Vector.zip256 (· + ·) a b) a

theorem generatedCarry_ternary (a b : BitVec 256) :
    CIL.Vector.map256 (fun x => x.sshiftRight 63)
      (CIL.Vector.ternaryLogic a b (CIL.Vector.zip256 (· + ·) a b) (BitVec.ofNat 8 212)) =
    generatedCarry a b := by
  conv in a => rw [← CIL.Vector.pack256_lanes a]
  conv in b => rw [← CIL.Vector.pack256_lanes b]
  simp only [generatedCarry, CIL.Vector.zip256]
  rw [UInt256Proof.SIMD.ternary_carry_packed_normal]
  simp only [CIL.Vector.lane256_0, CIL.Vector.lane256_1, CIL.Vector.lane256_2, CIL.Vector.lane256_3]

#print axioms generatedCarry_ternary

def vectorCarryStart : Nat := if Extracted.profile.avx512FVL then
  (vectorBody.code.findIdx fun op => match op with
    | .intrinsic (.avx512 .ternaryLogic) 4 => true | _ => false) - 6
else (vectorBody.code.findIdx fun op =>
  match op with | .intrinsic (.vector (.ltu64 256)) 2 => true | _ => false) - 4

def vectorIncomingStart : Nat := vectorCarryStart + if Extracted.profile.avx512FVL then 12 else 6

def vectorOutputStart : Nat := (vectorBody.code.findIdx fun op =>
  match op with | .skipInit => true | _ => false) - 1

/-- Follow the extracted feature guard to the selected carry computation. -/
theorem vector_carry_dispatch (memory : Memory) (frame : Frame) (args : List Value)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel vectorIndex vectorCarryStart args frame [] memory =
        .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex (vectorOperandStart + 13) args frame [] memory =
        .ok (result, returned) ∧ post result returned := by
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have profile : vectorBody.profile = Extracted.profile := by rfl
  conv at continuation in vectorCarryStart => cbv
  conv in vectorOperandStart => cbv
  repeat' first
    | exact continuation
    | (apply run_next_exists post found (by rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.FeatureProfile.evaluate,
           checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

#print axioms vector_carry_dispatch

/-- Load the initialized sum argument, compare it with the saved initial left
    operand, and write the generated carry mask through the actual byref argument. -/
theorem vector_carry_checked (original entered current : Memory)
    (inputs outputs : List Reference) (sum mask : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (sumMember : sum ∈ outputs) (maskMember : mask ∈ outputs)
    (authority : AccessBelow entered.nextIdentity entered current)
    (sumArgument : args[3]? = some (.reference (.address sum)))
    (maskArgument : args[4]? = some (.reference (.address mask)))
    (leftHome rightHome : Reference) (a b : BitVec 256)
    (leftSlot : frame.locals[0]? = some (.bytes .vector256 leftHome))
    (rightSlot : frame.locals[1]? = some (.bytes .vector256 rightHome))
    (rightRead : read current rightHome 32 1 = .ok (numberBytes b.toNat 32))
    (leftRead : read current leftHome 32 1 = .ok (numberBytes a.toNat 32))
    (sumRead : read current sum 32 1 = .ok (numberBytes (CIL.Vector.zip256 (· + ·) a b).toNat 32))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      write current mask (numberBytes (generatedCarry a b).toNat 32) 1 = .ok after →
      read after mask 32 1 = .ok (numberBytes (generatedCarry a b).toNat 32) →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, OutsideOutput mask id offset → after.cells id offset = current.cells id offset) →
      (∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
        read current reference width alignment = .ok bytes → read after reference width alignment = .ok bytes) →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vectorIndex vectorIncomingStart args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex vectorCarryStart args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨after, written, readback, afterCall, afterAuthority, outside, privateReads, advanced⟩ :=
    vector_output_update original entered current inputs outputs mask (generatedCarry a b)
      call currentCall maskMember authority
  have done := continuation after written readback afterCall afterAuthority outside privateReads advanced
  have ternaryWritten := written
  rw [← generatedCarry_ternary] at ternaryWritten
  simp only [generatedCarry] at written
  have maskFormed := currentCall.output_formed maskMember
  have sumFormed := currentCall.output_formed sumMember
  have reading := vector_load_snapshot current sum (CIL.Vector.zip256 (· + ·) a b) sumRead
  have loadLeft := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vectorBody) (args := args) (pc := pc) (stack := stack)
    .vector256 (.v256 a) a.toNat rfl leftSlot leftRead
  have loadRight := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vectorBody) (args := args) (pc := pc) (stack := stack)
    .vector256 (.v256 b) b.toNat rfl rightSlot rightRead
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have profile : vectorBody.profile = Extracted.profile := by rfl
  conv at done in vectorIncomingStart => cbv
  conv in vectorCarryStart => cbv
  repeat' first
    | exact done
    | (apply run_next_exists post found (by rfl)
       first
       | exact loadLeft _ _
       | exact loadRight _ _
       | (simp (config := { implicitDefEqProofs := false })
           [step, profile, cil_code, sumArgument, maskArgument, maskFormed, sumFormed, reading,
             pureArity, scalars, CIL.step, CIL.Intrinsic.available, generatedCarry,
             checkedValue, numericValue, formValue, staticInstruction, memoryInstruction,
             CIL.Vector.intrinsic_lt256, CIL.Vector.intrinsic_ternary_add256,
             CIL.Vector.intrinsic_sign256, CIL.Vector.intrinsic_reinterpret256, ternaryWritten, storeValue, referenceAt, written, checkedAt,
             Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector_carry_checked
end UInt256Proof.Add.Safety

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
