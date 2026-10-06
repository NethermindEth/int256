import UInt256.Methods.Subtract.VectorSafetyLookup
import UInt256.Methods.AddSubtract.VectorOutput

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- The correction store uses saved lane differences and the checked lookup vector. -/
theorem vector_correction_output_checked (original entered current : Memory)
    (inputs outputs : List Reference) (output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (outputMember : output ∈ outputs)
    (authority : AccessBelow entered.nextIdentity entered current)
    (outputArgument : args[2]? = some (.reference (.address output)))
    (differenceHome correctionHome : Reference) (difference correction : BitVec 256)
    (differenceSlot : frame.locals[2]? = some (.bytes .vector256 differenceHome))
    (correctionSlot : frame.locals[8]? = some (.bytes .vector256 correctionHome))
    (differenceRead : read current differenceHome 32 1 = .ok (numberBytes difference.toNat 32))
    (correctionRead : read current correctionHome 32 1 = .ok (numberBytes correction.toNat 32))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      read after output 32 1 = .ok (numberBytes (CIL.Vector.zip256 (· - ·) difference correction).toNat 32) →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = current.cells id offset) →
      (∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
        read current reference width alignment = .ok bytes → read after reference width alignment = .ok bytes) →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vectorIndex (vectorTestStart + 40) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex (vectorTestStart + 34) args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  exact vector_output_checked original entered current inputs outputs output frame args
    call currentCall outputMember authority outputArgument (vectorTestStart + 34) 2 8
    (.vector (.sub64 256)) (CIL.Vector.zip256 (· - ·) difference correction) (by rfl)
    differenceHome correctionHome difference correction differenceSlot correctionSlot differenceRead correctionRead
    (by simp [CIL.Vector.intrinsic_sub256]) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    post continuation

#print axioms vector_correction_output_checked
def vectorCascadeFuel : Nat := if Extracted.profile.bmi1 then 9 else 8

/-- Execute the selected profile's cascade-flag suffix and expire its frame.
    The sum is read from its initialized numeric home after the output write. -/
theorem vector_cascade_return (memory : Memory) (frame : Frame) (args : List Value)
    (sumHome : Reference) (sum : BitVec 32)
    (slot : frame.locals[6]? = some (.bytes .word32 sumHome))
    (loaded : read memory sumHome 4 1 = .ok (numberBytes sum.toNat 4)) :
    run Extracted.program vectorCascadeFuel vectorIndex (vectorTestStart + 40) args frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (if sum &&& 16 > 0 then 1 else 0))]) := by
  have loadSum := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vectorBody) (args := args) (pc := pc) (stack := stack)
    .word32 (.i32 sum) sum.toNat rfl slot loaded
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have profile : vectorBody.profile = Extracted.profile := by rfl
  have returns : vectorBody.returnsValue = true := by rfl
  conv in vectorTestStart => cbv
  first
  | (have disabled : Extracted.profile.bmi1 = false := by rfl
     simp only [vectorCascadeFuel, disabled, Bool.false_eq_true, ite_false]
     iterate 7
       apply Eq.trans
       · apply run_next found (by rfl)
         first
         | exact loadSum _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, profile, cil_code, CIL.FeatureProfile.evaluate, pureArity, scalars, CIL.step, CIL.binary,
               checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)
     have fetched : vectorBody.code[vectorTestStart + 47]? = some .ret := by rfl
     conv at fetched in vectorTestStart => cbv
     simp [run, found, fetched, returns, step, checkedValue, numericValue,
       Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    )
  | (have enabled : Extracted.profile.bmi1 = true := by rfl
     simp only [vectorCascadeFuel, enabled, ite_true]
     have extracted : CIL.Vector.bextr32 sum 4 1 =
         if sum.getLsbD 4 then BitVec.ofNat 32 1 else BitVec.ofNat 32 0 :=
       CIL.Vector.bextr_flag_value sum
     have masked : sum &&& BitVec.ofNat 32 16 =
         if sum.getLsbD 4 then BitVec.ofNat 32 16 else BitVec.ofNat 32 0 :=
       CIL.Vector.bit4_mask_value sum
     cases bit : sum[4]
     all_goals
       iterate 8
         apply Eq.trans
         · apply run_next found (by rfl)
           first
           | exact loadSum _ _
           | (simp (config := { implicitDefEqProofs := false })
               [step, profile, cil_code, CIL.FeatureProfile.evaluate, pureArity, scalars,
                 CIL.step, CIL.Intrinsic.available, CIL.Vector.intrinsic_bextr_flag,
                 extracted, bit, staticInstruction, memoryInstruction,
                 checkedValue, numericValue, checkedAt, Except.mapError,
                 Bind.bind, Except.bind, Pure.pure, Except.pure]
              first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)
       have fetched : vectorBody.code[vectorTestStart + 54]? = some .ret := by rfl
       conv at fetched in vectorTestStart => cbv
       simp [run, found, fetched, returns, step, masked, bit, checkedValue, numericValue,
         Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure])

#print axioms vector_cascade_return
end UInt256Proof.Subtract.Safety
