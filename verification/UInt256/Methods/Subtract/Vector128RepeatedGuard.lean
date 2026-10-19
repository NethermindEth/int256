import UInt256.Methods.Subtract.Vector128Entry
import UInt256.Methods.Subtract.Vector128FastAt
import UInt256.Methods.Subtract.Vector128RepairAt
import UInt256.Methods.Subtract.ScalarDispatchWith
import UInt256.Methods.Subtract.ImplGuards

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector

/-- The incoming-borrow block guarded by an AdvSimd test conjoined with itself. -/
def subtractRepeatedIncomingCode (adv : Bool) : List CIL.Op := if adv then [
  .feature .advSimd, .feature .advSimd, .band, .brzero 53,
  .intrinsic (.vector (.zero 128)) 0, .local 7, .const32 1, .intrinsic (.advSimd .extract64) 3, .setLocal 9,
  .local 7, .local 8, .const32 1, .intrinsic (.advSimd .extract64) 3, .setLocal 10,
  .branch 65,
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile"
] else [
  .feature .advSimd, .feature .advSimd, .band, .brzero 53,
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .local 7, .const32 8, .intrinsic (.sse .shiftLeftBytes) 2, .setLocal 9,
  .local 8, .intrinsic (.vector (.reinterpret 128)) 1, .local 7, .intrinsic (.vector (.reinterpret 128)) 1,
  .const32 8, .intrinsic (.sse .alignBytes) 3, .intrinsic (.vector (.reinterpret 128)) 1, .setLocal 10]

theorem subtract_repeated_incoming_length (adv : Bool) : (subtractRepeatedIncomingCode adv).length = 27 := by
  cases adv <;> rfl

/-- SubtractVector128 whose ISA test repeats the AdvSimd feature in a conjunction. -/
def subtractRepeatedVectorBody (profile : CIL.FeatureProfile) (borrow storage : Nat) : CIL.Method :=
  { profile := profile, returnsValue := true,
    locals := [.nullRef, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
    localKinds := [.reference, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128,
      .vector128, .vector128, .vector128, .word64, .word64, .word64, .word64, .word64],
    parameterHomes := [], staticSites := [],
    code := vector128PrefixCode ++ subtractStartCode ++ subtractRepeatedIncomingCode profile.advSimd ++
      subtractDecisionCodeTo 121 ++ subtractRepairBorrowCode 11 borrow ++ subtractStoreCode 11 storage ++
      subtractFastCode }

/-- The repeated-guard incoming block stores both shifted masks for the selected ISA. -/
theorem subtract_repeated_incoming_checked (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (leadingLength : leading.length = 38)
    (code : body.code = leading ++ subtractRepeatedIncomingCode body.profile.advSimd ++ tail)
    (sse : body.profile.advSimd = false → body.profile.sse2 = true)
    (ssse : body.profile.advSimd = false → body.profile.ssse3 = true)
    (vectorSpecs : ∀ i : Fin 10, specs[i.val]? = some vector128ZeroSpec)
    (original entered current : Memory) (inputs outputs : List Reference)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot) (layout : frame.locals = root :: slots)
    (args : List Value) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity specs slots) (values : Fin 4 → BitVec 128)
    (state : SubtractVectorState program original entered current inputs outputs slots values 8)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, SubtractVectorState program original entered after inputs outputs slots values 10 →
      ∃ fuel result returned,
        run program fuel method 65 args frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 38 args frame [] current = .ok (result, returned) ∧ post result returned := by
  obtain ⟨m8, s9, st8⟩ := state.store body specs frame root layout enteredWF homes (by decide) (vectorSpecs 8)
  obtain ⟨m9, s10, st9⟩ := s9.store body specs frame root layout enteredWF homes (by decide) (vectorSpecs 9)
  have done := continuation m9 s10
  have a6 := state.load frame root layout 6 (by decide) body
  have b6 := s9.load frame root layout 6 (by decide) body
  have b7 := s9.load frame root layout 7 (by decide) body
  have e6 : subtractSnapshot values 6 = subtractMask (values 0) (values 2) := rfl
  have e7 : subtractSnapshot values 7 = subtractMask (values 1) (values 3) := rfl
  have e8 : subtractSnapshot values ⟨8, by decide⟩ = incoming128Low (subtractMask (values 0) (values 2)) := rfl
  have e9 : subtractSnapshot values ⟨9, by decide⟩ =
      incoming128High (subtractMask (values 0) (values 2)) (subtractMask (values 1) (values 3)) := rfl
  rw [e6] at a6 b6
  rw [e7] at b7
  rw [e8] at st8
  rw [e9] at st9
  cases selected : body.profile.advSimd
  · rw [← incoming128_sse_low] at st8
    rw [← incoming128_sse_high] at st9
    repeat' first
      | exact done
      | (apply run_next_exists post found
           (by simp [code, List.getElem?_append, leadingLength, subtractRepeatedIncomingCode, selected]; rfl)
         first
         | exact a6 _ _ _
         | exact b6 _ _ _
         | exact b7 _ _ _
         | exact st8 _ _ _
         | exact st9 _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [show (BitVec.setWidth 8 (8 : BitVec 32)).toNat = 8 from rfl, step, selected, sse, ssse, pureArity,
               scalars, CIL.step.eq_def, CIL.binary, CIL.truth, CIL.Intrinsic.available, CIL.FeatureProfile.evaluate,
               CIL.Vector.intrinsic_sse_shift, CIL.Vector.intrinsic_sse_align,
               CIL.Vector.intrinsic_reinterpret128, checkedValue, numericValue,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))
  · rw [← incoming128_arm_low] at st8
    rw [← incoming128_arm_high] at st9
    repeat' first
      | exact done
      | (apply run_next_exists post found
           (by simp [code, List.getElem?_append, leadingLength, subtractRepeatedIncomingCode, selected]; rfl)
         first
         | exact a6 _ _ _
         | exact b6 _ _ _
         | exact b7 _ _ _
         | exact st8 _ _ _
         | exact st9 _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, selected, pureArity, scalars, CIL.step.eq_def, CIL.binary, CIL.truth, CIL.Intrinsic.available,
               CIL.FeatureProfile.evaluate, CIL.Vector.intrinsic_zero128, CIL.Vector.intrinsic_adv_extract,
               checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms subtract_repeated_incoming_checked
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Subtract.Safety CIL.Vector

theorem subtract_repeated_decision_leading (adv : Bool) :
    (vector128PrefixCode ++ subtractStartCode ++ subtractRepeatedIncomingCode adv).length = 65 := by
  rw [List.length_append, subtract_repeated_incoming_length]
  rfl

/-- Both helper branches from entry: modular difference, exact underflow, caller bytes kept. -/
theorem subtract_repeated_vector_entry (program : CIL.Program) (method borrow storage : Nat)
    (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractRepeatedVectorBody profile borrow storage))
    (borrowFound : program[borrow]? = some (borrowBody profile))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (sse : profile.advSimd = false → profile.sse2 = true)
    (ssse : profile.advSimd = false → profile.ssse3 = true)
    (original entered : Memory) (left right output : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions program original [left, right] [output])
    (setup : enterFrame (subtractRepeatedVectorBody profile borrow storage) args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity subtractVectorSpecs slots)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (outputArg : args[2]? = some (.reference (.address output))) :
    ∃ fuel final returned,
      run program fuel method 0 args frame [] entered = .ok (final, returned) ∧
      SubtractResult original final returned left right output := by
  let body := subtractRepeatedVectorBody profile borrow storage
  let values := subtractInputValues original left right
  let saved := vector128SavedFrame frame slots right
  let decided := vector128PrefixCode ++ subtractStartCode ++ subtractRepeatedIncomingCode profile.advSimd
  have savedLayout : saved.locals = .root (some (.address right)) :: slots := rfl
  have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have owned : ∀ id ∈ saved.owned, original.nextIdentity ≤ id := fun id member => (fresh.2 id member).1
  have decidedLength : decided.length = 65 := subtract_repeated_decision_leading _
  let post := fun final returned => SubtractResult original final returned left right output
  apply vector128_inputs_checked program body method subtractVectorSpecs found
    (subtractStartCode ++ subtractRepeatedIncomingCode profile.advSimd ++ subtractDecisionCodeTo 121 ++
      subtractRepairBorrowCode 11 borrow ++ subtractStoreCode 11 storage ++ subtractFastCode)
    (by simp only [body, subtractRepeatedVectorBody, List.append_assoc]) subtract_vector_first_four
    original entered [left, right] [output] left right frame slots args call setup layout homes
    (by simp) (by simp) leftArg rightArg post
  intro l0 l1 r0 r1 current s0 s1 s2 s3 read0 read1 read2 read3 preserved currentCall authority _
  have state := subtract_initial_state program original entered current left right output slots l0 l1 r0 r1
    s0 s1 s2 s3 read0 read1 read2 read3 preserved currentCall authority
  apply subtract_start_checked program body method subtractVectorSpecs found vector128PrefixCode
    (subtractRepeatedIncomingCode profile.advSimd ++ subtractDecisionCodeTo 121 ++ subtractRepairBorrowCode 11 borrow ++
      subtractStoreCode 11 storage ++ subtractFastCode) rfl
    (by simp only [body, subtractRepeatedVectorBody, List.append_assoc]) subtract_vector_specs
    original entered current [left, right] [output] saved _ slots savedLayout args enteredWF homes values state post
  intro m8 s8
  apply subtract_repeated_incoming_checked program body method subtractVectorSpecs found
    (vector128PrefixCode ++ subtractStartCode)
    (subtractDecisionCodeTo 121 ++ subtractRepairBorrowCode 11 borrow ++ subtractStoreCode 11 storage ++ subtractFastCode)
    rfl (by simp only [body, subtractRepeatedVectorBody, List.append_assoc]) sse ssse subtract_vector_specs
    original entered m8 [left, right] [output] saved _ slots savedLayout args enteredWF homes values s8 post
  intro m10 s10
  apply subtract_decision_checked_at program body method found 65 121 decided
    (subtractRepairBorrowCode 11 borrow ++ subtractStoreCode 11 storage ++ subtractFastCode)
    decidedLength (by simp only [body, decided, subtractRepeatedVectorBody, List.append_assoc])
    original entered m10 [left, right] [output] saved _ slots savedLayout args values s10 post
  by_cases fast : subtractPropagation values = BitVec.ofNat 128 0
  · simp only [fast, ite_true]
    obtain ⟨fuel, final, returned, executed, wellFormed, flag, lowRead, highRead, writable, footprint⟩ :=
      subtract_fast_checked_at program body method subtractVectorSpecs found 121
        (decided ++ subtractDecisionCodeTo 121 ++ subtractRepairBorrowCode 11 borrow ++ subtractStoreCode 11 storage) []
        (by simp only [List.length_append, decidedLength]; rfl)
        (by simp only [body, decided, subtractRepeatedVectorBody, List.append_assoc, List.append_nil]) rfl
        subtract_vector_specs original entered m10 [left, right] [output] output saved _ slots savedLayout args call
        (by simp) outputArg homes values s10 owned
    exact ⟨fuel, final, returned, executed,
      subtract_fast_result original final left right output returned fast wellFormed flag lowRead highRead writable footprint⟩
  · simp only [fast, ite_false]
    apply subtract_repair_borrow_at program body method subtractVectorSpecs found 79 10
      (decided ++ subtractDecisionCodeTo 121)
      (subtractStoreCode 11 storage ++ subtractFastCode) (by simp only [List.length_append, decidedLength]; rfl) borrow
      (by simp only [body, decided, subtractRepeatedVectorBody, List.append_assoc]) borrowFound subtract_word_specs
      original entered m10 saved _ slots savedLayout left right output call s10.call s10.preserved homes enteredWF
      s10.authority args leftArg rightArg post
    intro borrowHome results after borrowState
    exact subtract_store_finish_at program body method found 110 11
      (decided ++ subtractDecisionCodeTo 121 ++ subtractRepairBorrowCode 11 borrow)
      subtractFastCode (by simp only [List.length_append, decidedLength]; rfl) storage
      (by simp only [body, decided, subtractRepeatedVectorBody, List.append_assoc]) storageFound rfl original after saved
      left right output borrowHome results args outputArg call owned borrowState

/-- Checked invocation of the repeated-guard SubtractVector128 with its borrow and storage callees. -/
theorem checked_subtract_repeated_vector (program : CIL.Program) (method borrow storage : Nat)
    (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractRepeatedVectorBody profile borrow storage))
    (borrowFound : program[borrow]? = some (borrowBody profile))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (sse : profile.advSimd = false → profile.sse2 = true)
    (ssse : profile.advSimd = false → profile.ssse3 = true) :
    VectorChecked program method := by
  intro memory left right output call
  let args := binaryArguments left right output
  obtain ⟨frame, entered, slots, setup, layout, homes, _, _⟩ :=
    vector128_frame_setup (subtractRepeatedVectorBody profile borrow storage) subtractVectorSpecs ⟨rfl, rfl⟩ rfl rfl
      memory args call.1.1
  obtain ⟨fuel, final, returned, executed, result⟩ :=
    subtract_repeated_vector_entry program method borrow storage profile found borrowFound storageFound sse ssse
      memory entered left right output frame slots args call setup layout homes rfl rfl rfl
  have checked : args.mapM (checkedValue memory) = .ok args := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [args, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  exact ⟨fuel, final, returned,
    certify_invocation program method _ args memory frame entered fuel final returned found checked setup live executed,
    result⟩

#print axioms subtract_repeated_vector_entry
#print axioms checked_subtract_repeated_vector
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.Subtract.Safety

/-- SubtractImpl and SubtractVector128 both repeat their feature test in a conjunction. -/
theorem checked_repeated_guard_impl (program : CIL.Program) (impl scalar vector borrow small storage : Nat)
    (profile : CIL.FeatureProfile) (noAvx2 : profile.avx2 = false)
    (sse : profile.advSimd = false → profile.sse2 = true)
    (ssse : profile.advSimd = false → profile.ssse3 = true)
    (sse42 : profile.advSimd = false → profile.sse42 = true)
    (implFound : program[impl]? = some (subtractImplBodyWith profile scalar (avx2RepeatedGuard 125) 125))
    (scalarFound : program[scalar]? = some (subtractScalarBodyWith profile vector small 5 41))
    (vectorFound : program[vector]? = some (subtractRepeatedVectorBody profile borrow storage))
    (borrowFound : program[borrow]? = some (borrowBody profile))
    (smallFound : program[small]? = some (subtractSmallBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile)) :
    ReportingBinaryContract (· - ·) (fun a b => decide (a.toNat < b.toNat)) program impl := by
  apply subtract_impl_contract_with program impl scalar profile _ 125 implFound
    (avx2_repeated_guard_skips program impl scalar 125 profile implFound noAvx2)
  intro memory left right output call
  obtain ⟨fuel, final, values, certified, result⟩ :=
    checked_subtract_scalar_contract_with program scalar vector small profile scalarFound
      (checked_subtract_repeated_vector program vector borrow storage profile vectorFound borrowFound storageFound sse ssse)
      (small_checked_of_body program small storage profile smallFound storageFound) sse42 memory left right output call
  exact ⟨fuel, final, values, certified.1, result⟩

#print axioms checked_repeated_guard_impl
end UInt256Proof.Subtract.Profile
