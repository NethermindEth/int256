import UInt256.Methods.Subtract.Vector128Entry
import UInt256.Methods.Subtract.Vector128FastAt
import UInt256.Methods.Subtract.Vector128RepairAt
import UInt256.Methods.Subtract.ScalarDispatchWith
import UInt256.Methods.Subtract.ImplGuards
import UInt256.Methods.Subtract.Vector128Helpers

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector UInt256Proof.AddSubtract

/-- The incoming-borrow block whose AdvSimd upper window comes from a private helper. -/
def subtractHelperIncomingCode (adv : Bool) (pair : Nat) : List CIL.Op := if adv then [
  .feature .advSimd, .brzero 50,
  .intrinsic (.vector (.zero 128)) 0, .local 7, .const32 1, .intrinsic (.advSimd .extract64) 3, .setLocal 9,
  .local 7, .local 8, .call pair 2, .setLocal 10,
  .branch 62,
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile"
] else [
  .feature .advSimd, .brzero 50,
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .local 7, .const32 8, .intrinsic (.sse .shiftLeftBytes) 2, .setLocal 9,
  .local 8, .intrinsic (.vector (.reinterpret 128)) 1, .local 7, .intrinsic (.vector (.reinterpret 128)) 1,
  .const32 8, .intrinsic (.sse .alignBytes) 3, .intrinsic (.vector (.reinterpret 128)) 1, .setLocal 10]

theorem subtract_helper_incoming_length (adv : Bool) (pair : Nat) :
    (subtractHelperIncomingCode adv pair).length = 24 := by
  cases adv <;> rfl

/-- The propagation test whose two half tests are merged by a private helper. -/
def subtractMergeDecisionCode (merge target : Nat) : List CIL.Op := [
  .local 5, .intrinsic (.vector (.zero 128)) 0, .intrinsic (.vector (.eq64 128)) 2,
  .local 9, .intrinsic (.vector (.band 128)) 2,
  .local 6, .intrinsic (.vector (.zero 128)) 0, .intrinsic (.vector (.eq64 128)) 2,
  .local 10, .intrinsic (.vector (.band 128)) 2,
  .call merge 2,
  .intrinsic (.vector (.zero 128)) 0, .intrinsic (.vector (.equalsAll 128)) 2,
  .brnonzero target]

/-- SubtractVector128 with the propagation merge (and the AdvSimd upper window) in private helpers. -/
def subtractHelperVectorBody (profile : CIL.FeatureProfile) (pair merge borrow storage : Nat) : CIL.Method :=
  { profile := profile, returnsValue := true,
    locals := [.nullRef, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
    localKinds := [.reference, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128,
      .vector128, .vector128, .vector128, .word64, .word64, .word64, .word64, .word64],
    parameterHomes := [], staticSites := [],
    code := vector128PrefixCode ++ subtractStartCode ++ subtractHelperIncomingCode profile.advSimd pair ++
      subtractMergeDecisionCode merge 118 ++ subtractRepairBorrowCode 11 borrow ++ subtractStoreCode 11 storage ++
      subtractFastCode }

/-- The helper-based incoming block stores both shifted masks for the selected ISA. -/
theorem subtract_helper_incoming_checked (program : CIL.Program) (body : CIL.Method) (method pair : Nat)
    (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (leadingLength : leading.length = 38)
    (code : body.code = leading ++ subtractHelperIncomingCode body.profile.advSimd pair ++ tail)
    (pairFound : body.profile.advSimd = true → program[pair]? = some (extractPairBody body.profile))
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
        run program fuel method 62 args frame [] after = .ok (result, returned) ∧ post result returned) :
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
           (by simp [code, List.getElem?_append, leadingLength, subtractHelperIncomingCode, selected]; rfl)
         first
         | exact a6 _ _ _
         | exact b6 _ _ _
         | exact b7 _ _ _
         | exact st8 _ _ _
         | exact st9 _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [show (BitVec.setWidth 8 (8 : BitVec 32)).toNat = 8 from rfl, step, selected, sse, ssse, pureArity,
               scalars, CIL.step.eq_def, CIL.truth, CIL.Intrinsic.available, CIL.FeatureProfile.evaluate,
               CIL.Vector.intrinsic_sse_shift, CIL.Vector.intrinsic_sse_align,
               CIL.Vector.intrinsic_reinterpret128, checkedValue, numericValue,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))
  · rw [← incoming128_arm_low] at st8
    rw [← incoming128_arm_high] at st9
    have pairBody := pairFound selected
    have bodyProfile : body.profile.advSimd = true := selected
    iterate 9
      apply run_next_exists post found
        (by simp [code, List.getElem?_append, leadingLength, subtractHelperIncomingCode, selected]; rfl)
      first
      | exact a6 _ _ _
      | exact b6 _ _ _
      | exact b7 _ _ _
      | exact st8 _ _ _
      | (simp (config := { implicitDefEqProofs := false })
          [step, selected, pureArity, scalars, CIL.step.eq_def, CIL.truth, CIL.Intrinsic.available,
            CIL.FeatureProfile.evaluate, CIL.Vector.intrinsic_zero128, CIL.Vector.intrinsic_adv_extract,
            checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
         first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)
    apply run_pure_call_exists post found
      (by simp [code, List.getElem?_append, leadingLength, subtractHelperIncomingCode, selected]; rfl)
      (by simp [step, checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
          try exact ⟨⟨rfl, rfl⟩, rfl⟩)
      ⟨5, extract_pair_invoke body.profile program pair pairBody bodyProfile _ _ _⟩
    apply run_next_exists post found
      (by simp [code, List.getElem?_append, leadingLength, subtractHelperIncomingCode, selected] <;> rfl)
      (st9 _ _ _)
    apply run_next_exists post found
      (by simp [code, List.getElem?_append, leadingLength, subtractHelperIncomingCode, selected]; rfl)
      (by simp [step, pureArity, scalars, CIL.step.eq_def, Bind.bind, Except.bind, Pure.pure, Except.pure]
          try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))
    exact done

/-- Branch on the helper-merged propagation test without writing memory. -/
theorem subtract_merge_decision_checked (program : CIL.Program) (body : CIL.Method) (method merge : Nat)
    (found : program[method]? = some body) (base target : Nat) (leading tail : List CIL.Op)
    (leadingLength : leading.length = base)
    (code : body.code = leading ++ subtractMergeDecisionCode merge target ++ tail)
    (mergeFound : program[merge]? = some (mergePropagationBody body.profile))
    (original entered current : Memory) (inputs outputs : List Reference)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot) (layout : frame.locals = root :: slots)
    (args : List Value) (values : Fin 4 → BitVec 128)
    (state : SubtractVectorState program original entered current inputs outputs slots values 10)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method (if subtractPropagation values = BitVec.ofNat 128 0 then target else base + 14) args frame []
        current = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method base args frame [] current = .ok (result, returned) ∧ post result returned := by
  have a4 := state.load frame root layout 4 (by decide) body
  have a5 := state.load frame root layout 5 (by decide) body
  have a8 := state.load frame root layout 8 (by decide) body
  have a9 := state.load frame root layout 9 (by decide) body
  by_cases zero : subtractPropagation values = BitVec.ofNat 128 0
  all_goals
    simp only [zero, ite_true, ite_false] at continuation
    unfold subtractPropagation at zero
    iterate 10
      apply run_next_exists post found (by seg_fetch code leadingLength)
      first
      | exact a4 _ _ _
      | exact a5 _ _ _
      | exact a8 _ _ _
      | exact a9 _ _ _
      | (simp (config := { implicitDefEqProofs := false })
           [CIL.truth, Option.bind, List.mapM, checkedIntrinsic, step, pureArity, scalars, CIL.step.eq_def,
             CIL.Intrinsic.available, CIL.Vector.intrinsic_zero128, CIL.Vector.intrinsic_eq128,
             CIL.Vector.intrinsic_and128, CIL.Vector.intrinsic_or128, CIL.Vector.intrinsic_equal_all128,
             show (0 : BitVec 128) = BitVec.ofNat 128 0 from rfl, zero,
             checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
         try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))
    apply run_pure_call_exists post found (by seg_fetch code leadingLength)
      (by simp [step, checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
          try exact ⟨⟨rfl, rfl⟩, rfl⟩)
      ⟨4, merge_propagation_invoke body.profile program merge mergeFound _ _ _⟩
    iterate 3
      apply run_next_exists post found (by seg_fetch code leadingLength)
      first
      | exact a4 _ _ _
      | exact a5 _ _ _
      | exact a8 _ _ _
      | exact a9 _ _ _
      | (simp (config := { implicitDefEqProofs := false })
           [CIL.truth, Option.bind, List.mapM, checkedIntrinsic, step, pureArity, scalars, CIL.step.eq_def,
             CIL.Intrinsic.available, CIL.Vector.intrinsic_zero128, CIL.Vector.intrinsic_eq128,
             CIL.Vector.intrinsic_and128, CIL.Vector.intrinsic_or128, CIL.Vector.intrinsic_equal_all128,
             show (0 : BitVec 128) = BitVec.ofNat 128 0 from rfl, zero,
             checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
         try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))
    try simp only [List.reverse_nil, List.nil_append, List.cons_append]
    split
    all_goals first
      | exact continuation
      | (exfalso; simp only [show (0 : BitVec 128) = BitVec.ofNat 128 0 from rfl] at *; simp_all)

#print axioms subtract_helper_incoming_checked
#print axioms subtract_merge_decision_checked
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Subtract.Safety CIL.Vector

theorem subtract_helper_decision_leading (adv : Bool) (pair : Nat) :
    (vector128PrefixCode ++ subtractStartCode ++ subtractHelperIncomingCode adv pair).length = 62 := by
  rw [List.length_append, subtract_helper_incoming_length]
  rfl

/-- Both branches from entry with private vector helpers: modular difference, exact underflow, caller bytes kept. -/
theorem subtract_helper_vector_entry (program : CIL.Program) (method pair merge borrow storage : Nat)
    (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractHelperVectorBody profile pair merge borrow storage))
    (pairFound : profile.advSimd = true → program[pair]? = some (extractPairBody profile))
    (mergeFound : program[merge]? = some (mergePropagationBody profile))
    (borrowFound : program[borrow]? = some (borrowBody profile))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (sse : profile.advSimd = false → profile.sse2 = true)
    (ssse : profile.advSimd = false → profile.ssse3 = true)
    (original entered : Memory) (left right output : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions program original [left, right] [output])
    (setup : enterFrame (subtractHelperVectorBody profile pair merge borrow storage) args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity subtractVectorSpecs slots)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (outputArg : args[2]? = some (.reference (.address output))) :
    ∃ fuel final returned,
      run program fuel method 0 args frame [] entered = .ok (final, returned) ∧
      SubtractResult original final returned left right output := by
  let body := subtractHelperVectorBody profile pair merge borrow storage
  let values := subtractInputValues original left right
  let saved := vector128SavedFrame frame slots right
  let decided := vector128PrefixCode ++ subtractStartCode ++ subtractHelperIncomingCode profile.advSimd pair
  have savedLayout : saved.locals = .root (some (.address right)) :: slots := rfl
  have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have owned : ∀ id ∈ saved.owned, original.nextIdentity ≤ id := fun id member => (fresh.2 id member).1
  have decidedLength : decided.length = 62 := subtract_helper_decision_leading _ _
  let post := fun final returned => SubtractResult original final returned left right output
  apply vector128_inputs_checked program body method subtractVectorSpecs found
    (subtractStartCode ++ subtractHelperIncomingCode profile.advSimd pair ++ subtractMergeDecisionCode merge 118 ++
      subtractRepairBorrowCode 11 borrow ++ subtractStoreCode 11 storage ++ subtractFastCode)
    (by simp only [body, subtractHelperVectorBody, List.append_assoc]) subtract_vector_first_four
    original entered [left, right] [output] left right frame slots args call setup layout homes
    (by simp) (by simp) leftArg rightArg post
  intro l0 l1 r0 r1 current s0 s1 s2 s3 read0 read1 read2 read3 preserved currentCall authority _
  have state := subtract_initial_state program original entered current left right output slots l0 l1 r0 r1
    s0 s1 s2 s3 read0 read1 read2 read3 preserved currentCall authority
  apply subtract_start_checked program body method subtractVectorSpecs found vector128PrefixCode
    (subtractHelperIncomingCode profile.advSimd pair ++ subtractMergeDecisionCode merge 118 ++ subtractRepairBorrowCode 11 borrow ++
      subtractStoreCode 11 storage ++ subtractFastCode) rfl
    (by simp only [body, subtractHelperVectorBody, List.append_assoc]) subtract_vector_specs
    original entered current [left, right] [output] saved _ slots savedLayout args enteredWF homes values state post
  intro m8 s8
  apply subtract_helper_incoming_checked program body method pair subtractVectorSpecs found
    (vector128PrefixCode ++ subtractStartCode)
    (subtractMergeDecisionCode merge 118 ++ subtractRepairBorrowCode 11 borrow ++ subtractStoreCode 11 storage ++ subtractFastCode)
    rfl (by simp only [body, subtractHelperVectorBody, List.append_assoc]) pairFound sse ssse subtract_vector_specs
    original entered m8 [left, right] [output] saved _ slots savedLayout args enteredWF homes values s8 post
  intro m10 s10
  apply subtract_merge_decision_checked program body method merge found 62 118 decided
    (subtractRepairBorrowCode 11 borrow ++ subtractStoreCode 11 storage ++ subtractFastCode)
    decidedLength (by simp only [body, decided, subtractHelperVectorBody, List.append_assoc]) mergeFound
    original entered m10 [left, right] [output] saved _ slots savedLayout args values s10 post
  by_cases fast : subtractPropagation values = BitVec.ofNat 128 0
  · simp only [fast, ite_true]
    obtain ⟨fuel, final, returned, executed, wellFormed, flag, lowRead, highRead, writable, footprint⟩ :=
      subtract_fast_checked_at program body method subtractVectorSpecs found 118
        (decided ++ subtractMergeDecisionCode merge 118 ++ subtractRepairBorrowCode 11 borrow ++ subtractStoreCode 11 storage) []
        (by simp only [List.length_append, decidedLength]; rfl)
        (by simp only [body, decided, subtractHelperVectorBody, List.append_assoc, List.append_nil]) rfl
        subtract_vector_specs original entered m10 [left, right] [output] output saved _ slots savedLayout args call
        (by simp) outputArg homes values s10 owned
    exact ⟨fuel, final, returned, executed,
      subtract_fast_result original final left right output returned fast wellFormed flag lowRead highRead writable footprint⟩
  · simp only [fast, ite_false]
    apply subtract_repair_borrow_at program body method subtractVectorSpecs found 76 10
      (decided ++ subtractMergeDecisionCode merge 118)
      (subtractStoreCode 11 storage ++ subtractFastCode) (by simp only [List.length_append, decidedLength]; rfl) borrow
      (by simp only [body, decided, subtractHelperVectorBody, List.append_assoc]) borrowFound subtract_word_specs
      original entered m10 saved _ slots savedLayout left right output call s10.call s10.preserved homes enteredWF
      s10.authority args leftArg rightArg post
    intro borrowHome results after borrowState
    exact subtract_store_finish_at program body method found 107 11
      (decided ++ subtractMergeDecisionCode merge 118 ++ subtractRepairBorrowCode 11 borrow)
      subtractFastCode (by simp only [List.length_append, decidedLength]; rfl) storage
      (by simp only [body, decided, subtractHelperVectorBody, List.append_assoc]) storageFound rfl original after saved
      left right output borrowHome results args outputArg call owned borrowState

/-- Checked invocation of the helper-based SubtractVector128 with its callees. -/
theorem checked_subtract_helper_vector (program : CIL.Program) (method pair merge borrow storage : Nat)
    (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractHelperVectorBody profile pair merge borrow storage))
    (pairFound : profile.advSimd = true → program[pair]? = some (extractPairBody profile))
    (mergeFound : program[merge]? = some (mergePropagationBody profile))
    (borrowFound : program[borrow]? = some (borrowBody profile))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (sse : profile.advSimd = false → profile.sse2 = true)
    (ssse : profile.advSimd = false → profile.ssse3 = true) :
    VectorChecked program method := by
  intro memory left right output call
  let args := binaryArguments left right output
  obtain ⟨frame, entered, slots, setup, layout, homes, _, _⟩ :=
    vector128_frame_setup (subtractHelperVectorBody profile pair merge borrow storage) subtractVectorSpecs ⟨rfl, rfl⟩ rfl rfl
      memory args call.1.1
  obtain ⟨fuel, final, returned, executed, result⟩ :=
    subtract_helper_vector_entry program method pair merge borrow storage profile found pairFound mergeFound borrowFound storageFound sse ssse
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

#print axioms subtract_helper_vector_entry
#print axioms checked_subtract_helper_vector
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.Subtract.Safety

/-- SubtractVector128 with its window extraction and propagation merge in private helpers. -/
theorem checked_extracted_helpers_impl (program : CIL.Program) (impl scalar vector pair merge borrow small storage : Nat)
    (profile : CIL.FeatureProfile) (noAvx2 : profile.avx2 = false)
    (sse : profile.advSimd = false → profile.sse2 = true)
    (ssse : profile.advSimd = false → profile.ssse3 = true)
    (sse42 : profile.advSimd = false → profile.sse42 = true)
    (implFound : program[impl]? = some (subtractImplBodyWith profile scalar (avx2Guard 121) 121))
    (scalarFound : program[scalar]? = some (subtractScalarBodyWith profile vector small 5 41))
    (vectorFound : program[vector]? = some (subtractHelperVectorBody profile pair merge borrow storage))
    (pairFound : profile.advSimd = true → program[pair]? = some (extractPairBody profile))
    (mergeFound : program[merge]? = some (mergePropagationBody profile))
    (borrowFound : program[borrow]? = some (borrowBody profile))
    (smallFound : program[small]? = some (subtractSmallBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile)) :
    ReportingBinaryContract (· - ·) (fun a b => decide (a.toNat < b.toNat)) program impl := by
  apply subtract_impl_contract_with program impl scalar profile _ 121 implFound
    (avx2_guard_skips program impl scalar 121 profile implFound noAvx2)
  intro memory left right output call
  obtain ⟨fuel, final, values, certified, result⟩ :=
    checked_subtract_scalar_contract_with program scalar vector small profile scalarFound
      (checked_subtract_helper_vector program vector pair merge borrow storage profile vectorFound pairFound mergeFound
        borrowFound storageFound sse ssse)
      (small_checked_of_body program small storage profile smallFound storageFound) sse42 memory left right output call
  exact ⟨fuel, final, values, certified.1, result⟩

#print axioms checked_extracted_helpers_impl
end UInt256Proof.Subtract.Profile
