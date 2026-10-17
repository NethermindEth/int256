import UInt256.Methods.Subtract.Vector128RepairAt
import UInt256.Methods.Subtract.Vector128FastAt
import UInt256.Methods.Subtract.Vector128Entry
import UInt256.Methods.Subtract.ImplGuards
import UInt256.Methods.Subtract.ReversedSmallHelper

namespace UInt256Proof.Subtract.Profile

/-- Store the four words high first for the reversed StoreLimbs and return the final borrow. -/
def subtractReversedStoreCode (bl storage : Nat) : List CIL.Op := [
  .arg 2, .local (bl + 4), .local (bl + 3), .local (bl + 2), .local (bl + 1), .call storage 5,
  .local bl, .const32 0, .convI8, .gtu, .ret (some .unsigned8)]
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Subtract.Safety

/-- Push the output reference and the four completed words high first for the reversed storage call. -/
theorem subtract_reversed_store_prefix_at (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (base bl : Nat) (leading tail : List CIL.Op) (leadingLength : leading.length = base)
    (storage : Nat) (code : body.code = leading ++ subtractReversedStoreCode bl storage ++ tail)
    (output : Reference) (args : List Value)
    (outputArg : args[2]? = some (.reference (.address output)))
    (frame : Frame) (memory : Memory) (results : Fin 4 → Reference) (words : Fin 4 → BitVec 64)
    (outputFormed : form memory output = .ok output)
    (slots : ∀ i, frame.locals[i.val + (bl + 1)]? = some (.bytes .word64 (results i)))
    (reads : ∀ i, read memory (results i) 8 1 = .ok (numberBytes (words i).toNat 8))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method (base + 5) args frame
        [.scalar (.i64 (words 0)), .scalar (.i64 (words 1)), .scalar (.i64 (words 2)),
          .scalar (.i64 (words 3)), .reference (.address output)] memory = .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run program fuel method base args frame [] memory = .ok (result, returned) ∧ post result returned := by
  have s0 : frame.locals[bl + 1]? = some (.bytes .word64 (results 0)) := by simpa using slots 0
  have s1 : frame.locals[bl + 2]? = some (.bytes .word64 (results 1)) := by
    simpa [show 1 + (bl + 1) = bl + 2 by omega] using slots 1
  have s2 : frame.locals[bl + 3]? = some (.bytes .word64 (results 2)) := by
    simpa [show 2 + (bl + 1) = bl + 3 by omega] using slots 2
  have s3 : frame.locals[bl + 4]? = some (.bytes .word64 (results 3)) := by
    simpa [CIL.fin_val_three, show 3 + (bl + 1) = bl + 4 by omega] using slots 3
  have r0 := load_local_word64_of_read (reads 0)
  have r1 := load_local_word64_of_read (reads 1)
  have r2 := load_local_word64_of_read (reads 2)
  have r3 := load_local_word64_of_read (reads 3)
  repeat' first
    | exact continuation
    | (apply run_next_exists post found (by seg_fetch code leadingLength)
       simp (config := { implicitDefEqProofs := false })
         [step, checkedValue, formValue, outputArg, outputFormed, s0, s1, s2, s3, r0, r1, r2, r3,
           checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

/-- Return the final borrow word as the unsigned underflow flag and retire the frame. -/
theorem subtract_reversed_store_return_at (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (base bl : Nat) (leading tail : List CIL.Op) (leadingLength : leading.length = base)
    (storage : Nat) (code : body.code = leading ++ subtractReversedStoreCode bl storage ++ tail)
    (returns : body.returnsValue = true)
    (args : List Value) (frame : Frame) (memory : Memory)
    (borrowHome : Reference) (borrowWord : BitVec 64)
    (slot : frame.locals[bl]? = some (.bytes .word64 borrowHome))
    (loaded : read memory borrowHome 8 1 = .ok (numberBytes borrowWord.toNat 8)) :
    run program 5 method (base + 6) args frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (scalarUnderflowFlag borrowWord))]) := by
  have reading := load_local_word64_of_read loaded
  iterate 4
    apply Eq.trans
    · apply run_next found (by seg_fetch code leadingLength)
      simp (config := { implicitDefEqProofs := false })
        [step, slot, reading, checkedValue, numericValue, pureArity, scalars,
          CIL.step.eq_def, CIL.binary, CIL.unary, instruction, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  have fetched : body.code[base + 6 + 1 + 1 + 1 + 1]? = some (.ret (some .unsigned8)) := by
    seg_fetch code leadingLength
  by_cases positive : BitVec.ofNat 64 0 < borrowWord
  all_goals simp [run, found, fetched, returns, step, checkedValue, numericValue, CIL.NarrowKind.extend,
    scalarUnderflowFlag, positive, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Store the four ripple words through the reversed limb helper and return the exact borrow. -/
theorem subtract_reversed_store_finish_at (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (base bl : Nat) (leading tail : List CIL.Op) (leadingLength : leading.length = base)
    (storage : Nat) (code : body.code = leading ++ subtractReversedStoreCode bl storage ++ tail)
    (storageFound : program[storage]? = some (reversedStorageBody body.profile))
    (returns : body.returnsValue = true)
    (original current : CIL.Safety.Memory) (frame : Frame)
    (left right output borrowHome : Reference) (results : Fin 4 → Reference) (args : List Value)
    (outputArg : args[2]? = some (.reference (.address output)))
    (call : CallingConditions program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : ScalarBorrowState (program := program) original current frame left right output borrowHome results 4
      bl (bl + 1)) :
    ∃ fuel final values,
      run program fuel method base args frame [] current = .ok (final, values) ∧
      SubtractResult original final values left right output := by
  let words := scalarDifferenceWord original left right
  let post := fun final values => SubtractResult original final values left right output
  have formed := state.call.output_formed (by simp : output ∈ [output])
  apply subtract_reversed_store_prefix_at program body method found base bl leading tail leadingLength storage code
    output args outputArg frame current results words formed state.resultSlots (fun i => state.completed i i.isLt) post
  obtain ⟨childFuel, stored, invoked, valid, outside, authority, value, _⟩ :=
    reversed_store_limbs_readable_contract body.profile program storage storageFound
      current [left, right] output (words 0) (words 1) (words 2) (words 3) state.call
  have stepped : step body (.call storage 5) (base + 5) args frame
      [.scalar (.i64 (words 0)), .scalar (.i64 (words 1)), .scalar (.i64 (words 2)),
        .scalar (.i64 (words 3)), .reference (.address output)] current =
      .ok (.call storage (UInt256Proof.Multiply.LimbStorage.arguments output (words 3) (words 2) (words 1) (words 0))
        [] current) := by
    simp [step, UInt256Proof.Multiply.LimbStorage.arguments, checkedValue, numericValue,
      formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    try exact ⟨rfl, rfl⟩
  obtain ⟨outputAllocation, outputPresent, _, _⟩ := formed_reference_live _ _ _
    (call.output_formed (by simp : output ∈ [output]))
  have outputOld := (call.1.1.1 _ _ outputPresent).1
  obtain ⟨borrowAllocation, borrowPresent, _, _⟩ := access_within_allocation _ _ _ _ _ state.borrowWrite
  have borrowOld := (state.call.1.1.1 _ _ borrowPresent).1
  have distinct : borrowHome.allocation ≠ output.allocation :=
    Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le outputOld state.borrowFresh))
  have borrowRead := authority.read_eq state.borrowRead borrowOld
    (fun i _ => outside _ _ (Or.inl distinct))
  have returned := subtract_reversed_store_return_at program body method found base bl leading tail leadingLength storage code
    returns args frame stored borrowHome _ state.borrowSlot borrowRead
  obtain ⟨fuel, executed⟩ := run_call_exists found
    (by seg_fetch code leadingLength) stepped ⟨childFuel, invoked⟩ ⟨5, returned⟩
  refine ⟨fuel, leaveFrame frame stored, _, executed, ?_⟩
  have retained := leaveFrame_preserves_memory_below frame stored original.nextIdentity owned
  have bytes : (fun offset => ((leaveFrame frame stored).cells output.allocation offset).bits) =
      (fun offset => (stored.cells output.allocation offset).bits) := by
    funext offset
    rw [retained.cells output.allocation outputOld offset]
  refine ⟨leaveFrame_preserves_wellFormed _ _ valid.1.1, ?_, ?_, ?_, ?_⟩
  · have computed : inputValue (leaveFrame frame stored) output = scalarDifferenceValue original left right := by
      simpa only [inputValue, bytes, scalarDifferenceValue] using value
    exact computed.trans (scalar_difference_value original left right)
  · rw [scalar_flag_underflow]
    rfl
  · exact (retained.access output outputOld 32 1 true).trans
      (valid.1.2.2 (wordView output) (by simp))
  · intro id old offset untouched
    exact (retained.cells id old offset).trans ((outside id offset untouched).trans (state.callerCells id old offset))

#print axioms subtract_reversed_store_prefix_at
#print axioms subtract_reversed_store_return_at
#print axioms subtract_reversed_store_finish_at
end UInt256Proof.Subtract.Profile
namespace UInt256Proof.Subtract.Profile
open UInt256Proof.AddSubtract.Safety

/-- SubtractVector128 whose repair path stores its words high first. -/
def subtractReversedVectorBody (profile : CIL.FeatureProfile) (borrow storage : Nat) : CIL.Method :=
  { profile := profile, returnsValue := true,
    locals := [.nullRef, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
    localKinds := [.reference, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128,
      .vector128, .vector128, .vector128, .word64, .word64, .word64, .word64, .word64],
    parameterHomes := [], staticSites := [],
    code := vector128PrefixCode ++ subtractStartCode ++ subtractIncomingCode profile.advSimd ++
      subtractDecisionCodeTo 119 ++ subtractRepairBorrowCode 11 borrow ++ subtractReversedStoreCode 11 storage ++
      subtractFastCode }
end UInt256Proof.Subtract.Profile


namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Subtract.Safety CIL.Vector

/-- Both helper branches from entry: modular difference, exact underflow, caller bytes kept. -/
theorem subtract_reversed_vector_entry (program : CIL.Program) (method borrow storage : Nat)
    (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractReversedVectorBody profile borrow storage))
    (borrowFound : program[borrow]? = some (borrowBody profile))
    (storageFound : program[storage]? = some (reversedStorageBody profile))
    (sse : profile.advSimd = false → profile.sse2 = true)
    (ssse : profile.advSimd = false → profile.ssse3 = true)
    (original entered : Memory) (left right output : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions program original [left, right] [output])
    (setup : enterFrame (subtractReversedVectorBody profile borrow storage) args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity subtractVectorSpecs slots)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (outputArg : args[2]? = some (.reference (.address output))) :
    ∃ fuel final returned,
      run program fuel method 0 args frame [] entered = .ok (final, returned) ∧
      SubtractResult original final returned left right output := by
  let body := subtractReversedVectorBody profile borrow storage
  let values := subtractInputValues original left right
  let saved := vector128SavedFrame frame slots right
  let decided := vector128PrefixCode ++ subtractStartCode ++ subtractIncomingCode profile.advSimd
  have savedLayout : saved.locals = .root (some (.address right)) :: slots := rfl
  have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have owned : ∀ id ∈ saved.owned, original.nextIdentity ≤ id := fun id member => (fresh.2 id member).1
  have decidedLength : decided.length = 63 := subtract_incoming_leading _
  let post := fun final returned => SubtractResult original final returned left right output
  apply vector128_inputs_checked program body method subtractVectorSpecs found
    (subtractStartCode ++ subtractIncomingCode profile.advSimd ++ subtractDecisionCodeTo 119 ++
      subtractRepairBorrowCode 11 borrow ++ subtractReversedStoreCode 11 storage ++ subtractFastCode)
    (by simp only [body, subtractReversedVectorBody, List.append_assoc]) subtract_vector_first_four
    original entered [left, right] [output] left right frame slots args call setup layout homes
    (by simp) (by simp) leftArg rightArg post
  intro l0 l1 r0 r1 current s0 s1 s2 s3 read0 read1 read2 read3 preserved currentCall authority _
  have state := subtract_initial_state program original entered current left right output slots l0 l1 r0 r1
    s0 s1 s2 s3 read0 read1 read2 read3 preserved currentCall authority
  apply subtract_start_checked program body method subtractVectorSpecs found vector128PrefixCode
    (subtractIncomingCode profile.advSimd ++ subtractDecisionCodeTo 119 ++ subtractRepairBorrowCode 11 borrow ++
      subtractReversedStoreCode 11 storage ++ subtractFastCode) rfl
    (by simp only [body, subtractReversedVectorBody, List.append_assoc]) subtract_vector_specs
    original entered current [left, right] [output] saved _ slots savedLayout args enteredWF homes values state post
  intro m8 s8
  apply subtract_incoming_checked program body method subtractVectorSpecs found
    (vector128PrefixCode ++ subtractStartCode)
    (subtractDecisionCodeTo 119 ++ subtractRepairBorrowCode 11 borrow ++ subtractReversedStoreCode 11 storage ++ subtractFastCode)
    rfl (by simp only [body, subtractReversedVectorBody, List.append_assoc]) sse ssse subtract_vector_specs
    original entered m8 [left, right] [output] saved _ slots savedLayout args enteredWF homes values s8 post
  intro m10 s10
  apply subtract_decision_checked_at program body method found 63 119 decided
    (subtractRepairBorrowCode 11 borrow ++ subtractReversedStoreCode 11 storage ++ subtractFastCode)
    decidedLength (by simp only [body, decided, subtractReversedVectorBody, List.append_assoc])
    original entered m10 [left, right] [output] saved _ slots savedLayout args values s10 post
  by_cases fast : subtractPropagation values = BitVec.ofNat 128 0
  · simp only [fast, ite_true]
    obtain ⟨fuel, final, returned, executed, wellFormed, flag, lowRead, highRead, writable, footprint⟩ :=
      subtract_fast_checked_at program body method subtractVectorSpecs found 119
        (decided ++ subtractDecisionCodeTo 119 ++ subtractRepairBorrowCode 11 borrow ++ subtractReversedStoreCode 11 storage) []
        (by simp only [List.length_append, decidedLength]; rfl)
        (by simp only [body, decided, subtractReversedVectorBody, List.append_assoc, List.append_nil]) rfl
        subtract_vector_specs original entered m10 [left, right] [output] output saved _ slots savedLayout args call
        (by simp) outputArg homes values s10 owned
    exact ⟨fuel, final, returned, executed,
      subtract_fast_result original final left right output returned fast wellFormed flag lowRead highRead writable footprint⟩
  · simp only [fast, ite_false]
    apply subtract_repair_borrow_at program body method subtractVectorSpecs found 77 10
      (decided ++ subtractDecisionCodeTo 119)
      (subtractReversedStoreCode 11 storage ++ subtractFastCode) (by simp only [List.length_append, decidedLength]; rfl) borrow
      (by simp only [body, decided, subtractReversedVectorBody, List.append_assoc]) borrowFound subtract_word_specs
      original entered m10 saved _ slots savedLayout left right output call s10.call s10.preserved homes enteredWF
      s10.authority args leftArg rightArg post
    intro borrowHome results after borrowState
    exact subtract_reversed_store_finish_at program body method found 108 11
      (decided ++ subtractDecisionCodeTo 119 ++ subtractRepairBorrowCode 11 borrow)
      subtractFastCode (by simp only [List.length_append, decidedLength]; rfl) storage
      (by simp only [body, decided, subtractReversedVectorBody, List.append_assoc]) storageFound rfl original after saved
      left right output borrowHome results args outputArg call owned borrowState

/-- Checked invocation of the reversed-store SubtractVector128 with its borrow and storage callees. -/
theorem checked_subtract_reversed_vector (program : CIL.Program) (method borrow storage : Nat)
    (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractReversedVectorBody profile borrow storage))
    (borrowFound : program[borrow]? = some (borrowBody profile))
    (storageFound : program[storage]? = some (reversedStorageBody profile))
    (sse : profile.advSimd = false → profile.sse2 = true)
    (ssse : profile.advSimd = false → profile.ssse3 = true) :
    VectorChecked program method := by
  intro memory left right output call
  let args := binaryArguments left right output
  obtain ⟨frame, entered, slots, setup, layout, homes, _, _⟩ :=
    vector128_frame_setup (subtractReversedVectorBody profile borrow storage) subtractVectorSpecs ⟨rfl, rfl⟩ rfl rfl
      memory args call.1.1
  obtain ⟨fuel, final, returned, executed, result⟩ :=
    subtract_reversed_vector_entry program method borrow storage profile found borrowFound storageFound sse ssse
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

#print axioms subtract_reversed_vector_entry
#print axioms checked_subtract_reversed_vector
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.Subtract.Safety

/-- StoreLimbs takes its words high first at every call site. -/
theorem checked_reversed_store_impl (program : CIL.Program) (impl scalar vector borrow small storage : Nat)
    (profile : CIL.FeatureProfile) (noAvx2 : profile.avx2 = false)
    (sse : profile.advSimd = false → profile.sse2 = true)
    (ssse : profile.advSimd = false → profile.ssse3 = true)
    (sse42 : profile.advSimd = false → profile.sse42 = true)
    (implFound : program[impl]? = some (subtractImplBodyWith profile scalar (avx2Guard 123) 123))
    (scalarFound : program[scalar]? = some (subtractScalarBodyWith profile vector small 5 41))
    (vectorFound : program[vector]? = some (subtractReversedVectorBody profile borrow storage))
    (borrowFound : program[borrow]? = some (borrowBody profile))
    (smallFound : program[small]? = some (subtractReversedSmallBody profile storage))
    (storageFound : program[storage]? = some (reversedStorageBody profile)) :
    ReportingBinaryContract (· - ·) (fun a b => decide (a.toNat < b.toNat)) program impl := by
  apply subtract_impl_contract_with program impl scalar profile _ 123 implFound
    (avx2_guard_skips program impl scalar 123 profile implFound noAvx2)
  intro memory left right output call
  obtain ⟨fuel, final, values, certified, result⟩ :=
    checked_subtract_scalar_contract_with program scalar vector small profile scalarFound
      (checked_subtract_reversed_vector program vector borrow storage profile vectorFound borrowFound storageFound sse ssse)
      (reversed_small_checked program small storage profile smallFound storageFound) sse42 memory left right output call
  exact ⟨fuel, final, values, certified.1, result⟩

#print axioms checked_reversed_store_impl
end UInt256Proof.Subtract.Profile
