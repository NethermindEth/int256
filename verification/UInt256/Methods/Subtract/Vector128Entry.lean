import UInt256.Methods.Subtract.Vector128Arithmetic
import UInt256.Methods.Subtract.Vector128Repair
import UInt256.Methods.Subtract.Vector128Fast

namespace UInt256Proof.Subtract.Profile
open UInt256Proof.AddSubtract.Safety

/-- SubtractVector128 for either 128-bit ISA; only the incoming-mask block differs. -/
def subtractVectorBody (profile : CIL.FeatureProfile) (borrow storage : Nat) : CIL.Method :=
  { profile := profile, returnsValue := true,
    locals := [.nullRef, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0, .v128 0,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
    localKinds := [.reference, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128, .vector128,
      .vector128, .vector128, .vector128, .word64, .word64, .word64, .word64, .word64],
    parameterHomes := [], staticSites := [],
    code := vector128PrefixCode ++ subtractStartCode ++ subtractIncomingCode profile.advSimd ++
      subtractDecisionCode ++ subtractRepairCode borrow storage ++ subtractFastCode }

def subtractVectorSpecs : List CIL.Safety.NumericLocalSpec :=
  List.replicate 10 vector128ZeroSpec ++ List.replicate 5 subtractWordSpec

theorem subtract_vector_specs : ∀ i : Fin 10, subtractVectorSpecs[i.val]? = some vector128ZeroSpec := by
  intro i
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem subtract_word_specs : ∀ i : Fin 5, subtractVectorSpecs[10 + i.val]? = some subtractWordSpec := by
  intro i
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem subtract_vector_first_four : ∀ i : Fin 4, subtractVectorSpecs[i.val]? = some vector128ZeroSpec :=
  fun i => subtract_vector_specs ⟨i.val, by omega⟩

#print axioms subtract_vector_specs
#print axioms subtract_word_specs
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Subtract.Safety CIL.Vector UInt256Proof

/-- Initial operand halves as the first four saved snapshots. -/
theorem subtract_initial_state (program : CIL.Program) (original entered current : Memory)
    (left right output : Reference) (slots : List LocalSlot) (l0 l1 r0 r1 : Reference)
    (s0 : slots[0]? = some (.bytes .vector128 l0)) (s1 : slots[1]? = some (.bytes .vector128 l1))
    (s2 : slots[2]? = some (.bytes .vector128 r0)) (s3 : slots[3]? = some (.bytes .vector128 r1))
    (read0 : read current l0 16 1 = .ok (numberBytes (inputHalf original left 0).toNat 16))
    (read1 : read current l1 16 1 = .ok (numberBytes (inputHalf original left 1).toNat 16))
    (read2 : read current r0 16 1 = .ok (numberBytes (inputHalf original right 0).toNat 16))
    (read3 : read current r1 16 1 = .ok (numberBytes (inputHalf original right 1).toNat 16))
    (preserved : MemoryBelow original.nextIdentity original current)
    (currentCall : CallingConditions program current [left, right] [output])
    (authority : AccessBelow entered.nextIdentity entered current) :
    SubtractVectorState program original entered current [left, right] [output] slots
      (subtractInputValues original left right) 4 := by
  obtain ⟨v0, v1, v2, v3⟩ := subtract_input_values original left right
  refine ⟨currentCall, preserved, authority, ?_⟩
  intro i lower
  obtain ⟨i, bound⟩ := i
  have small : i < 4 := lower
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact ⟨l0, s0, by
      change read current l0 16 1 = .ok (numberBytes (subtractInputValues original left right 0).toNat 16)
      rw [v0]; exact read0⟩
  · exact ⟨l1, s1, by
      change read current l1 16 1 = .ok (numberBytes (subtractInputValues original left right 1).toNat 16)
      rw [v1]; exact read1⟩
  · exact ⟨r0, s2, by
      change read current r0 16 1 = .ok (numberBytes (subtractInputValues original left right 2).toNat 16)
      rw [v2]; exact read2⟩
  · exact ⟨r1, s3, by
      change read current r1 16 1 = .ok (numberBytes (subtractInputValues original left right 3).toNat 16)
      rw [v3]; exact read3⟩

/-- Fast-path facts denote the independent difference and underflow of the initial operands. -/
theorem subtract_fast_result (original final : Memory) (left right output : Reference) (returned : List Value)
    (fast : subtractPropagation (subtractInputValues original left right) = BitVec.ofNat 128 0)
    (wellFormed : final.WellFormed)
    (flag : returned = [.scalar (.i32 (if lane64 (subtractSnapshot (subtractInputValues original left right) 7) 1 >
      BitVec.ofNat 64 0 then 1 else 0))])
    (lowRead : read final output 16 1 = .ok (numberBytes (zip128 (· + ·)
      (subtractSnapshot (subtractInputValues original left right) 4)
      (subtractSnapshot (subtractInputValues original left right) 8)).toNat 16))
    (highRead : read final { output with offset := output.offset + 16 } 16 1 = .ok (numberBytes (zip128 (· + ·)
      (subtractSnapshot (subtractInputValues original left right) 5)
      (subtractSnapshot (subtractInputValues original left right) 9)).toNat 16))
    (writable : access final output 32 1 true = .ok ())
    (footprint : ∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
      final.cells id offset = original.cells id offset) :
    SubtractResult original final returned left right output := by
  let a := inputLimb original left
  let b := inputLimb original right
  have none : NoBorrowPropagation a b := by
    apply propagation128_zero
    rw [← limb_propagation]
    exact fast
  change read final output 16 1 = .ok (numberBytes (zip128 (· + ·)
    (subtractSnapshot (limbHalves a b) 4) (subtractSnapshot (limbHalves a b) 8)).toNat 16) at lowRead
  change read final { output with offset := output.offset + 16 } 16 1 = .ok (numberBytes (zip128 (· + ·)
    (subtractSnapshot (limbHalves a b) 5) (subtractSnapshot (limbHalves a b) 9)).toNat 16) at highRead
  rw [limb_fast_low] at lowRead
  rw [limb_fast_high] at highRead
  refine ⟨wellFormed, ?_, ?_, writable, fun id bound offset outside => footprint id offset bound outside⟩
  · rw [output_value_of_packed_halves final output (speculativeDifference a b) lowRead highRead,
      speculative_difference_value a b none, input_limbs_value, input_limbs_value]
  · rw [flag]
    change [Value.scalar (.i32 (if lane64 (subtractSnapshot (limbHalves a b) 7) 1 > BitVec.ofNat 64 0 then 1 else 0))] = _
    rw [limb_fast_underflow a b none, input_limbs_value, input_limbs_value]
    rfl

#print axioms subtract_initial_state
#print axioms subtract_fast_result
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Subtract.Safety CIL.Vector

/-- Both helper branches from entry: modular difference, exact underflow, caller bytes kept. -/
theorem subtract_vector_entry (program : CIL.Program) (method borrow storage : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractVectorBody profile borrow storage))
    (borrowFound : program[borrow]? = some (borrowBody profile))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (sse : profile.advSimd = false → profile.sse2 = true)
    (ssse : profile.advSimd = false → profile.ssse3 = true)
    (original entered : Memory) (left right output : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions program original [left, right] [output])
    (setup : enterFrame (subtractVectorBody profile borrow storage) args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity subtractVectorSpecs slots)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (outputArg : args[2]? = some (.reference (.address output))) :
    ∃ fuel final returned,
      run program fuel method 0 args frame [] entered = .ok (final, returned) ∧
      SubtractResult original final returned left right output := by
  let body := subtractVectorBody profile borrow storage
  let values := subtractInputValues original left right
  let saved := vector128SavedFrame frame slots right
  have savedLayout : saved.locals = .root (some (.address right)) :: slots := rfl
  have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have owned : ∀ id ∈ saved.owned, original.nextIdentity ≤ id := fun id member => (fresh.2 id member).1
  let post := fun final returned => SubtractResult original final returned left right output
  apply vector128_inputs_checked program body method subtractVectorSpecs found
    (by cases selected : profile.advSimd <;> simp only [CodeAt, body, subtractVectorBody, selected] <;> rfl) subtract_vector_first_four
    original entered [left, right] [output] left right frame slots args call setup layout homes
    (by simp) (by simp) leftArg rightArg post
  intro l0 l1 r0 r1 current s0 s1 s2 s3 read0 read1 read2 read3 preserved currentCall authority _
  have state := subtract_initial_state program original entered current left right output slots l0 l1 r0 r1
    s0 s1 s2 s3 read0 read1 read2 read3 preserved currentCall authority
  apply subtract_start_checked program body method subtractVectorSpecs found (by cases selected : profile.advSimd <;> simp only [CodeAt, body, subtractVectorBody, selected] <;> rfl) subtract_vector_specs
    original entered current [left, right] [output] saved _ slots savedLayout args enteredWF homes values state post
  intro m8 s8
  apply subtract_incoming_checked program body method subtractVectorSpecs found
    (by cases selected : profile.advSimd <;> simp only [CodeAt, body, subtractVectorBody, selected] <;> rfl) sse ssse subtract_vector_specs
    original entered m8 [left, right] [output] saved _ slots savedLayout args enteredWF homes values s8 post
  intro m10 s10
  apply subtract_decision_checked program body method found
    (by cases selected : profile.advSimd <;> simp only [CodeAt, body, subtractVectorBody, selected] <;> rfl)
    original entered m10 [left, right] [output] saved _ slots savedLayout args values s10 post
  by_cases fast : subtractPropagation values = BitVec.ofNat 128 0
  · simp only [fast, ite_true]
    obtain ⟨fuel, final, returned, executed, wellFormed, flag, lowRead, highRead, writable, footprint⟩ :=
      subtract_fast_checked program body method subtractVectorSpecs found
        (by cases selected : profile.advSimd <;> simp only [CodeAt, body, subtractVectorBody, selected] <;> rfl) rfl subtract_vector_specs
        original entered m10 [left, right] [output] output saved _ slots savedLayout args call (by simp) outputArg
        homes values s10 owned
    exact ⟨fuel, final, returned, executed,
      subtract_fast_result original final left right output returned fast wellFormed flag lowRead highRead writable footprint⟩
  · simp only [fast, ite_false]
    apply subtract_repair_borrow program body method subtractVectorSpecs found
      borrow storage (by cases selected : profile.advSimd <;> simp only [CodeAt, body, subtractVectorBody, selected] <;> rfl) borrowFound subtract_word_specs
      original entered m10 saved _ slots savedLayout left right output call s10.call s10.preserved homes enteredWF
      s10.authority args leftArg rightArg post
    intro borrowHome results after borrowState
    exact subtract_repair_finish program body method found
      borrow storage (by cases selected : profile.advSimd <;> simp only [CodeAt, body, subtractVectorBody, selected] <;> rfl) storageFound rfl original after saved
      left right output borrowHome results args outputArg call owned borrowState

#print axioms subtract_vector_entry
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Subtract.Safety

/-- Checked invocation of SubtractVector128 with its borrow and storage callees. -/
theorem checked_subtract_vector_contract (program : CIL.Program) (method borrow storage : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractVectorBody profile borrow storage))
    (borrowFound : program[borrow]? = some (borrowBody profile))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (sse : profile.advSimd = false → profile.sse2 = true)
    (ssse : profile.advSimd = false → profile.ssse3 = true)
    (memory : Memory) (left right output : Reference)
    (call : CallingConditions program memory [left, right] [output]) :
    ∃ fuel final values,
      InvocationCertificate program method (binaryArguments left right output) memory fuel final values ∧
      SubtractResult memory final values left right output := by
  let args := binaryArguments left right output
  obtain ⟨frame, entered, slots, setup, layout, homes, _, _⟩ :=
    vector128_frame_setup (subtractVectorBody profile borrow storage) subtractVectorSpecs ⟨rfl, rfl⟩ rfl rfl rfl
      memory args call.1.1
  obtain ⟨fuel, final, returned, executed, result⟩ :=
    subtract_vector_entry program method borrow storage profile found borrowFound storageFound sse ssse
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

#print axioms checked_subtract_vector_contract
end UInt256Proof.Subtract.Profile
