import UInt256.Methods.Subtract.Vector256Steps
import UInt256.Safety.ReportingContract
import CIL.Safety.Certificate
import CIL.Safety.NumericHomes
import UInt256.RepresentationLemmas

namespace UInt256Proof.Subtract.Vector256
open CIL.Safety UInt256Model.Safety

def implSpecs : List NumericLocalSpec :=
  [⟨.vector256, .v256 0, 0, rfl⟩, ⟨.vector256, .v256 0, 0, rfl⟩, ⟨.vector256, .v256 0, 0, rfl⟩,
   ⟨.vector256, .v256 0, 0, rfl⟩, ⟨.vector256, .v256 0, 0, rfl⟩, ⟨.vector256, .v256 0, 0, rfl⟩,
   ⟨.word32, .i32 0, 0, rfl⟩, ⟨.word32, .i32 0, 0, rfl⟩, ⟨.vector256, .v256 0, 0, rfl⟩]

theorem speculative_value (a b : BitVec 256)
    (fast : equalLanes a b &&& borrowIncoming (borrowLanes a b) = 0) : speculative a b = a - b := by
  have result := fast_difference (UInt256Model.decode a) (UInt256Model.decode b)
    (by rwa [UInt256Proof.value_decode, UInt256Proof.value_decode])
  rwa [UInt256Proof.value_decode, UInt256Proof.value_decode] at result

theorem corrected_value (a b : BitVec 256) : corrected a b = a - b := by
  have result := cascade_difference (UInt256Model.decode a) (UInt256Model.decode b)
  rwa [UInt256Proof.value_decode, UInt256Proof.value_decode] at result

theorem fast_flag_bits (a b : BitVec 256)
    (fast : equalLanes a b &&& borrowIncoming (borrowLanes a b) = 0) :
    (if 0#32 < CIL.Vector.moveMask64 (borrowLanes a b) &&& 8#32 then 1#32 else 0#32) =
      if a.toNat < b.toNat then 1#32 else 0#32 := by
  have result := fast_flag_value (UInt256Model.decode a) (UInt256Model.decode b)
    (by rwa [UInt256Proof.value_decode, UInt256Proof.value_decode])
  rwa [UInt256Proof.value_decode, UInt256Proof.value_decode] at result

theorem slow_flag_bits (bmi1 : Bool) (a b : BitVec 256) :
    slowFlag bmi1 (CIL.Vector.moveMask64 (equalLanes a b) + 2 * CIL.Vector.moveMask64 (borrowLanes a b)) =
      if a.toNat < b.toNat then 1#32 else 0#32 := by
  have result := slow_flag_value bmi1 (UInt256Model.decode a) (UInt256Model.decode b)
  rwa [UInt256Proof.value_decode, UInt256Proof.value_decode] at result

/-- AVX2 `SubtractImpl`: the exact initial-operand borrow, the wrapped difference, a writable output and
    unchanged caller bytes outside it, for either borrow-mask form and either flag extraction. -/
theorem impl_contract (program : CIL.Program) (method lookup : Nat) (profile : CIL.FeatureProfile)
    (avx512 bmi1 : Bool) (found : program[method]? = some (subtractImplBody profile avx512 bmi1 lookup))
    (lookupFound : program[lookup]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile))
    (features : ImplProfile profile avx512 bmi1) :
    ReportingBinaryContract (· - ·) (fun left right => decide (left.toNat < right.toNat)) program method := by
  intro memory left right output call
  obtain ⟨frame, entered, setup, live⟩ := call.binary_setup_succeeds
    (body := subtractImplBody profile avx512 bmi1 lookup)
    (by simp [subtractImplBody, FrameSetupFits, InitializersFit, InitializerFits, AggregateArgumentsFit,
      ParameterArgumentsFit, SelectedKindsFit])
  obtain ⟨frame', entered', setup', homes, _, wf⟩ := numeric_frame_setup
    (subtractImplBody profile avx512 bmi1 lookup) implSpecs rfl rfl rfl rfl rfl memory
    (binaryArguments left right output) call.1.1
  rw [setup] at setup'
  cases setup'
  have writable : WritableHomes entered memory.nextIdentity
      (subtractImplBody profile avx512 bmi1 lookup).localKinds frame.locals :=
    UInt256Model.Safety.NumericHomes.writable homes
  have owned : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id := fun id member =>
    ((enterFrame_fresh _ _ _ _ _ setup).2 id member).1
  have state := VectorFrame.initial call setup
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [.scalar (.i32 (if (inputValue memory left).toNat < (inputValue memory right).toNat
      then 1 else 0))] ∧
    inputValue final output = inputValue memory left - inputValue memory right ∧
    access final output 32 1 true = .ok () ∧
    ∀ id, id < memory.nextIdentity → ∀ offset, OutsideOutput output id offset →
      final.cells id offset = memory.cells id offset
  have finished : ∃ fuel final returned,
      run program fuel method 0 (binaryArguments left right output) frame [] entered =
        .ok (final, returned) ∧ post final returned := by
    apply impl_inputs program method lookup profile avx512 bmi1 found features memory entered entered
      left right output frame call writable state post
    intro after state
    apply impl_masks program method lookup profile avx512 bmi1 found features memory entered after
      left right output frame call writable _ _ state post
    intro after state
    apply impl_decision program method lookup profile avx512 bmi1 found features memory entered after
      left right output frame call writable _ _ state post
    · intro fast after state
      apply impl_fast_return program method lookup profile avx512 bmi1 found features memory entered after
        left right output frame _ _ _ state post
      obtain ⟨value, access, footprint⟩ := state.finish call owned
      exact ⟨by rw [fast_flag_bits _ _ fast]; rfl, value.trans (speculative_value _ _ fast), access, footprint⟩
    · intro _ after state
      apply impl_index program method lookup profile avx512 bmi1 found features memory entered after
        left right output frame call writable _ _ _ state post
      intro after state
      apply impl_slow_tail program method lookup profile avx512 bmi1 found lookupFound features memory entered
        after left right output frame call writable _ _ _ state post
      intro after state
      obtain ⟨value, access, footprint⟩ := state.finish call owned
      exact ⟨by rw [slow_flag_bits]; rfl, value.trans (corrected_value _ _), access, footprint⟩
  obtain ⟨fuel, final, returned, ran, flag, value, access, footprint⟩ := finished
  have checked : (binaryArguments left right output).mapM (checkedValue memory) =
      .ok (binaryArguments left right output) := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [binaryArguments, checkedValue, formValue, fl, fr, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  subst flag
  refine ⟨fuel, final, ?_, value, access, footprint⟩
  simpa only [decide_eq_true_eq] using
    certify_invocation program method _ _ memory frame entered fuel final _ found checked setup live ran

#print axioms impl_contract
end UInt256Proof.Subtract.Vector256
