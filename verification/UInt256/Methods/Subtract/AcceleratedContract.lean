import UInt256.Methods.Subtract.ScalarDispatch
import UInt256.Safety.ReportingContract

namespace UInt256Proof.Subtract.Profile
open CIL.Safety

/-- SubtractImpl with AVX2 disabled: the 256-bit block is unreachable, then the scalar dispatcher. -/
def subtractImplBody (profile : CIL.FeatureProfile) (scalarIndex : Nat) : CIL.Method :=
  { profile := profile, returnsValue := true,
    locals := [.v256 0, .v256 0, .v256 0, .v256 0, .v256 0, .v256 0, .i32 0, .i32 0, .v256 0],
    localKinds := [.vector256, .vector256, .vector256, .vector256, .vector256, .vector256, .word32, .word32, .vector256],
    parameterHomes := [], staticSites := [],
    code := [.feature .avx2, .brzero 125] ++ List.replicate 123 subtractScalarUnreachable ++
      [.arg 0, .arg 1, .arg 2, .call scalarIndex 3, .ret (some .unsigned8)] }

def publicSubtractBody (profile : CIL.FeatureProfile) (implIndex : Nat) : CIL.Method :=
  { profile := profile, returnsValue := false, locals := [], localKinds := [], parameterHomes := [], staticSites := [],
    code := [.arg 0, .arg 1, .arg 2, .call implIndex 3, .pop, .ret] }

def publicSubtractUnderflowBody (profile : CIL.FeatureProfile) (implIndex : Nat) : CIL.Method :=
  { profile := profile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [],
    code := [.arg 0, .arg 1, .arg 2, .call implIndex 3, .ret (some .unsigned8)] }
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.Subtract.Safety

/-- Load the three references before the call at `call`, failing nowhere on checked caller views. -/
theorem subtract_forward_prefix (program : CIL.Program) (method : Nat) (body : CIL.Method) (start : Nat)
    (found : program[method]? = some body)
    (arg0 : body.code[start]? = some (.arg 0)) (arg1 : body.code[start + 1]? = some (.arg 1))
    (arg2 : body.code[start + 2]? = some (.arg 2))
    (left right output : Reference) (frame : Frame) (memory : Memory)
    (call : CallingConditions program memory [left, right] [output])
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final values,
      run program fuel method (start + 3) (binaryArguments left right output) frame
        [.reference (.address output), .reference (.address right), .reference (.address left)] memory =
        .ok (final, values) ∧ post final values) :
    ∃ fuel final values,
      run program fuel method start (binaryArguments left right output) frame [] memory =
        .ok (final, values) ∧ post final values := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  apply run_next_exists post found arg0 (by
    simp [step, cil_guard, observerCount, binaryArguments, checkedValue, formValue, fl, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]; exact ⟨rfl, rfl, rfl, rfl⟩)
  apply run_next_exists post found arg1 (by
    simp [step, cil_guard, observerCount, binaryArguments, checkedValue, formValue, fr, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]; exact ⟨rfl, rfl, rfl, rfl⟩)
  apply run_next_exists post found arg2 (by
    simp [step, cil_guard, observerCount, binaryArguments, checkedValue, formValue, fo, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]; exact ⟨rfl, rfl, rfl, rfl⟩)
  exact continuation

/-- A byte-flag return retires the frame and forwards the flag. -/
theorem subtract_flag_return (program : CIL.Program) (method : Nat) (body : CIL.Method) (pc : Nat)
    (found : program[method]? = some body) (returns : body.returnsValue = true)
    (fetched : body.code[pc]? = some (.ret (some .unsigned8)))
    (args : List Value) (frame : Frame) (memory : Memory) (left right : Memory) (l r : Reference) :
    run program 1 method pc args frame [.scalar (.i32 (subtractUnderflow left l r))] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (subtractUnderflow left l r))]) := by
  unfold subtractUnderflow
  split <;> simp [run, found, fetched, returns, step, cil_guard, observerCount, checkedValue, numericValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] <;> rfl

#print axioms subtract_forward_prefix
#print axioms subtract_flag_return
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.Subtract.Safety

/-- A callee result over entered caller bytes becomes the caller-level result after frame retirement. -/
theorem subtract_forward_result (program : CIL.Program) (body : CIL.Method) (memory entered after : Memory)
    (frame : Frame) (left right output : Reference) (args : List Value)
    (call : CallingConditions program memory [left, right] [output])
    (setup : enterFrame body args memory = .ok (frame, entered))
    (result : SubtractResult entered after [.scalar (.i32 (subtractUnderflow entered left right))] left right output) :
    subtractUnderflow entered left right = subtractUnderflow memory left right ∧
    inputValue (leaveFrame frame after) output = inputValue memory left - inputValue memory right ∧
    access (leaveFrame frame after) output 32 1 true = .ok () ∧
    ∀ id, id < memory.nextIdentity → ∀ offset, OutsideOutput output id offset →
      (leaveFrame frame after).cells id offset = memory.cells id offset := by
  have inputSame : ∀ reference ∈ [left, right], inputValue entered reference = inputValue memory reference := by
    intro reference member
    exact call.input_value_after_setup setup member
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have retained := leaveFrame_preserves_memory_below frame after memory.nextIdentity
    (fun id member => (fresh.2 id member).1)
  have before := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed (by simp : output ∈ [output]))
  have old := (call.1.1.1 _ _ present).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [subtractUnderflow, inputSame left (by simp), inputSame right (by simp)]
  · have bytes : (fun offset => ((leaveFrame frame after).cells output.allocation offset).bits) =
        (fun offset => (after.cells output.allocation offset).bits) := by
      funext offset
      rw [retained.cells output.allocation old offset]
    have math := result.value
    rw [inputSame left (by simp), inputSame right (by simp)] at math
    simpa only [inputValue, bytes] using math
  · exact (retained.access output old 32 1 true).trans result.writable
  · intro id bound offset outside
    exact (retained.cells id bound offset).trans
      ((result.footprint id (Nat.lt_of_lt_of_le bound fresh.1.next) offset outside).trans (before.cells id bound offset))

theorem subtract_checked_arguments (program : CIL.Program) (memory : Memory) (left right output : Reference)
    (call : CallingConditions program memory [left, right] [output]) :
    (binaryArguments left right output).mapM (checkedValue memory) = .ok (binaryArguments left right output) := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  simp [binaryArguments, checkedValue, formValue, fl, fr, fo, checkedAt,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- SubtractImpl with AVX2 disabled forwards the dispatcher's exact result. -/
theorem subtract_impl_contract (program : CIL.Program) (method scalarIndex : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (subtractImplBody profile scalarIndex)) (noAvx2 : profile.avx2 = false)
    (scalarChecked : ∀ memory left right output,
      CallingConditions program memory [left, right] [output] →
      ∃ fuel final values,
        invoke program fuel scalarIndex (binaryArguments left right output) memory = .ok (final, values) ∧
        SubtractResult memory final values left right output) :
    ReportingBinaryContract (· - ·) (fun left right => decide (left.toNat < right.toNat)) program method := by
  intro memory left right output call
  have fits : FrameSetupFits (subtractImplBody profile scalarIndex) (binaryArguments left right output) := by
    simp [subtractImplBody, FrameSetupFits, InitializersFit, InitializerFits, AggregateArgumentsFit, ParameterArgumentsFit, SelectedKindsFit]
  obtain ⟨frame, entered, setup, live⟩ := call.binary_setup_succeeds fits
  have enteredCall := call.after_frame_setup setup
  obtain ⟨childFuel, after, values, invoked, result⟩ := scalarChecked entered left right output enteredCall
  have flagEq := result.flag
  subst flagEq
  have fl := enteredCall.input_formed (reference := left) (by simp)
  have fr := enteredCall.input_formed (reference := right) (by simp)
  have fo := enteredCall.output_formed (reference := output) (by simp)
  have stepped : step (subtractImplBody profile scalarIndex) (.call scalarIndex 3) 128
      (binaryArguments left right output) frame
      [.reference (.address output), .reference (.address right), .reference (.address left)]
      entered = .ok (.call scalarIndex (binaryArguments left right output) [] entered) := by
    simp [step, cil_guard, observerCount, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, invoked⟩
    ⟨1, subtract_flag_return program method _ 129 found rfl (by rfl) _ frame after entered entered left right⟩
  let post : Memory → List Value → Prop := fun final values =>
    final = leaveFrame frame after ∧ values = [.scalar (.i32 (subtractUnderflow entered left right))]
  have guarded : ∃ fuel final values,
      run program fuel method 0 (binaryArguments left right output) frame [] entered =
        .ok (final, values) ∧ post final values := by
    have bodyProfile : (subtractImplBody profile scalarIndex).profile = profile := rfl
    apply run_next_exists post found (by rfl) (by
      simp [step, cil_guard, observerCount, bodyProfile, noAvx2, pureArity, scalars, CIL.step.eq_def, CIL.FeatureProfile.evaluate,
        Bind.bind, Except.bind, Pure.pure, Except.pure]; try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))
    apply run_next_exists post found (by rfl) (by
      simp [step, cil_guard, observerCount, checkedValue, numericValue, pureArity, scalars, CIL.step.eq_def, CIL.truth,
        Bind.bind, Except.bind, Pure.pure, Except.pure]; try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))
    exact subtract_forward_prefix program method _ 125 found (by rfl) (by rfl) (by rfl) left right output frame entered
      enteredCall post ⟨tailFuel, _, _, tail, rfl, rfl⟩
  obtain ⟨fuel, final, values, finished, sameFinal, sameValues⟩ := guarded
  subst final
  subst values
  obtain ⟨flagSame, value, writable, footprint⟩ :=
    subtract_forward_result program _ memory entered after frame left right output _ call setup result
  rw [flagSame] at finished
  refine ⟨fuel, leaveFrame frame after, ?_, value, writable, footprint⟩
  simpa only [subtractUnderflow, decide_eq_true_eq] using
    certify_invocation _ _ _ _ _ _ _ _ _ _ found (subtract_checked_arguments program memory left right output call)
      setup live finished

#print axioms subtract_forward_result
#print axioms subtract_checked_arguments
#print axioms subtract_impl_contract
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.Subtract.Safety

theorem subtract_reporting_invoke {program : CIL.Program} {impl : Nat}
    (reporting : ReportingBinaryContract (· - ·) (fun a b => decide (a.toNat < b.toNat)) program impl)
    (memory : Memory) (left right output : Reference)
    (call : CallingConditions program memory [left, right] [output]) :
    ∃ fuel after, invoke program fuel impl (binaryArguments left right output) memory =
        .ok (after, [.scalar (.i32 (subtractUnderflow memory left right))]) ∧
      SubtractResult memory after [.scalar (.i32 (subtractUnderflow memory left right))] left right output := by
  obtain ⟨fuel, after, certificate, value, writable, footprint⟩ := reporting memory left right output call
  refine ⟨fuel, after, ?_, ⟨invoke_preserves_wellFormed _ _ _ _ _ _ _ call.1.1 certificate.1, value, rfl, writable, footprint⟩⟩
  simpa only [subtractUnderflow, decide_eq_true_eq] using certificate.1

/-- Public Subtract discards the forwarded flag and keeps the wrapping difference. -/
theorem subtract_wrapping_contract (program : CIL.Program) (method impl : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (publicSubtractBody profile impl))
    (reporting : ReportingBinaryContract (· - ·) (fun a b => decide (a.toNat < b.toNat)) program impl) :
    WrappingBinaryContract (· - ·) program method := by
  intro memory left right output call
  have fits : FrameSetupFits (publicSubtractBody profile impl) (binaryArguments left right output) := by
    simp [publicSubtractBody, FrameSetupFits, InitializersFit, InitializerFits, AggregateArgumentsFit, ParameterArgumentsFit, SelectedKindsFit]
  obtain ⟨frame, entered, setup, live⟩ := call.binary_setup_succeeds fits
  have enteredCall := call.after_frame_setup setup
  obtain ⟨childFuel, after, invoked, result⟩ := subtract_reporting_invoke reporting entered left right output enteredCall
  have fl := enteredCall.input_formed (reference := left) (by simp)
  have fr := enteredCall.input_formed (reference := right) (by simp)
  have fo := enteredCall.output_formed (reference := output) (by simp)
  have stepped : step (publicSubtractBody profile impl) (.call impl 3) 3
      (binaryArguments left right output) frame
      [.reference (.address output), .reference (.address right), .reference (.address left)]
      entered = .ok (.call impl (binaryArguments left right output) [] entered) := by
    simp [step, cil_guard, observerCount, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have returned : run program 2 method 4 (binaryArguments left right output) frame
      [.scalar (.i32 (subtractUnderflow entered left right))] after = .ok (leaveFrame frame after, []) := by
    have returns : (publicSubtractBody profile impl).returnsValue = false := rfl
    apply Eq.trans
    · apply run_next found (by rfl)
      simp [step, cil_guard, observerCount, pureArity, scalars, CIL.step, checkedValue, instruction, Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · rw [run]
      simp [found, publicSubtractBody, step, cil_guard, observerCount, checkedValue, numericValue,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, invoked⟩ ⟨2, returned⟩
  let post : Memory → List Value → Prop := fun final values => final = leaveFrame frame after ∧ values = []
  obtain ⟨fuel, final, values, finished, sameFinal, sameValues⟩ :=
    subtract_forward_prefix program method _ 0 found (by rfl) (by rfl) (by rfl) left right output frame entered
      enteredCall post ⟨tailFuel, _, _, tail, rfl, rfl⟩
  subst final
  subst values
  obtain ⟨_, value, writable, footprint⟩ :=
    subtract_forward_result program _ memory entered after frame left right output _ call setup result
  exact ⟨fuel, leaveFrame frame after,
    certify_invocation _ _ _ _ _ _ _ _ _ _ found (subtract_checked_arguments program memory left right output call)
      setup live finished, value, writable, footprint⟩

/-- Public SubtractUnderflow forwards the exact underflow flag and the wrapping difference. -/
theorem subtract_underflow_contract (program : CIL.Program) (method impl : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (publicSubtractUnderflowBody profile impl))
    (reporting : ReportingBinaryContract (· - ·) (fun a b => decide (a.toNat < b.toNat)) program impl) :
    ReportingBinaryContract (· - ·) (fun a b => decide (a.toNat < b.toNat)) program method := by
  intro memory left right output call
  have fits : FrameSetupFits (publicSubtractUnderflowBody profile impl) (binaryArguments left right output) := by
    simp [publicSubtractUnderflowBody, FrameSetupFits, InitializersFit, InitializerFits, AggregateArgumentsFit,
      ParameterArgumentsFit, SelectedKindsFit]
  obtain ⟨frame, entered, setup, live⟩ := call.binary_setup_succeeds fits
  have enteredCall := call.after_frame_setup setup
  obtain ⟨childFuel, after, invoked, result⟩ := subtract_reporting_invoke reporting entered left right output enteredCall
  have fl := enteredCall.input_formed (reference := left) (by simp)
  have fr := enteredCall.input_formed (reference := right) (by simp)
  have fo := enteredCall.output_formed (reference := output) (by simp)
  have stepped : step (publicSubtractUnderflowBody profile impl) (.call impl 3) 3
      (binaryArguments left right output) frame
      [.reference (.address output), .reference (.address right), .reference (.address left)]
      entered = .ok (.call impl (binaryArguments left right output) [] entered) := by
    simp [step, cil_guard, observerCount, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, invoked⟩
    ⟨1, subtract_flag_return program method _ 4 found rfl (by rfl) _ frame after entered entered left right⟩
  let post : Memory → List Value → Prop := fun final values =>
    final = leaveFrame frame after ∧ values = [.scalar (.i32 (subtractUnderflow entered left right))]
  obtain ⟨fuel, final, values, finished, sameFinal, sameValues⟩ :=
    subtract_forward_prefix program method _ 0 found (by rfl) (by rfl) (by rfl) left right output frame entered
      enteredCall post ⟨tailFuel, _, _, tail, rfl, rfl⟩
  subst final
  subst values
  obtain ⟨flagSame, value, writable, footprint⟩ :=
    subtract_forward_result program _ memory entered after frame left right output _ call setup result
  rw [flagSame] at finished
  refine ⟨fuel, leaveFrame frame after, ?_, value, writable, footprint⟩
  simpa only [subtractUnderflow, decide_eq_true_eq] using
    certify_invocation _ _ _ _ _ _ _ _ _ _ found (subtract_checked_arguments program memory left right output call)
      setup live finished

#print axioms subtract_reporting_invoke
#print axioms subtract_wrapping_contract
#print axioms subtract_underflow_contract
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.Subtract.Safety

/-- SubtractImpl over the 128-bit accelerated dispatcher (AdvSimd, or SSE4.2 without it). -/
theorem checked_accelerated_impl_contract (program : CIL.Program) (impl scalar vector borrow small storage : Nat)
    (profile : CIL.FeatureProfile) (noAvx2 : profile.avx2 = false)
    (sse : profile.advSimd = false → profile.sse2 = true)
    (ssse : profile.advSimd = false → profile.ssse3 = true)
    (sse42 : profile.advSimd = false → profile.sse42 = true)
    (implFound : program[impl]? = some (subtractImplBody profile scalar))
    (scalarFound : program[scalar]? = some (subtractScalarBody profile vector small))
    (vectorFound : program[vector]? = some (subtractVectorBody profile borrow storage))
    (borrowFound : program[borrow]? = some (borrowBody profile))
    (smallFound : program[small]? = some (subtractSmallBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile)) :
    ReportingBinaryContract (· - ·) (fun a b => decide (a.toNat < b.toNat)) program impl := by
  apply subtract_impl_contract program impl scalar profile implFound noAvx2
  intro memory left right output call
  obtain ⟨fuel, final, values, certified, result⟩ :=
    checked_subtract_scalar_contract program scalar vector small borrow storage profile scalarFound vectorFound
      smallFound borrowFound storageFound sse ssse sse42 memory left right output call
  exact ⟨fuel, final, values, certified.1, result⟩

theorem checked_accelerated_subtract_contract (program : CIL.Program) (entry impl scalar vector borrow small storage : Nat)
    (profile : CIL.FeatureProfile) (noAvx2 : profile.avx2 = false)
    (sse : profile.advSimd = false → profile.sse2 = true)
    (ssse : profile.advSimd = false → profile.ssse3 = true)
    (sse42 : profile.advSimd = false → profile.sse42 = true)
    (entryFound : program[entry]? = some (publicSubtractBody profile impl))
    (implFound : program[impl]? = some (subtractImplBody profile scalar))
    (scalarFound : program[scalar]? = some (subtractScalarBody profile vector small))
    (vectorFound : program[vector]? = some (subtractVectorBody profile borrow storage))
    (borrowFound : program[borrow]? = some (borrowBody profile))
    (smallFound : program[small]? = some (subtractSmallBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile)) :
    WrappingBinaryContract (· - ·) program entry :=
  subtract_wrapping_contract program entry impl profile entryFound
    (checked_accelerated_impl_contract program impl scalar vector borrow small storage profile noAvx2 sse ssse sse42
      implFound scalarFound vectorFound borrowFound smallFound storageFound)

theorem checked_accelerated_underflow_contract (program : CIL.Program) (entry impl scalar vector borrow small storage : Nat)
    (profile : CIL.FeatureProfile) (noAvx2 : profile.avx2 = false)
    (sse : profile.advSimd = false → profile.sse2 = true)
    (ssse : profile.advSimd = false → profile.ssse3 = true)
    (sse42 : profile.advSimd = false → profile.sse42 = true)
    (entryFound : program[entry]? = some (publicSubtractUnderflowBody profile impl))
    (implFound : program[impl]? = some (subtractImplBody profile scalar))
    (scalarFound : program[scalar]? = some (subtractScalarBody profile vector small))
    (vectorFound : program[vector]? = some (subtractVectorBody profile borrow storage))
    (borrowFound : program[borrow]? = some (borrowBody profile))
    (smallFound : program[small]? = some (subtractSmallBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile)) :
    ReportingBinaryContract (· - ·) (fun a b => decide (a.toNat < b.toNat)) program entry :=
  subtract_underflow_contract program entry impl profile entryFound
    (checked_accelerated_impl_contract program impl scalar vector borrow small storage profile noAvx2 sse ssse sse42
      implFound scalarFound vectorFound borrowFound smallFound storageFound)

#print axioms checked_accelerated_impl_contract
#print axioms checked_accelerated_subtract_contract
#print axioms checked_accelerated_underflow_contract
end UInt256Proof.Subtract.Profile
