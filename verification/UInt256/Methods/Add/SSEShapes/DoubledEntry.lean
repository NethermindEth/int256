import UInt256.Methods.Add.ARMContract
set_option maxRecDepth 4096

namespace UInt256Proof.Add.SSEShapes
open CIL.Safety UInt256Model.Safety UInt256Proof.Add.Safety

/-- Public Add whose AVX2 guard tests the feature twice. -/
def doubledScalarBody (profile : CIL.FeatureProfile) (scalarIndex : Nat) : CIL.Method := { profile := profile, returnsValue := false, locals := [.v256 0, .v256 0, .v256 0, .v256 0], localKinds := [.vector256, .vector256, .vector256, .vector256], parameterHomes := [], staticSites := [], code := [
  .feature .avx2,
  .feature .avx2,
  .band,
  .brzero 27,
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .arg 0,
  .arg 1,
  .arg 2,
  .const32 0,
  .call scalarIndex 4,
  .pop,
  .ret] }

theorem doubled_entry_prefix (program : CIL.Program) (method scalarIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (doubledScalarBody profile scalarIndex)) (disabled : profile.avx2 = false) (left right output : Reference) (frame : Frame) (memory : CIL.Safety.Memory)
  (call : CallingConditions program memory [left, right] [output])
  (post : CIL.Safety.Memory → List Value → Prop)
  (continuation : ∃ fuel final values,
    run program fuel method 31 (binaryArguments left right output)
      frame [.scalar (.i32 0), .reference (.address output), .reference (.address right),
        .reference (.address left)] memory = .ok (final, values) ∧ post final values) :
  ∃ fuel final values,
    run program fuel method 0 (binaryArguments left right output)
      frame [] memory = .ok (final, values) ∧ post final values := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  repeat'
    first
    | exact continuation
    | simp (config := { failIfUnchanged := false })
      apply run_next_exists post
      · simp only [found, doubledScalarBody, disabled]; rfl
      · simp only [found, doubledScalarBody, disabled]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [found, doubledScalarBody, disabled, binaryArguments, step, checkedValue, numericValue, formValue, fl, fr, fo,
            pureArity, scalars, CIL.step.eq_def, CIL.binary, CIL.truth, CIL.FeatureProfile.evaluate, checkedAt, Except.mapError,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
        try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

theorem doubled_entry_return (program : CIL.Program) (method scalarIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (doubledScalarBody profile scalarIndex)) (disabled : profile.avx2 = false) (args : List Value) (flag : BitVec 32) (frame : Frame) (memory : CIL.Safety.Memory) :
  run program 2 method (31 + 1) args frame [.scalar (.i32 flag)] memory =
    .ok (leaveFrame frame memory, []) := by
  simp only [Nat.reduceAdd]
  apply Eq.trans
  · apply run_next
    · simp only [found, doubledScalarBody, disabled]; rfl
    · simp only [found, doubledScalarBody, disabled]; rfl
    · simp [step, pureArity, instruction, Bind.bind, Except.bind, Pure.pure, Except.pure]
      try exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [run]
    simp [found, doubledScalarBody, disabled, step, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Complete the public feature guard, certified dispatcher invocation and discarded scalar return, leaving only the public postcondition to discharge. -/
theorem doubled_entry_dispatch (program : CIL.Program) (method scalarIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (doubledScalarBody profile scalarIndex)) (disabled : profile.avx2 = false)
    (child : ∀ memory left right output,
      CallingConditions program memory [left, right] [output] →
      ∃ fuel final returned,
        InvocationCertificate program scalarIndex
          (binaryArguments left right output ++ [.scalar (.i32 0)]) memory fuel final returned ∧
        ARMScalarReportingPost memory final returned left right output 0)
  (memory : Memory) (frame : Frame) (left right output : Reference)
  (call : CallingConditions program memory [left, right] [output])
  (post : Memory → List Value → Prop)
  (continuation : ∀ childFuel final returned,
    InvocationCertificate program scalarIndex
      ((binaryArguments left right output ++ [.scalar (.i32 0)])) memory childFuel final returned →
    ARMScalarPost memory final returned left right output →
    post (leaveFrame frame final) []) :
  ∃ fuel final returned,
    run program fuel method 0 (binaryArguments left right output)
      frame [] memory = .ok (final, returned) ∧ post final returned := by
  apply doubled_entry_prefix program method scalarIndex profile found disabled left right output frame memory call post
  obtain ⟨childFuel, final, returned, certified, result⟩ :=
    child memory left right output call
  obtain ⟨returnedFlag, shape⟩ := result.scalar
  subst returned
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  have fetched : (doubledScalarBody profile scalarIndex).code[31]? = some (.call scalarIndex 4) := by rfl
  have stepped : step (doubledScalarBody profile scalarIndex) (.call scalarIndex 4) 31
      (binaryArguments left right output) frame
      [.scalar (.i32 0), .reference (.address output), .reference (.address right), .reference (.address left)] memory =
        .ok (.call scalarIndex ((binaryArguments left right output ++ [.scalar (.i32 0)])) [] memory) := by
    simp [step, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨fuel, executed⟩ := run_call_exists found fetched stepped ⟨childFuel, certified.1⟩
    ⟨2, doubled_entry_return program method scalarIndex profile found disabled (binaryArguments left right output) returnedFlag frame final⟩
  exact ⟨fuel, leaveFrame frame final, [], executed,
    continuation childFuel final [.scalar (.i32 returnedFlag)] certified result.toARMScalarPost⟩

/-- Public Add with a doubled AVX2 guard through its scalar dispatcher preserves checked execution, initial-input modular arithmetic, normal void return, writable output and all caller bytes outside output. -/
theorem doubled_add_contract_of_scalar (program : CIL.Program) (method scalarIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (doubledScalarBody profile scalarIndex)) (disabled : profile.avx2 = false)
    (child : ∀ memory left right output,
      CallingConditions program memory [left, right] [output] →
      ∃ fuel final returned,
        InvocationCertificate program scalarIndex
          (binaryArguments left right output ++ [.scalar (.i32 0)]) memory fuel final returned ∧
        ARMScalarReportingPost memory final returned left right output 0) :
    WrappingBinaryContract (· + ·) program method := by
  intro memory left right output call
  obtain ⟨frame, entered, setup, live⟩ := call.binary_setup_succeeds
    (body := doubledScalarBody profile scalarIndex)
    (by simp [doubledScalarBody, FrameSetupFits, InitializersFit, InitializerFits, AggregateArgumentsFit, ParameterArgumentsFit])
  have enteredCall := call.after_frame_setup setup
  have preserved := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [] ∧
    inputValue final output = inputValue memory left + inputValue memory right ∧
    access final output 32 1 true = .ok () ∧
    ∀ id, id < memory.nextIdentity → ∀ offset, OutsideOutput output id offset →
      final.cells id offset = memory.cells id offset
  have finish : ∃ fuel final returned,
      run program fuel method 0 (binaryArguments left right output)
        frame [] entered = .ok (final, returned) ∧ post final returned := by
    apply doubled_entry_dispatch program method scalarIndex profile found disabled child entered frame left right output enteredCall post
    intro childFuel final returned certified result
    have sum := result.value
    rw [call.input_value_after_setup setup (by simp : left ∈ [left, right]),
      call.input_value_after_setup setup (by simp : right ∈ [left, right])] at sum
    have retired := arm_scalar_retire memory entered final frame left right output returned
      call preserved fresh.1.next (fun id member => (fresh.2 id member).1)
      result.wellFormed sum result.scalar result.writable result.footprint
    exact ⟨rfl, retired.value, retired.writable, retired.footprint⟩
  obtain ⟨fuel, final, returned, executed, same, value, writable, footprint⟩ := finish
  subst returned
  have checked : (binaryArguments left right output).mapM (checkedValue memory) =
      .ok (binaryArguments left right output) := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [binaryArguments, checkedValue, formValue, fl, fr, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have certified := certify_invocation program method (doubledScalarBody profile scalarIndex)
    (binaryArguments left right output) memory frame entered fuel final []
    found checked setup live executed
  exact ⟨fuel, final, certified, value, writable, footprint⟩

#print axioms doubled_entry_prefix
#print axioms doubled_entry_return
#print axioms doubled_entry_dispatch
#print axioms doubled_add_contract_of_scalar
end UInt256Proof.Add.SSEShapes
