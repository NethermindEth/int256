import UInt256.Methods.Add.ARMScalarEntry
set_option maxRecDepth 4096

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety
def publicScalarBody (profile : CIL.FeatureProfile) (scalarIndex : Nat) : CIL.Method := { profile := profile, returnsValue := false, locals := [.v256 0, .v256 0, .v256 0, .v256 0], localKinds := [.vector256, .vector256, .vector256, .vector256], parameterHomes := [], staticSites := [], code := [
  .feature .avx2,
  .brzero 25,
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

theorem scalar_entry_prefix (program : CIL.Program) (method scalarIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (publicScalarBody profile scalarIndex)) (disabled : profile.avx2 = false) (left right output : Reference) (frame : Frame) (memory : CIL.Safety.Memory)
  (call : CallingConditions program memory [left, right] [output])
  (post : CIL.Safety.Memory → List Value → Prop)
  (continuation : ∃ fuel final values,
    run program fuel method 29 (binaryArguments left right output)
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
      · simp only [found, publicScalarBody, disabled]; rfl
      · simp only [found, publicScalarBody, disabled]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [found, publicScalarBody, disabled, binaryArguments, step, cil_guard, observerCount, checkedValue, numericValue, formValue, fl, fr, fo,
            pureArity, scalars, CIL.step.eq_def, CIL.truth, CIL.FeatureProfile.evaluate, checkedAt, Except.mapError,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
        try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

theorem scalar_entry_return (program : CIL.Program) (method scalarIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (publicScalarBody profile scalarIndex)) (disabled : profile.avx2 = false) (args : List Value) (flag : BitVec 32) (frame : Frame) (memory : CIL.Safety.Memory) :
  run program 2 method (29 + 1) args frame [.scalar (.i32 flag)] memory =
    .ok (leaveFrame frame memory, []) := by
  simp only [Nat.reduceAdd]
  apply Eq.trans
  · apply run_next
    · simp only [found, publicScalarBody, disabled]; rfl
    · simp only [found, publicScalarBody, disabled]; rfl
    · simp [step, cil_guard, observerCount, pureArity, instruction, Bind.bind, Except.bind, Pure.pure, Except.pure]
      try exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [run]
    simp [found, publicScalarBody, disabled, step, cil_guard, observerCount, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Complete the public feature guard, certified dispatcher invocation and discarded scalar return, leaving only the public postcondition to discharge. -/
theorem scalar_entry_dispatch (program : CIL.Program) (method scalarIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (publicScalarBody profile scalarIndex)) (disabled : profile.avx2 = false)
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
  apply scalar_entry_prefix program method scalarIndex profile found disabled left right output frame memory call post
  obtain ⟨childFuel, final, returned, certified, result⟩ :=
    child memory left right output call
  obtain ⟨returnedFlag, shape⟩ := result.scalar
  subst returned
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  have fetched : (publicScalarBody profile scalarIndex).code[29]? = some (.call scalarIndex 4) := by rfl
  have stepped : step (publicScalarBody profile scalarIndex) (.call scalarIndex 4) 29
      (binaryArguments left right output) frame
      [.scalar (.i32 0), .reference (.address output), .reference (.address right), .reference (.address left)] memory =
        .ok (.call scalarIndex ((binaryArguments left right output ++ [.scalar (.i32 0)])) [] memory) := by
    simp [step, cil_guard, observerCount, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨fuel, executed⟩ := run_call_exists found fetched stepped ⟨childFuel, certified.1⟩
    ⟨2, scalar_entry_return program method scalarIndex profile found disabled (binaryArguments left right output) returnedFlag frame final⟩
  exact ⟨fuel, leaveFrame frame final, [], executed,
    continuation childFuel final [.scalar (.i32 returnedFlag)] certified result.toARMScalarPost⟩

#print axioms scalar_entry_dispatch

#print axioms scalar_entry_prefix
#print axioms scalar_entry_return
end UInt256Proof.Add.Safety
namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- Public Add through its scalar dispatcher preserves checked execution, initial-input modular arithmetic, normal void return, writable output and all caller bytes outside output. -/
theorem add_contract_of_scalar (program : CIL.Program) (method scalarIndex : Nat) (profile : CIL.FeatureProfile) (found : program[method]? = some (publicScalarBody profile scalarIndex)) (disabled : profile.avx2 = false)
    (child : ∀ memory left right output,
      CallingConditions program memory [left, right] [output] →
      ∃ fuel final returned,
        InvocationCertificate program scalarIndex
          (binaryArguments left right output ++ [.scalar (.i32 0)]) memory fuel final returned ∧
        ARMScalarReportingPost memory final returned left right output 0) :
    WrappingBinaryContract (· + ·) program method := by
  intro memory left right output call
  obtain ⟨frame, entered, setup, live⟩ := call.binary_setup_succeeds
    (body := publicScalarBody profile scalarIndex)
    (by simp [publicScalarBody, FrameSetupFits, InitializersFit, InitializerFits, AggregateArgumentsFit, ParameterArgumentsFit, SelectedKindsFit])
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
    apply scalar_entry_dispatch program method scalarIndex profile found disabled child entered frame left right output enteredCall post
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
  have certified := certify_invocation program method (publicScalarBody profile scalarIndex)
    (binaryArguments left right output) memory frame entered fuel final []
    found checked setup live executed
  exact ⟨fuel, final, certified, value, writable, footprint⟩

#print axioms add_contract_of_scalar
end UInt256Proof.Add.Safety
namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

theorem checked_arm_add_contract (program : CIL.Program) (entry scalar vector small storage : Nat)
    (profile : CIL.FeatureProfile) (enabled : profile.advSimd = true) (disabled : profile.avx2 = false)
    (entryFound : program[entry]? = some (publicScalarBody profile scalar))
    (scalarFound : program[scalar]? = some (armScalarBody profile vector small))
    (vectorFound : program[vector]? = some (armBody profile))
    (smallFound : program[small]? = some (armSmallBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile)) :
    WrappingBinaryContract (· + ·) program entry := by
  apply add_contract_of_scalar program entry scalar profile entryFound disabled
  intro memory left right output call
  simpa only [vector128Arguments, binaryArguments, List.cons_append, List.nil_append] using
    checked_arm_scalar_contract program scalar vector small storage profile scalarFound vectorFound smallFound storageFound enabled
      memory left right output 0 rfl call
#print axioms checked_arm_add_contract
end UInt256Proof.Add.Safety
