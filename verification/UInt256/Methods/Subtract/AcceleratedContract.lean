import UInt256.Methods.Subtract.ScalarDispatch
import UInt256.Safety.ReportingForwarder

/-! Public Subtract and SubtractUnderflow over the 128-bit accelerated dispatcher: the entry
    wrappers and SubtractImpl forward the dispatcher's exact difference and underflow flag. -/

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

/-- SubtractImpl over the 128-bit accelerated dispatcher (AdvSimd, or SSE4.2 without it):
    with AVX2 disabled it skips the 256-bit block and forwards the dispatcher's exact result. -/
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
  intro memory left right output call
  have fits : FrameSetupFits (subtractImplBody profile scalar)
      (binaryArguments left right output) := by
    simp [subtractImplBody, FrameSetupFits, InitializersFit, InitializerFits,
      AggregateArgumentsFit, ParameterArgumentsFit]
  obtain ⟨frame, entered, setup, _⟩ := call.binary_setup_succeeds fits
  have enteredCall := call.after_frame_setup setup
  obtain ⟨childFuel, after, values, certified, result⟩ :=
    checked_subtract_scalar_contract program scalar vector small borrow storage profile
      scalarFound vectorFound smallFound borrowFound storageFound sse ssse sse42
      entered left right output enteredCall
  obtain rfl := result.flag
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have forwarded := run_call_post
    (post := fun final returned => SubtractResult memory final returned left right output)
    implFound (pc := 128) (args := binaryArguments left right output) (by rfl)
    (step_call_loaded enteredCall.binary_arguments_valid rfl) ⟨childFuel, certified.1⟩
    (run_return_exists implFound (by rfl)
      (step_return_unchanged (narrow := some .unsigned8) rfl rfl rfl
        ⟨_, rfl, CIL.NarrowKind.extend_ite_one_zero _ _⟩) rfl
      (subtract_result_retire call (enterFrame_preserves_caller_memory _ _ _ _ _ setup).cells
        fresh.1.next (fun id member => (fresh.2 id member).1) result))
  have executed : ∃ fuel final returned,
      run program fuel impl 0 (binaryArguments left right output) frame [] entered =
        .ok (final, returned) ∧ SubtractResult memory final returned left right output := by
    cil_contract_steps [implFound, noAvx2, binaryArguments,
      enteredCall.input_formed (reference := left) (by simp),
      enteredCall.input_formed (reference := right) (by simp),
      enteredCall.output_formed (reference := output) (by simp)] until forwarded
  obtain ⟨fuel, final, returned, ran, retired⟩ := executed
  obtain rfl := retired.flag
  refine ⟨fuel, final, ?_, retired.value, retired.writable, retired.footprint⟩
  simpa only [subtractUnderflow, decide_eq_true_eq] using
    InvocationCertificate.of_invoke call.1.wellFormed call.2
      (invoke_of_run implFound (checkedValues_of_valid call.binary_arguments_valid) setup ran)
/-- Public Subtract discards the forwarded flag and keeps the wrapping difference. -/
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
  forward_reporting_pop program entry impl _ _ _ entryFound rfl rfl rfl rfl rfl rfl
    (checked_accelerated_impl_contract program impl scalar vector borrow small storage profile noAvx2 sse ssse sse42
      implFound scalarFound vectorFound borrowFound smallFound storageFound)

/-- Public SubtractUnderflow forwards the exact underflow flag and the wrapping difference. -/
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
  forward_reporting_byte program entry impl _ _ _ entryFound rfl rfl rfl rfl rfl rfl
    (checked_accelerated_impl_contract program impl scalar vector borrow small storage profile noAvx2 sse ssse sse42
      implFound scalarFound vectorFound borrowFound smallFound storageFound)

end UInt256Proof.Subtract.Profile
