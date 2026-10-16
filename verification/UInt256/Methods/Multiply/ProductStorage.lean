import UInt256.Methods.Multiply.LimbStorage
import UInt256.Methods.Multiply.ProductStorageContract
import CIL.Safety.CallComposition

namespace UInt256Proof.Multiply.ProductStorage
open CIL.Safety UInt256Model.Safety

def body (profile : CIL.FeatureProfile) (callee : Nat) : CIL.Method :=
  { profile := profile, returnsValue := false, locals := [], code := [
    .feature .vector256Accelerated, .brzero 13,
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
    .arg 0, .arg 1, .arg 2, .arg 3, .arg 4, .call callee 5, .ret] }

/-- Scalar product storage reuses the checked four-limb writer. Its
  route also checks its feature branch, forwarding call and empty-frame return. -/
theorem store_product_contract (profile : CIL.FeatureProfile) (scalar : profile.vector256Accelerated = false)
  (program : CIL.Program) (index callee : Nat)
  (found : program[index]? = some (body profile callee))
  (childFound : program[callee]? = some (LimbStorage.body profile))
  (memory : Memory) (inputs : List Reference) (output : Reference)
  (w0 w1 w2 w3 : BitVec 64)
  (call : CallingConditions program memory inputs [output]) :
  ∃ fuel result,
    invoke program fuel index
      [.reference (.address output), .scalar (.i64 w0), .scalar (.i64 w1), .scalar (.i64 w2), .scalar (.i64 w3)]
      memory = .ok (result, []) ∧
    CallingConditions program result inputs [output] ∧
    (∀ id offset, OutsideOutput output id offset → result.cells id offset = memory.cells id offset) ∧
    AccessBelow memory.nextIdentity memory result ∧
    inputValue result output = BitVec.ofNat 256
      (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192) ∧
    (∃ bytes, read result output 32 1 = .ok bytes) := by
  obtain ⟨childFuel, stored, invoked, valid, outside, authority, value, readable⟩ :=
    LimbStorage.store_limbs_readable_contract profile program callee childFound memory inputs output w0 w1 w2 w3 call
  let args := [Value.reference (.address output), .scalar (.i64 w0), .scalar (.i64 w1),
    .scalar (.i64 w2), .scalar (.i64 w3)]
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have formed := call.output_formed (by simp : output ∈ [output])
  have checked : args.mapM (checkedValue memory) = .ok args := by
    simp [args, checkedValue, numericValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have setup : enterFrame (body profile callee) args memory = .ok (frame, memory) := by rfl
  have resume : run program 1 index 19 args frame [] stored = .ok (stored, []) := by
    have fetched : (body profile callee).code[19]? = some .ret := by rfl
    rw [run]
    simp only [found, fetched]
    rfl
  have stepped : step (body profile callee) (.call callee 5) 18 args frame args.reverse memory =
      .ok (.call callee args [] memory) := by
    simp [step, args, checkedValue, numericValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, invoked⟩ ⟨1, resume⟩
  have disabled (pc : Nat) (stack : List Value) :
      step (body profile callee) (.feature .vector256Accelerated) pc args frame stack memory =
        .ok (.next (pc + 1) (.scalar (.i32 0) :: stack) frame memory) := by
    change Except.ok (FrameAction.next (pc + 1)
      (.scalar (.i32 (if profile.vector256Accelerated then 1 else 0)) :: stack) frame memory) = _
    rw [scalar]
    rfl
  have started : ∃ fuel result returned,
      run program fuel index 0 args frame [] memory = .ok (result, returned) ∧
      result = stored ∧ returned = [] := by
    iterate 7
      apply run_next_exists (fun result returned => result = stored ∧ returned = []) found (by rfl)
      first
      | exact disabled _ _
      | rfl
      | simp only [step, args, List.getElem?_cons_zero,
          checkedValue, formValue, formed, checkedAt, Except.mapError,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
        rfl
    exact ⟨tailFuel, stored, [], tail, rfl, rfl⟩
  obtain ⟨fuel, result, returned, ran, rfl, rfl⟩ := started
  refine ⟨fuel, result, ?_, valid, outside, authority, value, readable⟩
  change invoke program fuel index args memory = _
  exact invoke_of_run found checked setup ran

theorem scalar_contract (profile : CIL.FeatureProfile) (scalar : profile.vector256Accelerated = false)
    (program : CIL.Program) (index callee : Nat)
    (found : program[index]? = some (body profile callee))
    (childFound : program[callee]? = some (LimbStorage.body profile)) : Contract program index :=
  store_product_contract profile scalar program index callee found childFound


#print axioms scalar_contract
#print axioms store_product_contract
end UInt256Proof.Multiply.ProductStorage
