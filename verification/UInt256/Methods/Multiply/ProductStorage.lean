import UInt256.Generated.MethodTemplates
import CIL.Safety.Equations
import UInt256.Methods.Multiply.LimbStorage
import UInt256.Methods.Multiply.ProductStorageContract
import CIL.Safety.CallComposition

namespace UInt256Proof.Multiply.ProductStorage
open CIL.Safety UInt256Model.Safety

def body (profile : CIL.FeatureProfile) (callee : Nat) : CIL.Method := by_elab
  let body ← Lean.Elab.Term.elabTermAndSynthesize
    (← `(UInt256Proof.Generated.Method.method26 $(Lean.mkIdent `profile) false $(Lean.mkIdent `callee))) none
  let some unfolded ← Lean.Meta.unfoldDefinition? body
    | throwError "Expected generated template application"
  return ← Lean.Meta.withTransparency .default (Lean.Meta.reduce unfolded)

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
  let frame : Frame := {
        activation := memory.nextIdentity
        locals := []
        owned := []
        arguments := []
        stackBytes := 0 }
  have formed := call.output_formed (by simp : output ∈ [output])
  have checked : args.mapM (checkedValue memory) = .ok args := by
    simp [args, checkedValue, numericValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have setup : enterFrame (body profile callee) args memory = .ok (frame, memory) := by rfl
  have disabled : profile.evaluate .vector256Accelerated = false := scalar
  have started : ∃ fuel result returned,
      run program fuel index 0 args frame [] memory = .ok (result, returned) ∧
      result = stored ∧ returned = [] := by
    cil_contract_steps [found, args, frame, formed, disabled, invoked]
    exact ⟨rfl, rfl⟩
  obtain ⟨fuel, result, returned, ran, rfl, rfl⟩ := started
  refine ⟨fuel, result, ?_, valid, outside, authority, value, readable⟩
  change invoke program fuel index args memory = _
  exact invoke_of_run found checked setup ran

theorem scalar_contract (profile : CIL.FeatureProfile) (scalar : profile.vector256Accelerated = false)
    (program : CIL.Program) (index callee : Nat)
    (found : program[index]? = some (body profile callee))
    (childFound : program[callee]? = some (LimbStorage.body profile)) : Contract program index :=
  store_product_contract profile scalar program index callee found childFound


end UInt256Proof.Multiply.ProductStorage
