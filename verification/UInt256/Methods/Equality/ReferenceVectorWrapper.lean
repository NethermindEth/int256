import UInt256.Safety.ReadOnlyForwarder
import CIL.Safety.CallComposition
import UInt256.Methods.Equality.ReferenceVector
import UInt256.Safety.ReadOnlyExecution

namespace UInt256Proof.Equality.ReferenceVectorWrapper
open CIL.Safety UInt256Model.Safety

def body (profile : CIL.FeatureProfile) (callee : Nat) : CIL.Method := { profile := profile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [], code := [
  .feature .vector256Accelerated,
  .brnonzero 12,
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
  .call callee 2,
  .ret (some .unsigned8)] }

theorem checked (profile : CIL.FeatureProfile) (program : CIL.Program) (index callee : Nat)
    (vector : profile.vector256Accelerated = true)
    (found : program[index]? = some (body profile callee))
    (leafFound : program[callee]? = some (ReferenceVector.body profile))
    (memory : Memory) (left right : Reference)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel final,
      InvocationCertificate program index (readOnlyArguments [left, right]) memory fuel final
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset := by
  have forwarded : BinaryReadOnlyInvocation
      (fun left right => .i32 (if left = right then 1 else 0)) program index := by
    apply forward_readOnly_binary program index 14 callee (body profile callee)
      (fun left right => .i32 (if left = right then 1 else 0))
      (fun left right => readOnlyArguments [left, right]) found (by rfl) (by rfl) (by rfl)
    · intro first second
      simp [body, FrameSetupFits, InitializersFit, AggregateArgumentsFit,
        ParameterArgumentsFit]
    · intro first second; rfl
    · intro first second; rfl
    · intro first second; split <;> rfl
    · intro first second
      exact ⟨_, rfl, CIL.NarrowKind.extend_ite_ofNat_one_zero _ _⟩
    · exact ReferenceVector.checked profile program callee leafFound
    · intro current first second frame currentCall post continuation
      have fl := currentCall.input_formed (reference := first) (by simp)
      have fr := currentCall.input_formed (reference := second) (by simp)
      have vectorOn : profile.evaluate .vector256Accelerated = true := vector
      cil_contract_steps 4 [readOnlyArguments, fl, fr, vectorOn]
      exact continuation
  exact forwarded memory left right call

#print axioms checked
end UInt256Proof.Equality.ReferenceVectorWrapper
