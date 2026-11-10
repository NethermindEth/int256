import UInt256.Safety.ReadOnlyForwarder
import CIL.StepEquations
import CIL.Safety.Equations
import UInt256.Methods.Equality.ScalarLeaf
import CIL.Safety.CallComposition
import CIL.Safety.GuardNormalization

namespace UInt256Proof.Equality.ReferenceScalar
open CIL.Safety UInt256Model.Safety

def body (profile : CIL.FeatureProfile) (callee : Nat) : CIL.Method := { profile := profile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [], code := [
  .feature .vector256Accelerated,
  .brnonzero 12,
  .feature .sse41,
  .brnonzero 8,
  .arg 0,
  .arg 1,
  .call callee 2,
  .ret (some .unsigned8),
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile"] }
theorem checked (profile : CIL.FeatureProfile) (program : CIL.Program) (index callee : Nat)
    (vector : profile.vector256Accelerated = false) (sse : profile.sse41 = false)
    (found : program[index]? = some (body profile callee))
    (leafFound : program[callee]? = some (ScalarLeaf.body profile))
    (memory : Memory) (left right : Reference)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel final,
      InvocationCertificate program index (readOnlyArguments [left, right]) memory fuel final
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset := by
  have forwarded : BinaryReadOnlyInvocation
      (fun left right => .i32 (if left = right then 1 else 0)) program index := by
    apply forward_readOnly_binary program index 6 callee (body profile callee)
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
    · exact ScalarLeaf.scalar_checked profile program callee leafFound
    · intro current first second frame currentCall post continuation
      have fl := currentCall.input_formed (reference := first) (by simp)
      have fr := currentCall.input_formed (reference := second) (by simp)
      have vectorOff : profile.evaluate .vector256Accelerated = false := vector
      have sseOff : profile.evaluate .sse41 = false := sse
      cil_contract_steps 6 [readOnlyArguments, fl, fr, vectorOff, sseOff]
      exact continuation
  exact forwarded memory left right call

#print axioms checked
end UInt256Proof.Equality.ReferenceScalar
