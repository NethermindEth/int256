import CIL.Safety.Equations
import UInt256.Safety.ReadOnlyExecution
import UInt256.Methods.Equality.VectorPrimitive

namespace UInt256Proof.Equality.ReferenceVector
open CIL.Safety UInt256Model.Safety VectorPrimitive

def body (profile : CIL.FeatureProfile) : CIL.Method := { profile := profile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [], code := [
  .arg 0,
  .loadAggregate 32,
  .memory (.bitcastValue (.aggregate 32) .vector256),
  .arg 1,
  .loadAggregate 32,
  .memory (.bitcastValue (.aggregate 32) .vector256),
  .intrinsic (.vector (.equalsAll 256)) 2,
  .ret (some .unsigned8)] }

theorem executed (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (body profile))
    (memory : Memory) (left right : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel, run program fuel index 0 (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))]) := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have hl := load_input call (input := left) (by simp)
  have hr := load_input call (input := right) (by simp)
  have cl := cast_input memory left
  have cr := cast_input memory right
  generalize leftEq : inputValue memory left = leftValue at *
  generalize rightEq : inputValue memory right = rightValue at *
  refine ⟨9, ?_⟩
  iterate 7
    apply Eq.trans
    · apply run_next found
      · simp only [body]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [body, step, cil_guard, observerCount, readOnlyArguments, checkedValue, numericValue, formValue, fl, fr,
            hl, hr, cl, cr, staticInstruction, checkedIntrinsic, pureArity, scalars,
            CIL.step.eq_def, CIL.Intrinsic.available, eval_equal,
            checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try exact ⟨rfl, rfl, rfl, rfl⟩
        done
  simp [run, found, body, step, cil_guard, observerCount, checkedValue, numericValue,
    CIL.NarrowKind.extend_ite_ofNat_one_zero, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem checked (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (body profile))
    (memory : Memory) (left right : Reference)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel final,
      InvocationCertificate program index (readOnlyArguments [left, right]) memory fuel final
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset :=
  certify_readOnly_binary program index (body profile)
    (fun left right => .i32 (if left = right then 1 else 0)) found
    (by intro left right; simp [body, FrameSetupFits, InitializersFit, AggregateArgumentsFit, ParameterArgumentsFit, SelectedKindsFit])
    (executed profile program index found) memory left right call

#print axioms executed
#print axioms checked
end UInt256Proof.Equality.ReferenceVector
