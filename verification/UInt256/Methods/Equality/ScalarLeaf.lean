import CIL.SymbolicExecution
import UInt256.Safety.ReadOnlyContract
import UInt256.Safety.LimbAccess
import CIL.Safety.StepComposition
import UInt256.Methods.Equality.Lemmas
import UInt256.Safety.ReadOnlyExecution

namespace UInt256Proof.Equality.ScalarLeaf

open CIL.Safety UInt256Model.Safety

def body (profile : CIL.FeatureProfile) : CIL.Method := { profile := profile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [], code := [
  .arg 0,
  .fieldAt 0 8,
  .arg 1,
  .fieldAt 0 8,
  .bxor,
  .arg 0,
  .fieldAt 8 8,
  .arg 1,
  .fieldAt 8 8,
  .bxor,
  .bor,
  .arg 0,
  .fieldAt 16 8,
  .arg 1,
  .fieldAt 16 8,
  .bxor,
  .bor,
  .arg 0,
  .fieldAt 24 8,
  .arg 1,
  .fieldAt 24 8,
  .bxor,
  .bor,
  .const32 0,
  .convI8,
  .eq,
  .ret (some .unsigned8)] }

variable (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
  (found : program[index]? = some (body profile))

def scalarDifference (memory : Memory) (left right : Reference) : BitVec 64 :=
  (inputLimb memory left 0 ^^^ inputLimb memory right 0) |||
  (inputLimb memory left 1 ^^^ inputLimb memory right 1) |||
  (inputLimb memory left 2 ^^^ inputLimb memory right 2) |||
  (inputLimb memory left 3 ^^^ inputLimb memory right 3)

include found in
theorem scalar_run (memory : Memory) (left right : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel, run program fuel index 0
      (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if scalarDifference memory left right = 0 then 1 else 0))]) := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have hl := fun index rest => call.input_field_instruction (reference := left) (by simp) index rest
  have hr := fun index rest => call.input_field_instruction (reference := right) (by simp) index rest
  have hc (value : BitVec 32) (rest : List Value) :
      instruction (.const32 value) rest memory = .ok (memory, .scalar (.i32 value) :: rest) := rfl
  have hl0 := hl (0 : Fin 4)
  have hl1 := hl (1 : Fin 4)
  have hl2 := hl (2 : Fin 4)
  have hl3 := hl (3 : Fin 4)
  have hr0 := hr (0 : Fin 4)
  have hr1 := hr (1 : Fin 4)
  have hr2 := hr (2 : Fin 4)
  have hr3 := hr (3 : Fin 4)
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, CIL.fin_val_three, Nat.reduceMul] at hl0 hl1 hl2 hl3 hr0 hr1 hr2 hr3

  refine ⟨28, ?_⟩
  -- This is a checked sufficient execution prefix, not an assumed summary:
  -- every fetched opcode and transition must prove before the final return.
  iterate 26
    apply Eq.trans
    · apply run_next
      · exact found
      · simp only [body]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [step, readOnlyArguments, checkedValue, numericValue, formValue, fl, fr,
            hl0, hl1, hl2, hl3, hr0, hr1, hr2, hr3, hc, pureArity, scalars, CIL.step.eq_def, CIL.binary, CIL.unary, checkedAt,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try (exact ⟨rfl, rfl, rfl, rfl⟩)
        done
  simp [run, found, body, step, checkedValue, numericValue, scalarDifference, CIL.NarrowKind.extend,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  split <;> rfl
#print axioms scalar_run

end UInt256Proof.Equality.ScalarLeaf

namespace UInt256Proof.Equality.ScalarLeaf

open CIL.Safety UInt256Model.Safety

theorem input_limb_value (memory : Memory) (reference : Reference) :
    UInt256Model.value (inputLimb memory reference) = inputValue memory reference :=
  UInt256Proof.input_value (fun offset => (memory.cells reference.allocation offset).bits) reference.offset

/-- The execution reduction is equivalent to equality of independently decoded
    initial values, including when their input views partially overlap. -/
theorem scalar_difference_zero (memory : Memory) (left right : Reference) :
    scalarDifference memory left right = 0 ↔ inputValue memory left = inputValue memory right := by
  have equal := xor_or_zero_value (inputLimb memory left) (inputLimb memory right)
  rw [input_limb_value, input_limb_value] at equal
  exact equal

variable (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
  (found : program[index]? = some (body profile))

include found in
theorem scalar_run_value (memory : Memory) (left right : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel, run program fuel index 0
      (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))]) := by
  simpa only [scalar_difference_zero] using scalar_run profile program index found memory left right frame call

#print axioms scalar_difference_zero
#print axioms scalar_run_value

end UInt256Proof.Equality.ScalarLeaf

namespace UInt256Proof.Equality.ScalarLeaf

open CIL.Safety UInt256Model.Safety

variable (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
  (found : program[index]? = some (body profile))

theorem scalar_frame_fits (left right : Reference) :
    FrameSetupFits (body profile) (readOnlyArguments [left, right]) := by
  simp [body, FrameSetupFits, InitializersFit, AggregateArgumentsFit, ParameterArgumentsFit]

include found in
theorem scalar_checked (memory : Memory) (left right : Reference)
    (call : CallingConditions program memory [left, right] []) :
    ∃ fuel final,
      InvocationCertificate program index (readOnlyArguments [left, right]) memory fuel final
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset :=
  certify_readOnly_binary program index (body profile)
    (fun left right => .i32 (if left = right then 1 else 0))
    found (scalar_frame_fits profile) (scalar_run_value profile program index found) memory left right call
#print axioms scalar_checked

end UInt256Proof.Equality.ScalarLeaf
