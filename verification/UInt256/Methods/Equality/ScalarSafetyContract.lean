import Extracted
import UInt256.Safety.ReadOnlyContract
import UInt256.Safety.LimbAccess
import CIL.Safety.StepComposition
import UInt256.Methods.Equality.Lemmas
import UInt256.Safety.ReadOnlyExecution

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

/-- Discover the reachable leaf containing the limb reads; its body is still
    executed and checked below, never assigned a contract by its shape. -/
def scalarIndex : Nat := Extracted.program.findIdx fun body =>
  body.code.any (fun op => match op with | .field _ => true | _ => false) &&
  !(body.code.any fun op => match op with | .call _ _ => true | _ => false)

def scalarDifference (memory : Memory) (left right : Reference) : BitVec 64 :=
  (inputLimb memory left 0 ^^^ inputLimb memory right 0) |||
  (inputLimb memory left 1 ^^^ inputLimb memory right 1) |||
  (inputLimb memory left 2 ^^^ inputLimb memory right 2) |||
  (inputLimb memory left 3 ^^^ inputLimb memory right 3)

theorem scalar_run (memory : Memory) (left right : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program memory [left, right] []) :
    ∃ fuel, run Extracted.program fuel scalarIndex 0
      (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if scalarDifference memory left right = 0 then 1 else 0))]) := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have hl := fun index rest => call.input_field_instruction (reference := left) (by simp) index rest
  have hr := fun index rest => call.input_field_instruction (reference := right) (by simp) index rest
  have hc (value : BitVec 32) (rest : List Value) :
      instruction (.const32 value) rest memory = .ok (memory, .scalar (.i32 value) :: rest) := rfl
  conv in scalarIndex => cbv
  refine ⟨28, ?_⟩
  -- This is a checked sufficient execution prefix, not an assumed summary:
  -- every fetched opcode and transition must prove before the final return.
  iterate 26
    apply Eq.trans
    · apply run_next
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [step, readOnlyArguments, checkedValue, numericValue, formValue, fl, fr,
            hl, hr, hc, pureArity, scalars, CIL.step.eq_def, CIL.binary, checkedAt,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try (exact ⟨rfl, rfl, rfl, rfl⟩)
        done
  simp [run, cil_code, step, checkedValue, numericValue, scalarDifference,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
#print axioms scalar_run

end UInt256Proof.Equality.Safety

namespace UInt256Proof.Equality.Safety

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

theorem scalar_run_value (memory : Memory) (left right : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program memory [left, right] []) :
    ∃ fuel, run Extracted.program fuel scalarIndex 0
      (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))]) := by
  simpa only [scalar_difference_zero] using scalar_run memory left right frame call

#print axioms scalar_difference_zero
#print axioms scalar_run_value

end UInt256Proof.Equality.Safety

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

def scalarBody : CIL.Method := Extracted.program[scalarIndex]?.getD
  { code := [], locals := [], returnsValue := false }

theorem scalar_body_found : Extracted.program[scalarIndex]? = some scalarBody := by rfl

theorem scalar_frame_fits (left right : Reference) :
    FrameSetupFits scalarBody (readOnlyArguments [left, right]) := by
  conv in scalarBody => cbv
  simp [FrameSetupFits, InitializersFit, AggregateArgumentsFit]

theorem scalar_checked (memory : Memory) (left right : Reference)
    (call : CallingConditions Extracted.program memory [left, right] []) :
    ∃ fuel final,
      InvocationCertificate Extracted.program scalarIndex (readOnlyArguments [left, right]) memory fuel final
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset :=
  certify_readOnly_binary Extracted.program scalarIndex scalarBody
    (fun left right => .i32 (if left = right then 1 else 0))
    scalar_body_found scalar_frame_fits scalar_run_value memory left right call
#print axioms scalar_checked

end UInt256Proof.Equality.Safety
