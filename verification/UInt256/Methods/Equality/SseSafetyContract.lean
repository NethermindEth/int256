import Extracted
import UInt256.Safety.ReadOnlyContract
import UInt256.Methods.Equality.HalfSafetyFacts
import CIL.Safety.StepComposition
import UInt256.Safety.ReadOnlyExecution

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

def sseIndex : Nat := Extracted.program.findIdx fun body => body.code.any fun op =>
  match op with | .intrinsic (.vector (.equalsAll 128)) _ => true | _ => false

/-- Execute the extracted SSE leaf with its two managed-reference locals. -/
theorem sse_run (memory : Memory) (left right : Reference) (frame : Frame)
    (first second : Option ManagedReference)
    (locals : frame.locals = [.root first, .root second])
    (call : CallingConditions Extracted.program memory [left, right] []) :
    ∃ fuel, run Extracted.program fuel sseIndex 0 (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))]) := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have hl := call.input_half_load (reference := left) (by simp)
  have hr := call.input_half_load (reference := right) (by simp)
  have al := call.input_half_address (reference := left) (by simp)
  have ar := call.input_half_address (reference := right) (by simp)
  have hl0 := hl 0
  have hr0 := hr 0
  have al1 := al 1
  have ar1 := ar 1
  have hl1 := hl 1
  have hr1 := hr 1
  simp only [Fin.val_one, Nat.mul_one] at al1 ar1 hl1 hr1
  simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] at hl0 hr0
  have difference := input_half_difference_zero memory left right
  conv in sseIndex => cbv
  refine ⟨26, ?_⟩
  iterate 25
    apply Eq.trans
    · apply run_next
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [cil_code, step, readOnlyArguments, checkedValue, numericValue, formValue, fl, fr,
            hl0, hr0, hl1, hr1, al1, ar1,
            locals, storeLocal, loadLocal, pureArity, scalars, staticInstruction, memoryInstruction,
            CIL.step, CIL.Intrinsic.available, intrinsic_equal128, intrinsic_xor128, intrinsic_or128, intrinsic_zero128,
            difference, instruction, CIL.offsetValue, referenceAt,
            UInt256Model.Equality.booleanWord, checkedAt,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try (exact ⟨rfl, rfl, rfl, rfl⟩)
        done
  simp [run, cil_code, step, checkedValue, numericValue, leaveFrame,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms sse_run

end UInt256Proof.Equality.Safety

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

def sseBody : CIL.Method := Extracted.program[sseIndex]?.getD
  { code := [], locals := [], returnsValue := false }

theorem sse_body_found : Extracted.program[sseIndex]? = some sseBody := by rfl

theorem sse_frame_fits (left right : Reference) :
    FrameSetupFits sseBody (readOnlyArguments [left, right]) := by
  conv in sseBody => cbv
  simp [FrameSetupFits, InitializersFit, InitializerFits, AggregateArgumentsFit]

theorem sse_frame_roots (memory : Memory) (left right : Reference)
    (frame : Frame) (entered : Memory)
    (setup : enterFrame sseBody (readOnlyArguments [left, right]) memory = .ok (frame, entered)) :
    frame.locals = [.root (some .null), .root (some .null)] := by
  conv at setup in sseBody => cbv
  simp [enterFrame, makeLocals, makeLocal, makeArgumentHomes,
    Bind.bind, Except.bind, Pure.pure, Except.pure] at setup
  obtain ⟨rfl, rfl⟩ := setup
  rfl

theorem sse_checked (memory : Memory) (left right : Reference)
    (call : CallingConditions Extracted.program memory [left, right] []) :
    ∃ fuel final,
      InvocationCertificate Extracted.program sseIndex (readOnlyArguments [left, right]) memory fuel final
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset :=
  certify_readOnly_binary_frame Extracted.program sseIndex sseBody
    (fun left right => .i32 (if left = right then 1 else 0))
    sse_body_found sse_frame_fits
    (fun frame => frame.locals = [.root (some .null), .root (some .null)])
    sse_frame_roots
    (fun memory left right frame roots call =>
      sse_run memory left right frame (some .null) (some .null) roots call)
    memory left right call

#print axioms sse_frame_roots
#print axioms sse_checked

end UInt256Proof.Equality.Safety
