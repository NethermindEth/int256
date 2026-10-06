import Extracted
import UInt256.Safety.ReadOnlyContract
import UInt256.Methods.Equality.VectorLemmas
import CIL.Safety.StepComposition
import UInt256.Safety.ReadOnlyExecution

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

def vectorIndex : Nat := Extracted.program.findIdx fun body => body.code.any fun op =>
  match op with | .intrinsic (.vector (.equalsAll 256)) _ => true | _ => false

/-- Full 32-byte loads are justified before interpreting vector equality.
    Bitcasts do not initialize memory or excuse unreadable vector lanes. -/
theorem vector_run (memory : Memory) (left right : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program memory [left, right] []) :
    ∃ fuel, run Extracted.program fuel vectorIndex 0 (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))]) := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have hl := call.input_load (reference := left) (by simp)
  have hr := call.input_load (reference := right) (by simp)
  conv in vectorIndex => cbv
  refine ⟨8, ?_⟩
  iterate 7
    apply Eq.trans
    · apply run_next
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [cil_code, step, readOnlyArguments, checkedValue, numericValue, formValue, fl, fr,
            hl, hr, pureArity, scalars, staticInstruction, memoryInstruction,
            CIL.step, CIL.Intrinsic.available, intrinsic_equal256,
            UInt256Model.Equality.booleanWord, checkedAt,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try (exact ⟨rfl, rfl, rfl, rfl⟩)
        done
  simp [run, cil_code, step, checkedValue, numericValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms vector_run

end UInt256Proof.Equality.Safety

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

def vectorBody : CIL.Method := Extracted.program[vectorIndex]?.getD
  { code := [], locals := [], returnsValue := false }

theorem vector_body_found : Extracted.program[vectorIndex]? = some vectorBody := by rfl

theorem vector_frame_fits (left right : Reference) :
    FrameSetupFits vectorBody (readOnlyArguments [left, right]) := by
  conv in vectorBody => cbv
  simp [FrameSetupFits, InitializersFit, AggregateArgumentsFit]

theorem vector_checked (memory : Memory) (left right : Reference)
    (call : CallingConditions Extracted.program memory [left, right] []) :
    ∃ fuel final,
      InvocationCertificate Extracted.program vectorIndex (readOnlyArguments [left, right]) memory fuel final
        [.scalar (.i32 (if inputValue memory left = inputValue memory right then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset :=
  certify_readOnly_binary Extracted.program vectorIndex vectorBody
    (fun left right => .i32 (if left = right then 1 else 0))
    vector_body_found vector_frame_fits vector_run memory left right call
#print axioms vector_checked

end UInt256Proof.Equality.Safety
