import UInt256.Methods.Equality.SseSafety
import UInt256.Safety.ReadOnlyExecution

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
