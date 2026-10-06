import UInt256.Methods.Equality.VectorSafety
import UInt256.Safety.ReadOnlyExecution

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
