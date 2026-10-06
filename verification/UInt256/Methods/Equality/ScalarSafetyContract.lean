import UInt256.Methods.Equality.ScalarSafetyFacts
import UInt256.Safety.ReadOnlyExecution

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
