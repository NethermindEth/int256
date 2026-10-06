import UInt256.Methods.Compare.ScalarSafety
import UInt256.Methods.Compare.Lemmas
import UInt256.Safety.ReadOnlyExecution

namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety

theorem input_limb_value (memory : Memory) (reference : Reference) :
    UInt256Model.value (inputLimb memory reference) = inputValue memory reference :=
  UInt256Proof.input_value (fun offset => (memory.cells reference.allocation offset).bits) reference.offset

theorem scalar_result_math (memory : Memory) (left right : Reference) :
    scalarResult memory left right =
      if (inputValue memory left).toNat < (inputValue memory right).toNat then 1 else 0 := by
  have order := UInt256Proof.Compare.value_lt_descending (inputLimb memory left) (inputLimb memory right)
  rw [input_limb_value, input_limb_value] at order
  simp only [order]
  by_cases h3 : inputLimb memory left 3 = inputLimb memory right 3 <;>
    by_cases h2 : inputLimb memory left 2 = inputLimb memory right 2 <;>
    by_cases h1 : inputLimb memory left 1 = inputLimb memory right 1 <;>
    simp [scalarResult, h3, h2, h1, BitVec.lt_def]

theorem scalar_run_value (memory : Memory) (left right : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program memory [left, right] []) :
    ∃ fuel, run Extracted.program fuel scalarIndex 0
      (readOnlyArguments [left, right]) frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if (inputValue memory left).toNat < (inputValue memory right).toNat then 1 else 0))]) := by
  simpa only [scalar_result_math] using scalar_run memory left right frame call

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
        [.scalar (.i32 (if (inputValue memory left).toNat < (inputValue memory right).toNat then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset :=
  certify_readOnly_binary Extracted.program scalarIndex scalarBody
    (fun left right => .i32 (if left.toNat < right.toNat then 1 else 0))
    scalar_body_found scalar_frame_fits scalar_run_value memory left right call

#print axioms scalar_result_math
#print axioms scalar_checked
end UInt256Proof.Compare.Safety
