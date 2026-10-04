import UInt256.Methods.Equality.ReferenceAutomation

open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Equality

theorem equal_correct (initial : Bytes) (left right : Nat) :
    UInt256Model.Equality.Contract Extracted.program Extracted.entryIndex initial left right := by
  reference_equality_execute initial, left, right

end UInt256Proof.Equality
