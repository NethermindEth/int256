import UInt256.Methods.Compare.Automation

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Compare

theorem less_correct (initial : Bytes) (left right : Nat) :
    UInt256Model.Compare.Contract Extracted.program Extracted.entryIndex .less
      initial left right := by
  comparison_execute initial, left, right

end UInt256Proof.Compare
