import UInt256.Methods.Bitwise.Automation
open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Bitwise
theorem xor_correct (initial : Bytes) (left right out : Nat) :
 UInt256Model.Bitwise.Contract Extracted.program Extracted.entryIndex .xor initial left right out := by
  binary_bitwise_execute initial,left,right,out,value_xor
end UInt256Proof.Bitwise
