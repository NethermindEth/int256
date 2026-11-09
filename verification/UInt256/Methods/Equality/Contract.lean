import CIL.ExecutionLemmas
import UInt256.Representation

open CIL UInt256Model
namespace UInt256Model.Equality

def booleanWord (b : Bool) : W32 := if b then 1 else 0

/-- Signedness belongs to the declared primitive operand, not the UInt256. -/
inductive Scalar where
  | u32 (bits : W32) | u64 (bits : W64)
  | s32 (bits : W32) | s64 (bits : W64)

def Scalar.argument : Scalar → Value
  | .u32 bits | .s32 bits => .i32 bits
  | .u64 bits | .s64 bits => .i64 bits

def Scalar.number : Scalar → Int
  | .u32 bits => bits.toNat
  | .u64 bits => bits.toNat
  | .s32 bits => bits.toInt
  | .s64 bits => bits.toInt

end UInt256Model.Equality
