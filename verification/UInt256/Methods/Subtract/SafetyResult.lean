import UInt256.Safety.Contract

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety

def subtractUnderflow (memory : CIL.Safety.Memory) (left right : Reference) : BitVec 32 :=
  if (inputValue memory left).toNat < (inputValue memory right).toNat then 1 else 0

structure SubtractResult (original final : CIL.Safety.Memory) (values : List Value)
    (left right output : Reference) : Prop where
  wellFormed : final.WellFormed
  value : inputValue final output = inputValue original left - inputValue original right
  flag : values = [.scalar (.i32 (subtractUnderflow original left right))]
  writable : access final output 32 1 true = .ok ()
  footprint : ∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset →
    final.cells id offset = original.cells id offset

end UInt256Proof.Subtract.Safety
