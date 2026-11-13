import UInt256.Safety.Calling
import UInt256.Safety.OutputAccess

namespace UInt256Proof.Safety
open CIL.Safety UInt256Model.Safety

def addOverflow (memory : CIL.Safety.Memory) (left right : Reference) : BitVec 32 :=
  if 2^256 ≤ (inputValue memory left).toNat + (inputValue memory right).toNat then 1 else 0

structure AddResult (original final : CIL.Safety.Memory) (values : List Value)
    (left right output : Reference) : Prop where
  wellFormed : final.WellFormed
  value : inputValue final output = inputValue original left + inputValue original right
  flag : values = [.scalar (.i32 (addOverflow original left right))]
  writable : access final output 32 1 true = .ok ()
  footprint : ∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset →
    final.cells id offset = original.cells id offset

end UInt256Proof.Safety
