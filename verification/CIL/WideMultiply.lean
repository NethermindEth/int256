import CIL.Types

namespace CIL.WideMultiply

def high64 (left right : W64) : W64 :=
  BitVec.ofNat 64 (left.toNat * right.toNat / 2^64)

end CIL.WideMultiply
