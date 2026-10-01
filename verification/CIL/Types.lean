import Std

namespace CIL

abbrev W64 := BitVec 64
abbrev W32 := BitVec 32

inductive Address where
  | byte (address : Nat)
  | local (frame index : Nat)
  deriving DecidableEq, Repr

inductive Value where
  | i8 (word : BitVec 8)
  | i64 (word : W64)
  | i32 (word : W32)
  | object (id : Nat)
  | ref (address : Address)
  | nullRef
  | unmodeled
  deriving DecidableEq, Repr

end CIL
