import Std

namespace CIL

abbrev W64 := BitVec 64
abbrev W32 := BitVec 32

inductive Address where
  | byte (address : Nat)
  | local (frame index : Nat)
  | static (bytes : List (BitVec 8)) (offset : Nat)
  deriving DecidableEq, Repr

inductive Value where
  | i8 (word : BitVec 8)
  | i64 (word : W64)
  | i32 (word : W32)
  | v128 (bits : BitVec 128)
  | v256 (bits : BitVec 256)
  | span (address : Address) (length : Nat)
  | dataToken (bytes : List (BitVec 8))
  | object (id : Nat)
  | ref (address : Address)
  | nullRef
  | unmodeled
  deriving DecidableEq, Repr

end CIL
