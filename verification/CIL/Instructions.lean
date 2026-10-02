import CIL.Types
import CIL.Features
import CIL.SIMD.Availability
import CIL.VectorMemory

namespace CIL

inductive Op where
  | arg (index : Nat)
  | local (index : Nat)
  | localAddr (index : Nat)
  | setLocal (index : Nat)
  | field (index : Fin 4)
  | fieldAddr (index : Fin 4)
  | const32 (word : W32)
  | convI8 | convI4 | convU1 | convU | add | sub | mul | band | bor | bxor
  | shl | shr | shrUn | ltu | gtu | eq | load64 | store64 | dup | pop
  | branch (target : Nat)
  | brzero (target : Nat)
  | brnonzero (target : Nat)
  | bltu (target : Nat)
  | bgeu (target : Nat)
  | call (method : Nat) (argc : Nat)
  | skipInit | asRef
  | feature (id : Feature)
  | intrinsic (operation : Intrinsic) (argc : Nat)
  | memory (operation : MemoryOp)
  | ret
  | unsupported (description : String)
  deriving Repr

structure Method where
  profile : FeatureProfile := FeatureProfile.scalar
  code : List Op
  locals : List Value
  returnsValue : Bool
  deriving Repr

abbrev Program := List Method

end CIL
