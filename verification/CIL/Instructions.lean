import CIL.Types
import CIL.Features
import CIL.SIMD.Availability
import CIL.VectorMemory

namespace CIL

inductive Op where
  | arg (index : Nat)
  | aggregateArg (index : Nat)
  | aggregateArgAddr (index : Nat)
  | local (index : Nat)
  | aggregateLocal (index : Nat)
  | aggregateLocalAddr (index : Nat)
  | setAggregateLocal (index : Nat)
  | localAddr (index : Nat)
  | setLocal (index : Nat)
  | field (index : Fin 4)
  | fieldAddr (index : Fin 4)
  | setField (index : Fin 4)
  | const32 (word : W32)
  | const64 (word : W64)
  | convI8 | convI4 | convU1 | convU4 | convU8 | convU | bnot | add | sub | mul | band | bor | bxor
  | shl | shr | shrUn | lt | ltu | gtu | eq | load64 | store64 | dup | pop
  | branch (target : Nat)
  | brzero (target : Nat)
  | brnonzero (target : Nat)
  | bltu (target : Nat)
  | bgeu (target : Nat)
  | bgtu (target : Nat)
  | bge (target : Nat)
  | blt (target : Nat)
  | beq (target : Nat)
  | bne (target : Nat)
  | call (method : Nat) (argc : Nat)
  | newValue (constructor : Nat) (argc : Nat)
  | skipInit | asRef
  | feature (id : Feature)
  | intrinsic (operation : Intrinsic) (argc : Nat)
  | memory (operation : MemoryOp)
  | ret
  | unsupported (description : String)
  deriving Repr

/-- Physical local storage, retained even when InitLocals is false. Reference
    slots retain managed-reference values rather than numerical addresses. -/
inductive LocalKind where
  | byte | word32 | word64 | vector128 | vector256 | reference
  deriving DecidableEq, Repr

structure StaticDescriptor where
  identity : Nat
  fieldName : String
  bytes : List (BitVec 8)
  deriving DecidableEq, Repr

structure Method where
  profile : FeatureProfile := FeatureProfile.scalar
  code : List Op
  locals : List Value
  localKinds : List LocalKind := []
  staticSites : List (Nat × StaticDescriptor) := []
  aggregateLocals : List Nat := []
  aggregateArgs : List Nat := []
  returnsValue : Bool
  deriving Repr

abbrev Program := List Method

end CIL
