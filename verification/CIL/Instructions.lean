import CIL.Types

namespace CIL

inductive Op where
  | arg (index : Nat)
  | local (index : Nat)
  | localAddr (index : Nat)
  | setLocal (index : Nat)
  | field (index : Fin 4)
  | fieldAddr (index : Fin 4)
  | const32 (word : W32)
  | convI8 | add | sub | band | bor | ltu | gtu | eq | load64 | store64 | dup | pop
  | branch (target : Nat)
  | brzero (target : Nat)
  | brnonzero (target : Nat)
  | bltu (target : Nat)
  | bgeu (target : Nat)
  | call (method : Nat) (argc : Nat)
  | featureDisabled | skipInit | asRef
  | ret
  | unsupported (description : String)
  deriving Repr

structure Method where
  code : List Op
  locals : List Value
  returnsValue : Bool
  deriving Repr

abbrev Program := List Method

end CIL
