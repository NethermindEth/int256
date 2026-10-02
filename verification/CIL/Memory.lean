import CIL.Types

namespace CIL

abbrev Memory := Address → Option Value

def write (m : Memory) (a : Address) (v : Value) : Memory :=
  fun b => if b = a then some v else m b

-- Byte-addressed caller storage allows even partially overlapping UInt256
-- references. Method locals occupy a disjoint private address space.
def readBytes (m : Memory) (base : Nat) : Nat → Option Nat
  | 0 => some 0
  | n + 1 => do
    let .i8 lo ← m (.byte base) | none
    let hi ← readBytes m (base + 1) n
    return lo.toNat + 256 * hi

def writeBytes (m : Memory) (base : Nat) (value : Nat) : Nat → Memory
  | 0 => m
  | n + 1 => writeBytes (write m (.byte base) (.i8 (BitVec.ofNat 8 value)))
      (base + 1) (value / 256) n

-- Static addresses carry bytes extracted from the artifact. Reads are independent
-- of mutable caller memory, and typed stores below cannot modify those bytes.
def readStaticBytes (bytes : List (BitVec 8)) (offset : Nat) : Nat → Option Nat
  | 0 => some 0
  | n + 1 => do
    let lo ← bytes[offset]?
    let hi ← readStaticBytes bytes (offset + 1) n
    return lo.toNat + 256 * hi

def read64 (m : Memory) : Address → Option Value
  | .byte base => do return .i64 (BitVec.ofNat 64 (← readBytes m base 8))
  | .local frame index => do
    let .i64 w ← m (.local frame index) | none
    return .i64 w
  | .static bytes offset => do
    return .i64 (BitVec.ofNat 64 (← readStaticBytes bytes offset 8))

def write64 (m : Memory) (address : Address) (word : W64) : Option Memory :=
  match address with
  | .byte base => some (writeBytes m base word.toNat 8)
  | .local frame index => some (write m (.local frame index) (.i64 word))
  | .static _ _ => none

end CIL
