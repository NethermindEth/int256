import UInt256.VectorRepresentation

open CIL UInt256Proof UInt256Model

namespace VectorMemoryTests

def zeroMemory : Memory := fun
  | .byte _ => some (.i8 0)
  | _ => none

-- Unaligned little-endian stores and exact width.
example : read64 (writeBytes zeroMemory 1 (1 + 2^64 * 2) 16) (.byte 1) =
    some (.i64 1) := by decide
example : read64 (writeBytes zeroMemory 1 (1 + 2^64 * 2) 16) (.byte 9) =
    some (.i64 2) := by decide
example : writeBytes zeroMemory 1 (2^128 - 1) 16 (.byte 0) = some (.i8 0) := by decide
example : writeBytes zeroMemory 1 (2^128 - 1) 16 (.byte 17) = some (.i8 0) := by decide

-- Early output writes really alter overlapping input bytes; a captured local
-- retains the old operand instead of silently re-reading the changed input.
def overlappingInput : Memory := writeBytes zeroMemory 1 (1 + 2^64) 16
example : read128 overlappingInput (.byte 1) = some (.v128 (BitVec.ofNat 128 (1 + 2^64))) :=
  by decide
example : read128 (writeBytes overlappingInput 9 0 16) (.byte 1) = some (.v128 1) := by decide
example : read128 (writeBytes
    (write overlappingInput (.local 0 0) (.v128 (BitVec.ofNat 128 (1 + 2^64)))) 9 0 16)
    (.local 0 0) = some (.v128 (BitVec.ofNat 128 (1 + 2^64))) := by decide

-- Ref offsets scale by the actual element size, including signed overloads.
example : unsafeAdd 16 1 (.byte 3) = some (.byte 19) := by decide
example : unsafeAdd 32 3 (.byte 3) = some (.byte 99) := by decide
example : unsafeAdd 16 (-1) (.byte 19) = some (.byte 3) := by decide
example : unsafeAdd 16 (-1) (.byte 3) = none := by decide
example : unsafeAdd 16 1 (.local 0 0) = none := by decide
example : unsafeAsRef (.v256 17) = none := by rfl
example : unsafeAsRef (.object 17) = some (.ref (.byte 17)) := by rfl
example : read128 (write zeroMemory (.local 0 0) (.v256 0)) (.local 0 0) = none := by decide

-- Synthetic semantic fixture bytes are independent of the production lookup.
-- Production table facts must instead be checked from extracted RVA bytes.
def fixtureData : List (BitVec 8) := [1, 2] ++ List.replicate 30 0
example (m : Memory) : read256 m (.static fixtureData 0) = some (.v256 513) := by
  change read256 zeroMemory (.static fixtureData 0) = some (.v256 513)
  decide
example (m : Memory) : read256 m (.static fixtureData 1) = none := by
  change read256 zeroMemory (.static fixtureData 1) = none
  decide
example (m : Memory) : write256 m (.static fixtureData 0) 0 = none := by rfl
example (m : Memory) : write128 m (.static fixtureData 0) 0 = none := by rfl
example (m : Memory) : evalMemory .spanCreate [.i32 33, .ref (.static fixtureData 0)] m =
    none := by rfl
example (m : Memory) : evalMemory .spanCreate [.i32 32, .ref (.static fixtureData 1)] m =
    none := by rfl
example (m : Memory) : evalMemory (.add 32 false)
    [.i64 1, .ref (.static fixtureData 0)] m =
      some (m, [.ref (.static fixtureData 32)]) := by rfl
example (m : Memory) : evalMemory .bitcastByteBool [.i32 1] m = some (m, [.i32 1]) := by rfl
example (m : Memory) : evalMemory .bitcastByteBool [.i32 256] m = none := by rfl
example (m : Memory) : evalMemory (.add 32 false) [.i32 1, .ref (.byte 0)] m = none := by rfl
example (m : Memory) : evalMemory (.add 16 true) [.i64 1, .ref (.byte 0)] m = none := by rfl

#print axioms readBytes_writeBytes
#print axioms captured256_survives_store
#print axioms vector_store4

end VectorMemoryTests
