import CIL.Semantics

open CIL

-- Exact widths, subtraction operand order, wrapping, and malformed stacks.
example : binary .sub (.i64 0) (.i64 1) =
    some (.i64 (BitVec.ofNat 64 (2^64 - 1))) := by decide
example : binary .sub (.i32 0) (.i32 1) =
    some (.i32 (BitVec.ofNat 32 (2^32 - 1))) := by decide
example : binary .sub (.i64 7) (.i64 2) = some (.i64 5) := by decide
example : binary .sub (.i64 7) (.i32 2) = none := by decide
example : binary .band (.i64 3) (.i64 1) = some (.i64 1) := by decide
example : binary .band (.i32 3) (.i32 2) = some (.i32 2) := by decide
example : binary .band (.i32 3) (.i64 2) = none := by decide
example (m : Memory) : step .sub false 0 [] 0 [.i64 2, .i64 7] m =
    some (.next 1 [.i64 5] m) := by rfl
example (m : Memory) : step .sub false 0 [] 0 [.i64 7] m = none := by rfl
example (m : Memory) : step .convI8 false 0 [] 0 [.i32 (BitVec.ofInt 32 (-1))] m =
    some (.next 1 [.i64 (BitVec.ofNat 64 (2^64 - 1))] m) := by rfl
