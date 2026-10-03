import CIL.ProfileEquivalence

namespace CIL.ExpansionTests

open CIL.Vector

example : evalIntrinsic (.bmi2 .multiplyHigh64)
    [.i64 (BitVec.ofNat 64 (2^64 - 1)), .i64 (BitVec.ofNat 64 (2^64 - 1))] =
    some (.i64 (BitVec.ofNat 64 (2^64 - 2))) := by decide

example : evalIntrinsic (.armBase64 .multiplyHigh64)
    [.i64 (BitVec.ofNat 64 (2^63)), .i64 2] = some (.i64 1) := by decide

example : evalIntrinsic (.avx2 .multiplyEven32)
    [.v256 (pack256 (BitVec.ofNat 64 (2^32 * 91 + 2)) 3 5 7),
     .v256 (pack256 (BitVec.ofNat 64 (2^32 * 113 + 11)) 13 17 19)] =
    some (.v256 (pack256 22 39 85 133)) := by decide

example : evalIntrinsic (.avx512DQ .mul64)
    [.v256 (pack256 (BitVec.ofNat 64 (2^64 - 1)) (BitVec.ofNat 64 (2^63)) 17 2),
     .v256 (pack256 2 2 3 (BitVec.ofNat 64 (2^64 - 1)))] =
    some (.v256 (pack256 (BitVec.ofNat 64 (2^64 - 2)) 0 51 (BitVec.ofNat 64 (2^64 - 2)))) := by decide

-- Vector logical shifts saturate beyond the lane width; scalar CIL masks counts.
example : evalIntrinsic (.avx2 .shr64) [.v256 (pack256 1 2 3 4), .i32 64] =
    some (.v256 0) := by decide

example : evalIntrinsic (.avx2 .shl64) [.v256 (pack256 1 2 3 4), .i32 64] =
    some (.v256 0) := by decide

example : evalIntrinsic (.avx2 .add64)
    [.v256 (pack256 (BitVec.ofNat 64 (2^64 - 1)) 2 3 4),
     .v256 (pack256 1 5 7 9)] = some (.v256 (pack256 0 7 10 13)) := by decide

example : evalIntrinsic (.avx2 .eq64)
    [.v256 (pack256 1 2 3 4), .v256 (pack256 1 7 3 9)] =
    some (.v256 (pack256 (~~~0) 0 (~~~0) 0)) := by decide

example : evalIntrinsic (.vector (.createScalar32 256)) [.i32 (BitVec.ofNat 32 (2^32 - 1))] =
    some (.v256 (BitVec.ofNat 256 (2^32 - 1))) := by decide

example : evalIntrinsic (.vector (.sum64 256))
    [.v256 (pack256 (BitVec.ofNat 64 (2^64 - 1)) 1 0 0)] = some (.i64 0) := by decide

example : evalIntrinsic (.avx .moveMask32)
    [.v256 (BitVec.ofNat 256 (2^31 + 2^255))] = some (.i32 129) := by decide

example : evalIntrinsic (.avx512 .gtu64)
    [.v256 (pack256 (BitVec.ofNat 64 (2^63)) 0 0 0), .v256 0] =
    some (.v256 (pack256 (~~~0) 0 0 0)) := by decide

example : evalIntrinsic (.avx2 .signedgt64)
    [.v256 (pack256 (BitVec.ofNat 64 (2^63)) 0 0 0), .v256 0] = some (.v256 0) := by decide

example : evalIntrinsic (.bmi2 .multiplyHigh64) [.i32 1, .i32 2] = none := by rfl

example : Intrinsic.available FeatureProfile.scalar (.bmi2 .multiplyHigh64) = false := rfl

example : Intrinsic.available { architecture := .x64, bmi2 := true }
    (.bmi2 .multiplyHigh64) = true := rfl

example : evalIntrinsic (.avx512 .ltu64) [.v256 0] = none := by rfl

end CIL.ExpansionTests
