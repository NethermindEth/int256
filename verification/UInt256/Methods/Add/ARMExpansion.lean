import UInt256.Methods.Add.ARMOverflowContract
import UInt256.Safety.CodeExpansion

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- The ARM `Add` program in production method order. -/
def armProgram (profile : CIL.FeatureProfile) : CIL.Program :=
  [publicScalarBody profile 1, armScalarBody profile 2 3, armBody profile, armSmallBody profile 4,
    UInt256Proof.Multiply.LimbStorage.body profile]

/-- The ARM `AddOverflow` program in production method order. -/
def armReportingProgram (profile : CIL.FeatureProfile) : CIL.Program :=
  [publicReportingBody profile 1, armScalarBody profile 2 3, armBody profile, armSmallBody profile 4,
    UInt256Proof.Multiply.LimbStorage.body profile]

theorem arm_program_contract (profile : CIL.FeatureProfile) (enabled : profile.advSimd = true)
    (disabled : profile.avx2 = false) : WrappingBinaryContract (· + ·) (armProgram profile) 0 :=
  checked_arm_add_contract _ 0 1 2 3 4 profile enabled disabled rfl rfl rfl rfl rfl

theorem arm_reporting_program_contract (profile : CIL.FeatureProfile) (enabled : profile.advSimd = true)
    (disabled : profile.avx2 = false) :
    ReportingBinaryContract (· + ·) (fun left right => decide (2^256 ≤ left.toNat + right.toNat))
      (armReportingProgram profile) 0 :=
  checked_arm_add_overflow_contract _ 0 1 2 3 4 profile enabled disabled rfl rfl rfl rfl rfl

#print axioms arm_program_contract
#print axioms arm_reporting_program_contract
end UInt256Proof.Add.Safety
