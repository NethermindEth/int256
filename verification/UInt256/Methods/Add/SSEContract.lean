import UInt256.Methods.Add.SSEScalar
import UInt256.Methods.Add.ARMContract
import UInt256.Methods.Add.ARMOverflowContract

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- SSE4.2 Add: public entry, scalar dispatcher, vector helper with carry repair, portable small helper. -/
theorem checked_sse_add_contract (program : CIL.Program) (entry scalar vector carry small storage : Nat)
    (profile : CIL.FeatureProfile) (disabled : profile.advSimd = false) (noAvx2 : profile.avx2 = false)
    (sse2 : profile.sse2 = true) (ssse3 : profile.ssse3 = true) (sse42 : profile.sse42 = true)
    (entryFound : program[entry]? = some (publicScalarBody profile scalar))
    (scalarFound : program[scalar]? = some (sseScalarBody profile vector small))
    (vectorFound : program[vector]? = some (sseBody profile carry storage))
    (carryFound : program[carry]? = some (UInt256Proof.Add.CarrySafety.carryBody profile))
    (smallFound : program[small]? = some (portableSmallBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile)) :
    WrappingBinaryContract (· + ·) program entry := by
  apply add_contract_of_scalar program entry scalar profile entryFound noAvx2
  intro memory left right output call
  simpa only [vector128Arguments, binaryArguments, List.cons_append, List.nil_append] using
    checked_sse_scalar_contract program scalar vector small carry storage profile scalarFound vectorFound smallFound carryFound storageFound
      disabled sse2 ssse3 sse42 memory left right output 0 rfl call

/-- SSE4.2 AddOverflow: exact carry and wrapping sum through the same certified call graph. -/
theorem checked_sse_add_overflow_contract (program : CIL.Program) (entry scalar vector carry small storage : Nat)
    (profile : CIL.FeatureProfile) (disabled : profile.advSimd = false) (noAvx2 : profile.avx2 = false)
    (sse2 : profile.sse2 = true) (ssse3 : profile.ssse3 = true) (sse42 : profile.sse42 = true)
    (entryFound : program[entry]? = some (publicReportingBody profile scalar))
    (scalarFound : program[scalar]? = some (sseScalarBody profile vector small))
    (vectorFound : program[vector]? = some (sseBody profile carry storage))
    (carryFound : program[carry]? = some (UInt256Proof.Add.CarrySafety.carryBody profile))
    (smallFound : program[small]? = some (portableSmallBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile)) :
    ReportingBinaryContract (· + ·) (fun left right => decide (2^256 ≤ left.toNat + right.toNat)) program entry := by
  apply add_overflow_contract_of_scalar program entry scalar profile entryFound noAvx2
  intro memory left right output call
  simpa only [vector128Arguments, binaryArguments, List.cons_append, List.nil_append] using
    checked_sse_scalar_contract program scalar vector small carry storage profile scalarFound vectorFound smallFound carryFound storageFound
      disabled sse2 ssse3 sse42 memory left right output 1 rfl call

#print axioms checked_sse_add_contract
#print axioms checked_sse_add_overflow_contract
end UInt256Proof.Add.Safety
