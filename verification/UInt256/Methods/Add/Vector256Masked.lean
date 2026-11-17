import UInt256.Methods.Add.Vector256Entry

namespace UInt256Proof.Add.Vector256.Masked
open CIL.Safety UInt256Model.Safety UInt256Proof.Add.Safety UInt256Proof.Add.Vector256
variable {identity : Nat} {assembly : String}

theorem prepare_contract (program : CIL.Program) (method : Nat) (profile : CIL.FeatureProfile)
    (found : program[method]? = some (prepareMaskedBody profile)) (features : AddProfile profile false) :
    PrepareContract program method :=
  fun original memory left right output s0 s1 s2 s3 originalCall call grown same layout scratch =>
    prepare_invoke program method profile false _ (.inr ⟨rfl, rfl⟩) found features original memory
      left right output s0 s1 s2 s3 originalCall call grown same layout scratch

/-- AVX2 `Add` whose `PrepareAdd` masks the permuted carries with a constant lane mask. -/
theorem add_contract (program : CIL.Program) (profile : CIL.FeatureProfile)
    (entryFound : program[0]? = some (addEntryBody profile 1 3))
    (finishFound : program[1]? = some (finishAddBody profile 2))
    (lookupFound : program[2]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile identity assembly))
    (prepareFound : program[3]? = some (prepareMaskedBody profile))
    (features : AddProfile profile false) :
    WrappingBinaryContract (· + ·) program 0 :=
  add_contract_of_callees program profile false 1 3 entryFound
    (finish_contract program 1 2 profile false finishFound lookupFound features)
    (prepare_contract program 3 profile prepareFound features) features

/-- AVX2 `AddOverflow` whose `PrepareAdd` masks the permuted carries with a constant lane mask. -/
theorem add_overflow_contract (program : CIL.Program) (profile : CIL.FeatureProfile)
    (entryFound : program[0]? = some (addOverflowEntryBody profile 1 3))
    (finishFound : program[1]? = some (finishAddBody profile 2))
    (lookupFound : program[2]? = some (UInt256Proof.AddSubtract.Vector256.lookupBody profile identity assembly))
    (prepareFound : program[3]? = some (prepareMaskedBody profile))
    (features : AddProfile profile false) :
    ReportingBinaryContract (· + ·) (fun left right => decide (2^256 ≤ left.toNat + right.toNat)) program 0 :=
  add_overflow_contract_of_callees program profile false 1 3 entryFound
    (finish_contract program 1 2 profile false finishFound lookupFound features)
    (prepare_contract program 3 profile prepareFound features) features

end UInt256Proof.Add.Vector256.Masked
