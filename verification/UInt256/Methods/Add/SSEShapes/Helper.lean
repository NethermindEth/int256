import UInt256.Methods.Add.SSEShapes.Composite
import UInt256.Methods.Add.SSEContract

namespace UInt256Proof.Add.SSEShapes
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety UInt256Proof.Add.CarrySafety UInt256Proof.Safety

/-- Segment positions shared by the inline-merge AddVector128 bodies. -/
def inlineMergeLayout : Layout :=
  { incomingDoubled := false, incoming := 50, earlyDoubled := false, propagation := 82, decisionDoubled := false,
    combine := 98, merge := none, join := 106, fast := 204, repairDoubled := false, repair := 162 }

/-- A shaped helper body meets the scalar dispatcher's helper contract. -/
theorem shaped_helper_contract (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (layout : Layout) (shaped : Shaped body layout)
    (start : StartContract program body method specs)
    (repair : RepairContract program method specs layout.repair)
    (firstFourteen : ∀ i : Fin 14, specs[i.val]? = some vector128ZeroSpec)
    (sse2 : body.profile.sse2 = true) (ssse3 : body.profile.ssse3 = true) (disabled : body.profile.advSimd = false)
    (mergeFound : ∀ index, layout.merge = some index → program[index]? = some (mergeBody body.profile))
    (returns : body.returnsValue = true)
    (metadata : body.localKinds = .reference :: specs.map NumericLocalSpec.kind ∧ body.locals = .nullRef :: specs.map NumericLocalSpec.value)
    (vectors : body.vectorArgs = []) (parameters : body.parameterHomes = []) :
    SSEHelperContract program method := fun memory left right output flag _ call =>
  checked_shaped_contract program body method specs found layout shaped start repair firstFourteen sse2 ssse3 disabled
    mergeFound returns metadata vectors parameters memory left right output flag call

/-- Helper with the extracted start and the per-limb carry-call repair. -/
theorem carry_helper_contract (program : CIL.Program) (body : CIL.Method) (method carry storage : Nat)
    (found : program[method]? = some body) (layout : Layout) (shaped : Shaped body layout)
    (prefixCode : body.code = vector128AddPrefix ++ body.code.drop 37)
    (repairCode : At body.code layout.repair (repairCodeOf false carry storage))
    (carryFound : program[carry]? = some (carryBody body.profile))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body body.profile))
    (sse2 : body.profile.sse2 = true) (ssse3 : body.profile.ssse3 = true) (disabled : body.profile.advSimd = false)
    (mergeFound : ∀ index, layout.merge = some index → program[index]? = some (mergeBody body.profile))
    (returns : body.returnsValue = true)
    (metadata : body.localKinds = .reference :: armSpecs.map NumericLocalSpec.kind ∧ body.locals = .nullRef :: armSpecs.map NumericLocalSpec.value)
    (vectors : body.vectorArgs = []) (parameters : body.parameterHomes = []) :
    SSEHelperContract program method :=
  shaped_helper_contract program body method armSpecs found layout shaped
    (prefix_start program body method armSpecs found _ prefixCode (fun i => armSpecs_first ⟨i.val, by omega⟩))
    (call_repair program body method armSpecs found layout.repair carry storage false repairCode carryFound storageFound
      armSpecs_words returns)
    armSpecs_first sse2 ssse3 disabled mergeFound returns metadata vectors parameters

/-- SSE4.2 Add through the public entry and scalar dispatcher, given helper contracts. -/
theorem checked_shaped_add (program : CIL.Program) (entry scalar vector small : Nat) (profile : CIL.FeatureProfile)
    (disabled : profile.advSimd = false) (noAvx2 : profile.avx2 = false) (sse42 : profile.sse42 = true)
    (entryFound : program[entry]? = some (publicScalarBody profile scalar))
    (scalarFound : program[scalar]? = some (sseScalarBody profile vector small))
    (helper : SSEHelperContract program vector) (smallContract : PortableSmallContract program small) :
    WrappingBinaryContract (· + ·) program entry := by
  apply add_contract_of_scalar program entry scalar profile entryFound noAvx2
  intro memory left right output call
  simpa only [vector128Arguments, binaryArguments, List.cons_append, List.nil_append] using
    checked_sse_scalar_contract_of program scalar vector small profile scalarFound helper smallContract
      disabled sse42 memory left right output 0 rfl call

/-- SSE4.2 AddOverflow through the public entry and scalar dispatcher, given helper contracts. -/
theorem checked_shaped_add_overflow (program : CIL.Program) (entry scalar vector small : Nat) (profile : CIL.FeatureProfile)
    (disabled : profile.advSimd = false) (noAvx2 : profile.avx2 = false) (sse42 : profile.sse42 = true)
    (entryFound : program[entry]? = some (publicReportingBody profile scalar))
    (scalarFound : program[scalar]? = some (sseScalarBody profile vector small))
    (helper : SSEHelperContract program vector) (smallContract : PortableSmallContract program small) :
    ReportingBinaryContract (· + ·) (fun left right => decide (2^256 ≤ left.toNat + right.toNat)) program entry := by
  apply add_overflow_contract_of_scalar program entry scalar profile entryFound noAvx2
  intro memory left right output call
  simpa only [vector128Arguments, binaryArguments, List.cons_append, List.nil_append] using
    checked_sse_scalar_contract_of program scalar vector small profile scalarFound helper smallContract
      disabled sse42 memory left right output 1 rfl call

#print axioms shaped_helper_contract
#print axioms carry_helper_contract
#print axioms checked_shaped_add
#print axioms checked_shaped_add_overflow
end UInt256Proof.Add.SSEShapes
