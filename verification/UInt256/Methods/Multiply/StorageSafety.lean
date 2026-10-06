import UInt256.Methods.Add.StorageContract
import CIL.Safety.CallComposition

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety

def productStoreIndex : Nat := Extracted.program.findIdx fun body =>
  body.locals.isEmpty && match body.code with
    | .feature .vector256Accelerated :: _ => true
    | _ => false

def productStoreBody : CIL.Method := Extracted.program[productStoreIndex]?.getD
  { code := [], locals := [], returnsValue := false }

/-- Both product-storage routes reuse the checked four-limb writer. The scalar
    route also checks its feature branch, forwarding call and empty-frame return. -/
theorem store_product_contract (memory : Memory) (inputs : List Reference) (output : Reference)
    (w0 w1 w2 w3 : BitVec 64)
    (call : CallingConditions Extracted.program memory inputs [output]) :
    ∃ fuel result,
      invoke Extracted.program fuel productStoreIndex
        [.reference (.address output), .scalar (.i64 w0), .scalar (.i64 w1), .scalar (.i64 w2), .scalar (.i64 w3)]
        memory = .ok (result, []) ∧
      CallingConditions Extracted.program result inputs [output] ∧
      (∀ id offset, OutsideOutput output id offset → result.cells id offset = memory.cells id offset) ∧
      AccessBelow memory.nextIdentity memory result ∧
      inputValue result output = BitVec.ofNat 256
        (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192) ∧
      (∃ bytes, read result output 32 1 = .ok bytes) := by
  first
  | exact store_limbs_readable_contract memory inputs output w0 w1 w2 w3 call
  |
    obtain ⟨childFuel, stored, invoked, valid, outside, authority, value, readable⟩ :=
      store_limbs_readable_contract memory inputs output w0 w1 w2 w3 call
    let args := [Value.reference (.address output), .scalar (.i64 w0), .scalar (.i64 w1),
      .scalar (.i64 w2), .scalar (.i64 w3)]
    let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
    have found : Extracted.program[productStoreIndex]? = some productStoreBody := by rfl
    have profile : productStoreBody.profile = Extracted.profile := by rfl
    have formed := call.output_formed (by simp : output ∈ [output])
    have checked : args.mapM (checkedValue memory) = .ok args := by
      simp [args, checkedValue, numericValue, formValue, formed, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    have setup : enterFrame productStoreBody args memory = .ok (frame, memory) := by
      have locals : productStoreBody.locals = [] := by rfl
      have kinds : productStoreBody.localKinds = [] := by rfl
      have aggregates : productStoreBody.aggregateArgs = [] := by rfl
      simp [enterFrame, locals, kinds, aggregates, makeLocals, makeArgumentHomes, frame,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    have resume : run Extracted.program 1 productStoreIndex 19 args frame [] stored = .ok (stored, []) := by
      have fetched : productStoreBody.code[19]? = some .ret := by rfl
      rw [run]
      simp only [found, fetched]
      rfl
    have stepped : step productStoreBody (.call storageIndex 5) 18 args frame args.reverse memory =
        .ok (.call storageIndex args [] memory) := by
      simp [step, args, checkedValue, numericValue, formValue, formed, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    obtain ⟨tailFuel, tail⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, invoked⟩ ⟨1, resume⟩
    have started : ∃ fuel result returned,
        run Extracted.program fuel productStoreIndex 0 args frame [] memory = .ok (result, returned) ∧
        result = stored ∧ returned = [] := by
      iterate 7
        apply run_next_exists (fun result returned => result = stored ∧ returned = []) found (by rfl)
        simp (config := { implicitDefEqProofs := false })
          [step, args, profile, Extracted.profile, CIL.FeatureProfile.evaluate,
            checkedValue, numericValue, formValue, formed, checkedAt,
            pureArity, scalars, CIL.step, Except.mapError,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨tailFuel, stored, [], tail, rfl, rfl⟩
    obtain ⟨fuel, result, returned, ran, rfl, rfl⟩ := started
    refine ⟨fuel, result, ?_, valid, outside, authority, value, readable⟩
    change invoke Extracted.program fuel productStoreIndex args memory = _
    simpa only [invoke, found, checked, setup, Except.mapError, Bind.bind, Except.bind] using ran

#print axioms store_product_contract
end UInt256Proof.Multiply.Safety
