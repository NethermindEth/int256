import UInt256.Methods.Subtract.Vector128Contract
import UInt256.Methods.Subtract.ScalarSafetyPrefix
import CIL.Safety.CallComposition

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Follow the large-operand feature guards, invoke the proved vector helper,
    and forward its exact flag through the parent return. -/
theorem vector128_parent_call (memory : Memory) (left right output : Reference)
    (upper : BitVec 64) (large : upper ≠ BitVec.ofNat 64 0) (frame : Frame)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (post : Memory → List Value → Prop)
    (continuation : ∀ childFuel final,
      InvocationCertificate Extracted.program vector128Index (binaryArguments left right output)
        memory childFuel final [.scalar (.i32 (subtractUnderflow memory left right))] →
      inputValue final output = inputValue memory left - inputValue memory right →
      access final output 32 1 true = .ok () →
      (∀ id offset, id < memory.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset) →
      post (leaveFrame frame final) [.scalar (.i32 (subtractUnderflow memory left right))]) :
    ∃ fuel final returned,
      run Extracted.program fuel scalarIndex scalarFirstDecision (binaryArguments left right output)
        frame [.scalar (.i64 upper)] memory = .ok (final, returned) ∧ post final returned := by
  let args := binaryArguments left right output
  obtain ⟨childFuel, final, certified, result, writable, footprint⟩ :=
    checked_vector128_contract memory left right output call
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have fo := call.output_formed (reference := output) (by simp)
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  have fetched : scalarBody.code[24]? = some (.call vector128Index 3) := by rfl
  have stepped : step scalarBody (.call vector128Index 3) 24 args frame
      [.reference (.address output), .reference (.address right), .reference (.address left)] memory =
      .ok (.call vector128Index args [] memory) := by
    simp [args, binaryArguments, step, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have returned : run Extracted.program 1 scalarIndex 25 args frame
      [.scalar (.i32 (subtractUnderflow memory left right))] final =
      .ok (leaveFrame frame final, [.scalar (.i32 (subtractUnderflow memory left right))]) := by
    simp [run, found, show scalarBody.code[25]? = some .ret from rfl,
      show scalarBody.returnsValue = true from rfl, step, checkedValue, numericValue, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨fuel, executed⟩ := run_call_exists found fetched stepped ⟨_, certified.1⟩ ⟨1, returned⟩
  have finish : ∃ fuel final returned,
      run Extracted.program fuel scalarIndex 24 args frame
        [.reference (.address output), .reference (.address right), .reference (.address left)] memory =
        .ok (final, returned) ∧ post final returned :=
    ⟨fuel, _, _, executed, continuation childFuel final certified result writable footprint⟩
  have profile : scalarBody.profile = Extracted.profile := by rfl
  conv in scalarFirstDecision => cbv
  repeat' first
    | exact finish
    | (simp (config := { failIfUnchanged := false }) [BitVec.ofNat_eq_ofNat, large]
       apply run_next_exists post found (by rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, args, binaryArguments, profile, cil_code, pureArity, scalars, CIL.step, CIL.FeatureProfile.evaluate,
           checkedValue, numericValue, formValue, fl, fr, fo,
           checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

#print axioms vector128_parent_call
end UInt256Proof.Subtract.Safety
