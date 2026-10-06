import UInt256.Methods.Add.ARMSmallContract
import CIL.Safety.CallComposition

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- The scalar dispatcher calls the certified small helper and forwards its
    proved scalar flag. No arithmetic contract is assigned to an unproved body. -/
theorem arm_small_parent_call (enabled : Extracted.profile.advSimd = true)
    (memory : Memory) (input output : Reference) (word : BitVec 64) (frame : Frame)
    (args : List Value) (call : CallingConditions Extracted.program memory [input] [output])
    (post : Memory → List Value → Prop)
    (continuation : ∀ childFuel final returned,
      InvocationCertificate Extracted.program Extracted.addScalarUInt64Index
        (armSmallArguments input output word) memory childFuel final returned →
      ARMSmallPost memory final returned input output word →
      post (leaveFrame frame final) returned) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex 39 args frame
        [.reference (.address output), .scalar (.i64 word), .reference (.address input)] memory =
          .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    obtain ⟨childFuel, final, returned, certified, result⟩ :=
      checked_arm_small_contract enabled memory input output word call
    have fi := call.input_formed (reference := input) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    have found : Extracted.program[Extracted.addScalarIndex]? = some Extracted.addScalarBody := by rfl
    have fetched : Extracted.addScalarBody.code[39]? = some (.call Extracted.addScalarUInt64Index 3) := by rfl
    have stepped : step Extracted.addScalarBody (.call Extracted.addScalarUInt64Index 3) 39 args frame
        [.reference (.address output), .scalar (.i64 word), .reference (.address input)] memory =
          .ok (.call Extracted.addScalarUInt64Index (armSmallArguments input output word) [] memory) := by
      simp [step, armSmallArguments, checkedValue, numericValue, formValue, fi, fo,
        checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    have returnedRun : run Extracted.program 1 Extracted.addScalarIndex 40 args frame (returned ++ []) final =
        .ok (leaveFrame frame final, returned) := by
      rw [result.flag]
      simp [run, found, cil_code, step, checkedValue, numericValue, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    obtain ⟨fuel, executed⟩ := run_call_exists found fetched stepped
      ⟨childFuel, certified.1⟩ ⟨1, returnedRun⟩
    exact ⟨fuel, leaveFrame frame final, returned, executed,
      continuation childFuel final returned certified result⟩

#print axioms arm_small_parent_call
end UInt256Proof.Add.Safety
