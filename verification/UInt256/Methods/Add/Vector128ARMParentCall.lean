import UInt256.Methods.Add.Vector128ARMContract
import CIL.Safety.CallComposition

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- The actual scalar dispatcher's vector call and forwarding return use the
    independently certified helper and its proved scalar result shape. -/
theorem vector128_arm_parent_call (enabled : Extracted.profile.advSimd = true)
    (memory : Memory) (left right output : Reference) (flag : BitVec 32) (frame : Frame)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (post : Memory → List Value → Prop)
    (continuation : ∀ childFuel final returnedFlag,
      InvocationCertificate Extracted.program vector128Index (vector128Arguments left right output flag)
        memory childFuel
        final [.scalar (.i32 returnedFlag)] →
      inputValue final output = inputValue memory left + inputValue memory right →
      (flag ≠ BitVec.ofNat 32 0 → returnedFlag =
        if 2^256 ≤ (inputValue memory left).toNat + (inputValue memory right).toNat then 1 else 0) →
      access final output 32 1 true = .ok () →
      (∀ id offset, id < memory.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset) →
      post (leaveFrame frame final) [.scalar (.i32 returnedFlag)]) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex 25 (vector128Arguments left right output flag)
        frame [] memory = .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    obtain ⟨childFuel, final, returnedFlag, certified, result, overflow, writable, footprint⟩ :=
      checked_vector128_arm_contract enabled memory left right output flag call
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    have found : Extracted.program[Extracted.addScalarIndex]? = some Extracted.addScalarBody := by rfl
    have fetched : Extracted.addScalarBody.code[29]? = some (.call vector128Index 4) := by rfl
    have stepped : step Extracted.addScalarBody (.call vector128Index 4) 29
        (vector128Arguments left right output flag) frame
        [.scalar (.i32 flag), .reference (.address output), .reference (.address right), .reference (.address left)] memory =
        .ok (.call vector128Index (vector128Arguments left right output flag) [] memory) := by
      simp [step, vector128Arguments, checkedValue, numericValue, formValue, fl, fr, fo,
        checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    have returned : run Extracted.program 1 Extracted.addScalarIndex 30
        (vector128Arguments left right output flag) frame [.scalar (.i32 returnedFlag)] final =
        .ok (leaveFrame frame final, [.scalar (.i32 returnedFlag)]) := by
      simp [run, found, cil_code, step, checkedValue, numericValue, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    obtain ⟨fuel, executed⟩ := run_call_exists found fetched stepped ⟨_, certified.1⟩ ⟨1, returned⟩
    have done := continuation childFuel final returnedFlag certified result overflow writable footprint
    have finish : ∃ fuel final returned,
        run Extracted.program fuel Extracted.addScalarIndex 29 (vector128Arguments left right output flag)
          frame [.scalar (.i32 flag), .reference (.address output), .reference (.address right), .reference (.address left)] memory =
          .ok (final, returned) ∧ post final returned := ⟨fuel, _, _, executed, done⟩
    repeat' first
      | exact finish
      | (apply run_next_exists post found (by rfl)
         simp (config := { implicitDefEqProofs := false })
           [step, vector128Arguments, checkedValue, numericValue, formValue, fl, fr, fo,
             checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
         first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

#print axioms vector128_arm_parent_call
end UInt256Proof.Add.Safety
