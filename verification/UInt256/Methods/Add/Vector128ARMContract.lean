import UInt256.Methods.Add.Vector128ARMEntry
import CIL.Safety.ReturnArity

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def vector128Arguments (left right output : Reference) (flag : BitVec 32) : List Value :=
  [.reference (.address left), .reference (.address right), .reference (.address output), .scalar (.i32 flag)]

/-- Checked invocation of the extracted ARM helper. Valid caller views suffice
    to derive frame initialization and every visited reference/lifetime state. -/
theorem checked_vector128_arm_contract (enabled : Extracted.profile.advSimd = true)
    (memory : Memory) (left right output : Reference) (flag : BitVec 32)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ fuel final returned,
      InvocationCertificate Extracted.program vector128Index (vector128Arguments left right output flag)
        memory fuel final [.scalar (.i32 returned)] ∧
      inputValue final output = inputValue memory left + inputValue memory right ∧
      (flag ≠ BitVec.ofNat 32 0 → returned =
        if 2^256 ≤ (inputValue memory left).toNat + (inputValue memory right).toNat then 1 else 0) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < memory.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset) := by
  let args := vector128Arguments left right output flag
  obtain ⟨frame, entered, slots, setup, layout, homes, preserved, enteredWF⟩ :=
    vector128_frame_setup memory args call.1.1
  obtain ⟨fuel, final, returned, executed, scalar, result, writable, footprint⟩ :=
    vector128_arm_entry enabled memory entered [left, right] [output] left right output frame slots args
      call setup layout homes (by simp) (by simp) (by simp) rfl rfl rfl flag rfl
  obtain ⟨returnedValue, rfl, overflow⟩ := scalar
  have checked : args.mapM (checkedValue memory) = .ok args := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [args, vector128Arguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  exact ⟨fuel, final, returnedValue,
    certify_invocation Extracted.program vector128Index vector128Body args memory frame entered
      fuel final [.scalar (.i32 returnedValue)] (by rfl) checked setup live executed,
    result, overflow, writable, footprint⟩

#print axioms checked_vector128_arm_contract
end UInt256Proof.Add.Safety
