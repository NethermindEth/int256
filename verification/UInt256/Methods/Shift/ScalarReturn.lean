import UInt256.Methods.StoreLimbsContract
import UInt256.Methods.Shift.ScalarOutput
import UInt256.Methods.StorageScalar
import CIL.Safety.CallComposition
import CIL.Safety.ReturnMemory

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety
variable {profile : CIL.FeatureProfile} {direction : Direction} {storage : Nat}
  {program : CIL.Program} {index : Nat}
  (bodyFound : program[index]? = some (scalarBody profile direction storage))
  (store : StoreLimbsContract program storage)

include bodyFound store

/-- Execute the checked storage call and retire only this shift's private frame. -/
theorem shift_store_return (whole : Fin 4) (memory : Memory) (inputs : List Reference)
    (frame : Frame) (args : List Value) (output : Reference) (boundary : Nat)
    (w0 w1 w2 w3 : BitVec 64)
    (call : CallingConditions program memory inputs [output])
    (outputOld : output.allocation < boundary)
    (owned : ∀ id ∈ frame.owned, boundary ≤ id) :
    ∃ fuel final returned,
      run program fuel index (outputCall whole) args frame
        [.scalar (.i64 w3), .scalar (.i64 w2), .scalar (.i64 w1), .scalar (.i64 w0),
          .reference (.address output)] memory = .ok (final, returned) ∧
      returned = [] ∧ final.WellFormed ∧
      inputValue final output = BitVec.ofNat 256
        (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192) ∧
      access final output 32 1 true = .ok () ∧
      (∃ bytes, read final output 32 1 = .ok bytes) ∧
      (∀ id, id < boundary → ∀ offset, OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset) := by
  have cases : whole = 0 ∨ whole = 1 ∨ whole = 2 ∨ whole = 3 := by omega
  have fetched : (scalarBody profile direction storage).code[outputCall whole]? = some (.call storage 5) := by
    cases direction <;> rcases cases with rfl | rfl | rfl | rfl <;> rfl
  have returned : (scalarBody profile direction storage).code[outputCall whole + 1]? = some .ret := by
    cases direction <;> rcases cases with rfl | rfl | rfl | rfl <;> rfl
  have formed := call.output_formed (by simp : output ∈ [output])
  have stepped : step (scalarBody profile direction storage) (.call storage 5) (outputCall whole)
      args frame [.scalar (.i64 w3), .scalar (.i64 w2), .scalar (.i64 w1), .scalar (.i64 w0),
        .reference (.address output)] memory =
      .ok (.call storage (UInt256Proof.StorageScalar.arguments output w0 w1 w2 w3) [] memory) := by
    simp [step, UInt256Proof.StorageScalar.arguments, checkedValue, numericValue, formValue, formed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨childFuel, stored, invoked, valid, outside, authority, value, readable⟩ :=
    store
      memory inputs output w0 w1 w2 w3 call
  have tail : run program 1 index (outputCall whole + 1) args frame [] stored =
      .ok (leaveFrame frame stored, []) := run_return bodyFound returned (by rfl) (by rfl)
  obtain ⟨fuel, finished⟩ := run_call_exists bodyFound fetched stepped ⟨childFuel, invoked⟩ ⟨1, tail⟩
  have retained := leaveFrame_preserves_memory_below frame stored boundary owned
  have bytes : (fun offset => ((leaveFrame frame stored).cells output.allocation offset).bits) =
      (fun offset => (stored.cells output.allocation offset).bits) := by
    funext offset
    rw [retained.cells output.allocation outputOld offset]
  refine ⟨fuel, leaveFrame frame stored, [], finished, rfl,
    leaveFrame_preserves_wellFormed _ _ valid.1.1, ?_,
    (retained.access output outputOld 32 1 true).trans
      (valid.1.2.2 (wordView output) (by simp)), ?_, ?_⟩
  · simpa only [inputValue, bytes] using value
  · obtain ⟨snapshot, loaded⟩ := readable
    exact ⟨snapshot, (retained.read output outputOld 32 1).trans loaded⟩
  · intro id old offset untouched
    exact (retained.cells id old offset).trans (outside id offset untouched)

#print axioms shift_store_return
end UInt256Proof.Shift.Safety
