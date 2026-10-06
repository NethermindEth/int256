import UInt256.Methods.Shift.SafetyOutputMath
import UInt256.Methods.Add.StorageCall
import CIL.Safety.ReturnMemory

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety

/-- Invoke the current extracted storage helper and retire the parent frame;
    neither the helper nor its aliasing behavior is assumed. -/
theorem shift_store_return (whole : Fin 4) (memory : Memory) (inputs : List Reference)
    (frame : Frame) (args : List Value) (output : Reference) (boundary : Nat)
    (w0 w1 w2 w3 : BitVec 64)
    (call : CallingConditions Extracted.program memory inputs [output])
    (outputOld : output.allocation < boundary)
    (owned : ∀ id ∈ frame.owned, boundary ≤ id) :
    ∃ fuel final returned,
      run Extracted.program fuel shiftIndex (outputCall whole) args frame
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
  have fetched : shiftBody.code[outputCall whole]? = some (.call Extracted.storeLimbsIndex 5) := by
    rcases cases with rfl | rfl | rfl | rfl <;> rfl
  have returned : shiftBody.code[outputCall whole + 1]? = some .ret := by
    rcases cases with rfl | rfl | rfl | rfl <;> rfl
  have found : Extracted.program[shiftIndex]? = some shiftBody := by rfl
  have returns : shiftBody.returnsValue = false := by rfl
  have formed := call.output_formed (by simp : output ∈ [output])
  apply run_store_limbs_readable inputs output w0 w1 w2 w3 _ found fetched
  · unfold UInt256Proof.Safety.storageArguments
    repeat' (conv in UInt256Proof.Safety.storageWordOrder => cbv)
    simp [List.range_succ, List.findIdx, List.findIdx.go, step, checkedValue, numericValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl⟩
  · exact call
  · intro stored valid outside authority value readable
    have retained := leaveFrame_preserves_memory_below frame stored boundary owned
    have bytes : (fun offset => ((leaveFrame frame stored).cells output.allocation offset).bits) =
        (fun offset => (stored.cells output.allocation offset).bits) := by
      funext offset
      rw [retained.cells output.allocation outputOld offset]
    refine ⟨1, leaveFrame frame stored, [], ?_, rfl,
      leaveFrame_preserves_wellFormed _ _ valid.1.1, ?_,
      (retained.access output outputOld 32 1 true).trans
        (valid.1.2.2 (wordView output) (by simp)), ?_, ?_⟩
    · simp [run, found, returned, returns, step, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    · simpa only [inputValue, bytes] using value
    · obtain ⟨snapshot, loaded⟩ := readable
      exact ⟨snapshot, (retained.read output outputOld 32 1).trans loaded⟩
    · intro id old offset untouched
      exact (retained.cells id old offset).trans (outside id offset untouched)

#print axioms shift_store_return
end UInt256Proof.Shift.Safety
