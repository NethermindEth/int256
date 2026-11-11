import UInt256.Methods.Subtract.ScalarSafetySetup
import UInt256.Safety.CallerSetup
import CIL.Safety.AccessBelow
import CIL.Safety.StepComposition
import CIL.Safety.GuardNormalization
import CIL.Safety.MethodContract
import CIL.Safety.LocalSnapshotSteps

/-! The extracted scalar body's shared prefix: the right low limb is saved in a private home
    and the upper right limbs are or-combined for the first branch. -/

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety

def scalarFirstDecision : Nat := scalarBody.code.findIdx fun op =>
  match op with | .brnonzero _ => true | _ => false

/-- Save the right low limb and or-combine its upper limbs from the initial caller bytes. The
    remembered limb, caller bytes and access authority reach the first branch. -/
theorem scalar_right_prefix_checked (memory entered : Memory) (left right output : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (setup : enterFrame scalarBody (binaryArguments left right output) memory = .ok (frame, entered))
    (homes : WordHomes entered memory.nextIdentity scalarLocalSpecs frame.locals)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      LocalSnapshots after frame.locals
        (rememberLocal (fun _ => none) 0 (.i64 (inputLimb memory right 0))) →
      MemoryBelow memory.nextIdentity memory after →
      CallingConditions Extracted.program after [left, right] [output] →
      AccessBelow entered.nextIdentity entered after →
      memory.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel scalarIndex scalarFirstDecision (binaryArguments left right output) frame
          [.scalar (.i64 (inputLimb memory right 1 ||| inputLimb memory right 2 ||| inputLimb memory right 3))]
          after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel scalarIndex 0 (binaryArguments left right output) frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨reference, slot, _, _, writable⟩ := homes.word_at 0 0 (by rfl)
  have writableHomes := homes.writable
  have enteredCall := call.after_frame_setup setup
  have enteredFormed := enteredCall.1.1
  have preserved := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  cil_contract_steps (snapshots := LocalSnapshots.empty entered frame.locals)
    [found, binaryArguments, enteredCall.input_formed (reference := right) (by simp),
      call.input_field_after_setup setup (by simp : right ∈ [left, right]) 0]
  have afterCall := call.after_memory_below preserved localFormed
    (write_preserves_static_world _ _ _ _ _ _ enteredCall.2 localWrite)
  have done := continuation storedLocal localSnapshots preserved afterCall localAccess
    (Nat.le_trans (enterFrame_fresh _ _ _ _ _ setup).1.next
      (write_extends_allocations _ _ _ _ _ localWrite).next)
  conv at done in scalarFirstDecision => cbv
  have upperReads (index : Fin 4) (rest : List Value) :
      instruction (.fieldAt (8 * index.val) 8) (.reference (.address right) :: rest) storedLocal =
        .ok (storedLocal, .scalar (.i64 (inputLimb memory right index)) :: rest) := by
    rw [afterCall.input_field_instruction (by simp) index rest]
    simp only [inputLimb, call.input_bytes_of_memory_below preserved (reference := right) (by simp)]
  cil_contract_steps [found, binaryArguments,
    afterCall.input_formed (reference := right) (by simp), upperReads] until done

end UInt256Proof.Subtract.Safety
