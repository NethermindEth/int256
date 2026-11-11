import UInt256.Methods.Subtract.ScalarSafetySetup
import UInt256.Safety.CallerSetup
import CIL.Safety.AccessBelow
import CIL.Safety.StepComposition
import CIL.Safety.GuardNormalization
import CIL.Safety.MethodContract

/-! The extracted scalar body's shared prefix: the right low limb is saved in a private home
    and the upper right limbs are or-combined for the first branch. -/

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety

def scalarFirstDecision : Nat := scalarBody.code.findIdx fun op =>
  match op with | .brnonzero _ => true | _ => false

/-- Save the right low limb and or-combine its upper limbs from the initial caller bytes. The
    saved home, caller bytes and access authority reach the first branch. -/
theorem scalar_right_prefix_checked (memory entered : Memory) (left right output : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (setup : enterFrame scalarBody (binaryArguments left right output) memory = .ok (frame, entered))
    (homes : WordHomes entered memory.nextIdentity scalarLocalSpecs frame.locals)
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[0]? = some (.bytes .word64 reference) →
      read after reference 8 1 = .ok (numberBytes (inputLimb memory right 0).toNat 8) →
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
  have specified : scalarLocalSpecs[0]? = some (some 0) := by rfl
  obtain ⟨reference, slot, bound, _, writable⟩ := homes.word_at 0 0 specified
  obtain ⟨after, written, _, loaded, _⟩ := store_local_word64 (inputLimb memory right 0) writable
  have preserved := (enterFrame_preserves_caller_memory _ _ _ _ _ setup).trans
    (write_preserves_memory_below _ _ _ _ _ _ bound written)
  have enteredCall := call.after_frame_setup setup
  have afterCall := call.after_memory_below preserved
    (write_preserves_wellFormed _ _ _ _ _ enteredCall.1.1 written)
    (write_preserves_static_world _ _ _ _ _ _ enteredCall.2 written)
  have stored (pc : Nat) (rest : List Value) :
      step scalarBody (.setLocal 0) pc (binaryArguments left right output) frame
        (.scalar (.i64 (inputLimb memory right 0)) :: rest) entered =
          .ok (.next (pc + 1) rest frame after) := by
    obtain ⟨result, stepped, sameWrite, _⟩ := step_store_word64_same_frame
      (body := scalarBody) (pc := pc) (args := binaryArguments left right output) (rest := rest)
      (inputLimb memory right 0) slot writable
    rw [written] at sameWrite
    cases sameWrite
    exact stepped
  have done := continuation reference after slot loaded preserved afterCall
    (write_preserves_access_below written _)
    (Nat.le_trans (enterFrame_fresh _ _ _ _ _ setup).1.next
      (write_extends_allocations _ _ _ _ _ written).next)
  conv at done in scalarFirstDecision => cbv
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  have upperReads (index : Fin 4) (rest : List Value) :
      instruction (.fieldAt (8 * index.val) 8) (.reference (.address right) :: rest) after =
        .ok (after, .scalar (.i64 (inputLimb memory right index)) :: rest) := by
    rw [afterCall.input_field_instruction (by simp) index rest]
    simp only [inputLimb, call.input_bytes_of_memory_below preserved (reference := right) (by simp)]
  cil_contract_steps [found, binaryArguments,
    enteredCall.input_formed (reference := right) (by simp),
    afterCall.input_formed (reference := right) (by simp),
    call.input_field_after_setup setup (by simp : right ∈ [left, right]) 0,
    upperReads, stored] until done

end UInt256Proof.Subtract.Safety
