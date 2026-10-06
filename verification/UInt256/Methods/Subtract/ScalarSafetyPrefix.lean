import UInt256.Methods.Subtract.ScalarSafetySetup
import UInt256.Safety.CallerSetup
import CIL.Safety.AccessBelow
import CIL.Safety.StepComposition

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety

def scalarFirstDecision : Nat := scalarBody.code.findIdx fun op =>
  match op with | .brnonzero _ => true | _ => false

theorem scalar_right_store (memory entered : Memory) (left right output : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (setup : enterFrame scalarBody (binaryArguments left right output) memory = .ok (frame, entered))
    (homes : WordHomes entered memory.nextIdentity scalarLocalSpecs frame.locals) :
    ∃ reference after,
      frame.locals[0]? = some (.bytes .word64 reference) ∧
      read after reference 8 1 = .ok (numberBytes (inputLimb memory right 0).toNat 8) ∧
      MemoryBelow memory.nextIdentity memory after ∧
      CallingConditions Extracted.program after [left, right] [output] ∧
      AccessBelow entered.nextIdentity entered after ∧
      ∀ pc rest, step scalarBody (.setLocal 0) pc (binaryArguments left right output) frame
        (.scalar (.i64 (inputLimb memory right 0)) :: rest) entered = .ok (.next (pc + 1) rest frame after) := by
  have specified : scalarLocalSpecs[0]? = some (some 0) := by rfl
  obtain ⟨reference, slot, bound, _, writable⟩ := homes.word_at 0 0 specified
  obtain ⟨after, written, _, loaded, _⟩ := store_local_word64 (inputLimb memory right 0) writable
  have preserved := (enterFrame_preserves_caller_memory _ _ _ _ _ setup).trans
    (write_preserves_memory_below _ _ _ _ _ _ bound written)
  have enteredCall := call.after_frame_setup setup
  refine ⟨reference, after, slot, loaded, preserved,
    call.after_memory_below preserved (write_preserves_wellFormed _ _ _ _ _ enteredCall.1.1 written)
      (write_preserves_static_world _ _ _ _ _ _ enteredCall.2 written),
    write_preserves_access_below written _, ?_⟩
  intro pc rest
  obtain ⟨result, stepped, sameWrite, _⟩ := step_store_word64_same_frame
    (body := scalarBody) (pc := pc) (args := binaryArguments left right output) (rest := rest)
    (inputLimb memory right 0) slot writable
  rw [written] at sameWrite
  cases sameWrite
  exact stepped

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
      ∃ fuel result returned,
        run Extracted.program fuel scalarIndex scalarFirstDecision (binaryArguments left right output) frame
          [.scalar (.i64 (inputLimb memory right 1 ||| inputLimb memory right 2 ||| inputLimb memory right 3))]
          after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel scalarIndex 0 (binaryArguments left right output) frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨reference, after, slot, loaded, preserved, afterCall, authority, stored⟩ :=
    scalar_right_store memory entered left right output frame call setup homes
  have done := continuation reference after slot loaded preserved afterCall authority
  conv at done in scalarFirstDecision => cbv
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  have beforeFormed := (call.after_frame_setup setup).input_formed (reference := right) (by simp)
  have afterFormed := afterCall.input_formed (reference := right) (by simp)
  have firstRead := call.input_field_after_setup setup (by simp : right ∈ [left, right]) 0
  have upperReads (index : Fin 4) (rest : List Value) :
      instruction (.field index) (.reference (.address right) :: rest) after =
        .ok (after, .scalar (.i64 (inputLimb memory right index)) :: rest) := by
    rw [afterCall.input_field_instruction (by simp) index rest]
    simp only [inputLimb, call.input_bytes_of_memory_below preserved (reference := right) (by simp)]
  repeat' first
    | exact done
    | (simp (config := { failIfUnchanged := false }) [BitVec.ofNat_eq_ofNat]
       apply run_next_exists post found (by rfl)
       first
       | exact stored _ _
       | (simp (config := { implicitDefEqProofs := false })
           [step, binaryArguments, checkedValue, numericValue, formValue, beforeFormed, afterFormed,
             firstRead, upperReads, pureArity, scalars, CIL.step, CIL.binary, checkedAt,
             Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms scalar_right_store
#print axioms scalar_right_prefix_checked
end UInt256Proof.Subtract.Safety
