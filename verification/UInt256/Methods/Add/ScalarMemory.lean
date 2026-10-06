import UInt256.Methods.Add.ScalarSetup
import UInt256.Methods.Add.ScalarPrefix
import UInt256.Safety.CallerSetup
import CIL.Safety.AccessBelow

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

/-- The first local write is justified by fresh frame storage. All original
    caller bytes and permissions survive, including arbitrarily aliased inputs. -/
theorem scalar_right_store (memory entered : CIL.Safety.Memory)
    (left right output : Reference) (args : List Value) (frame : Frame)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (setup : enterFrame Extracted.addScalarBody args memory = .ok (frame, entered))
    (homes : WordHomes entered memory.nextIdentity scalarLocalSpecs frame.locals) :
    ∃ reference after,
      frame.locals[0]? = some (.bytes .word64 reference) ∧
      read after reference 8 1 = .ok (numberBytes (inputLimb memory right 0).toNat 8) ∧
      MemoryBelow memory.nextIdentity memory after ∧
      CallingConditions Extracted.program after [left, right] [output] ∧
      AccessBelow entered.nextIdentity entered after ∧
      ∀ pc rest,
        step Extracted.addScalarBody (.setLocal 0) pc args frame
          (.scalar (.i64 (inputLimb memory right 0)) :: rest) entered =
            .ok (.next (pc + 1) rest frame after) := by
  have specified : scalarLocalSpecs[0]? = some (some 0) := by
    simp [scalarLocalSpecs, cil_code]
  obtain ⟨reference, slot, bound, _, writable⟩ := homes.word_at 0 0 specified
  obtain ⟨after, written, stored, loaded, _⟩ := store_local_word64 (inputLimb memory right 0) writable
  have caller := (enterFrame_preserves_caller_memory _ _ _ _ _ setup).trans
    (write_preserves_memory_below _ _ _ _ _ _ bound written)
  have enteredCall := call.after_frame_setup setup
  have afterWF := write_preserves_wellFormed _ _ _ _ _ enteredCall.1.1 written
  have afterWorld := write_preserves_static_world _ _ _ _ _ _ enteredCall.2 written
  refine ⟨reference, after, slot, loaded, caller,
    call.after_memory_below caller afterWF afterWorld,
    write_preserves_access_below written _, ?_⟩
  intro pc rest
  obtain ⟨result, stepped, sameWrite, _⟩ := step_store_word64_same_frame
    (body := Extracted.addScalarBody) (pc := pc) (args := args) (rest := rest)
    (inputLimb memory right 0) slot writable
  rw [written] at sameWrite
  cases sameWrite
  exact stepped

/-- Discharge every prefix memory operation from ordinary calling conditions
    and actual frame setup. Only the branch continuation remains to be proved. -/
theorem scalar_right_prefix_checked (memory entered : CIL.Safety.Memory)
    (left right output : Reference) (extra : List Value) (frame : Frame)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (setup : enterFrame Extracted.addScalarBody (binaryArguments left right output ++ extra)
      memory = .ok (frame, entered))
    (homes : WordHomes entered memory.nextIdentity scalarLocalSpecs frame.locals)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[0]? = some (.bytes .word64 reference) →
      read after reference 8 1 = .ok (numberBytes (inputLimb memory right 0).toNat 8) →
      MemoryBelow memory.nextIdentity memory after →
      CallingConditions Extracted.program after [left, right] [output] →
      AccessBelow entered.nextIdentity entered after →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarIndex scalarFirstDecision
          (binaryArguments left right output ++ extra) frame
          [.scalar (.i64 (inputLimb memory right 1 ||| inputLimb memory right 2 |||
            inputLimb memory right 3))] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex 0
        (binaryArguments left right output ++ extra) frame [] entered = .ok (result, returned) ∧
      post result returned := by
  obtain ⟨reference, after, slot, loaded, preserved, afterCall, authority, stored⟩ :=
    scalar_right_store memory entered left right output _ frame call setup homes
  apply scalar_right_prefix left right output extra (inputLimb memory right) frame entered after
    ((call.after_frame_setup setup).input_formed (by simp)) (afterCall.input_formed (by simp))
    (fun rest => call.input_field_after_setup setup (by simp) 0 rest) ?_ stored post
    (continuation reference after slot loaded preserved afterCall authority)
  intro index rest
  rw [afterCall.input_field_instruction (by simp) index rest]
  simp only [inputLimb, call.input_bytes_of_memory_below preserved (reference := right) (by simp)]

#print axioms scalar_right_store
#print axioms scalar_right_prefix_checked

end UInt256Proof.Safety
