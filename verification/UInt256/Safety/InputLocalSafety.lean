import CIL.Safety.Equations
import CIL.Safety.Segment
import UInt256.Safety.LocalCallSafety

/-! Input loads and private local stores composed as checked execution segments. -/

namespace UInt256Model.Safety
open CIL.Safety

/-- Read one original input limb and store it while preserving private-local state. -/
theorem run_input_to_local {program : CIL.Program} {method pc argument target : Nat} {body : CIL.Method}
    {original entered current : Memory} {inputs outputs : List Reference} {frame : Frame}
    {known : Nat → Option (BitVec 64)} {args rest : List Value} {kinds : List CIL.LocalKind}
    (state : PrivateWords program original entered current inputs outputs frame known)
    (originalCall : CallingConditions program original inputs outputs) (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity kinds frame.locals)
    (input : Reference) (member : input ∈ inputs) (limb : Fin 4)
    (arg : args[argument]? = some (.reference (.address input)))
    (kind : kinds[target]? = some .word64)
    (found : program[method]? = some body)
    (code : CodeAt body pc [.arg argument, .fieldAt (8 * limb.val) 8, .setLocal target])
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after inputs outputs frame
        (rememberWord known target (inputLimb original input limb)) →
      ∃ fuel final returned, run program fuel method (pc + 3) args frame rest after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned, run program fuel method pc args frame rest current = .ok (final, returned) ∧ post final returned := by
  have formed := state.call.input_formed member
  have reading := state.input_field originalCall input member limb rest
  obtain ⟨after, stored, next⟩ := state.store enteredWF homes target kind (inputLimb original input limb)
    (pc + 2) args rest (body := body)
  have readingSegment : Segment program method pc (pc + 2)
      (SegmentState.exact args ⟨frame, rest, current⟩)
      (SegmentState.exact args
        ⟨frame, .scalar (.i64 (inputLimb original input limb)) :: rest, current⟩) := by
    cil_segment 2 [found, code, arg, formed, reading]
  have storingSegment : Segment program method (pc + 2) (pc + 3)
      (SegmentState.exact args
        ⟨frame, .scalar (.i64 (inputLimb original input limb)) :: rest, current⟩)
      (SegmentState.exact args ⟨frame, rest, after⟩) := by
    cil_segment 1 [found, code, stored]
  apply (readingSegment.trans storingSegment).run_exists args ⟨frame, rest, current⟩
    ⟨rfl, rfl⟩ post
  intro final valid
  rcases valid with ⟨_, rfl⟩
  exact continuation after next

#print axioms run_input_to_local
end UInt256Model.Safety
