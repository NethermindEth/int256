import UInt256.Methods.Shift.ScalarBody
import UInt256.Safety.VectorFrame
import UInt256.Safety.LimbAccess
import UInt256.Methods.Add.InputWords
import CIL.Safety.LocalSnapshotSteps

/-!
The scalar shift body up to its output routes: select the whole-limb count through the signed
count branches, then save the bit counts and the four operand limbs in private locals.
-/

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety
variable {profile : CIL.FeatureProfile} {direction : Direction} {storage : Nat}
  {program : CIL.Program} {index : Nat}
  (bodyFound : program[index]? = some (scalarBody profile direction storage))
include bodyFound

/-- All signed count branches either reach the zero write or select a bounded whole-limb
    count, which local 0 then holds. -/
theorem shift_count_dispatch (original entered current : Memory) (input output : Reference)
    (frame : Frame) (args : List Value) (count : BitVec 32)
    (argument : args[1]? = some (.scalar (.i32 count)))
    (originalCall : CallingConditions program original [input] [output])
    (homes : CompleteWritableHomes entered original.nextIdentity (numericKinds shiftSpecs)
      frame.locals)
    (state : VectorFrame program original entered current [input] output frame (fun _ => none)
      none)
    (post : Memory → List Value → Prop)
    (zero : ∀ after known,
      ¬ count.sshiftRight 6 < BitVec.ofNat 32 4 →
      (0 ≤ (count.sshiftRight 6).toInt ∨ count &&& (63 : BitVec 32) = 0) →
      VectorFrame program original entered after [input] output frame known none →
      ∃ fuel final returned, run program fuel index 14 args frame [] after =
        .ok (final, returned) ∧ post final returned)
    (ready : ∀ whole after known,
      whole < BitVec.ofNat 32 4 →
      (whole = count.sshiftRight 6 ∨
        (whole = 0 ∧ (count.sshiftRight 6).toInt < 0 ∧ count &&& (63 : BitVec 32) ≠ 0)) →
      VectorFrame program original entered after [input] output frame known none →
      known 0 = some (.i32 whole) →
      ∃ fuel final returned, run program fuel index 19 args frame [] after =
        .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned, run program fuel index 0 args frame [] current =
      .ok (final, returned) ∧ post final returned := by
  have found := bodyFound
  cil_contract_steps 3 [argument]
  refine state.run_store (kind := .word32) post originalCall homes found fun middle state => ?_
  have unsigned : ∃ fuel final returned, run program fuel index
      (if count.sshiftRight 6 < BitVec.ofNat 32 4 then 19 else 7) args frame [] middle =
        .ok (final, returned) ∧ post final returned := by
    by_cases small : count.sshiftRight 6 < BitVec.ofNat 32 4
    · simpa only [small, ↓reduceIte] using ready _ middle _ small (Or.inl rfl) state rfl
    simp only [small, ↓reduceIte]
    have signed : ∃ fuel final returned, run program fuel index
        (if 0 ≤ (count.sshiftRight 6).toInt then 14 else 10) args frame [] middle =
          .ok (final, returned) ∧ post final returned := by
      by_cases nonnegative : 0 ≤ (count.sshiftRight 6).toInt
      · simpa only [nonnegative, ↓reduceIte] using
          zero middle _ small (Or.inl nonnegative) state
      simp only [nonnegative, ↓reduceIte]
      have masked : ∃ fuel final returned, run program fuel index
          (if count &&& (63 : BitVec 32) != 0 then 17 else 14) args frame [] middle =
            .ok (final, returned) ∧ post final returned := by
        by_cases multiple : count &&& (63 : BitVec 32) = 0
        · simpa only [multiple, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] using
            zero middle _ small (Or.inr multiple) state
        simp only [bne_iff_ne, ne_eq, multiple, not_false_eq_true, ↓reduceIte]
        cil_contract_steps 1 []
        refine state.run_store (kind := .word32) post originalCall homes found
          fun after state => ?_
        exact ready 0 after _ (by decide) (Or.inr ⟨rfl, by omega, multiple⟩) state rfl
      cil_contract_steps 4 [argument]
      simpa only [bne_iff_ne, BitVec.ofNat_eq_ofNat] using masked
    cil_contract_steps (snapshots := state.locals) [] until signed
  cil_contract_steps (snapshots := state.locals) [] until unsigned

/-- Locals 1-6 once the bit counts and the four operand limbs are saved. -/
def preparedLocals (known : Nat → Option CIL.Value) (count : BitVec 32)
    (words : Fin 4 → BitVec 64) : Nat → Option CIL.Value :=
  rememberLocal (rememberLocal (rememberLocal (rememberLocal (rememberLocal (rememberLocal known
    1 (.i32 (count &&& 63))) 2 (.i32 (63 - (count &&& 63)))) 3 (.i64 (words 0)))
    4 (.i64 (words 1))) 5 (.i64 (words 2))) 6 (.i64 (words 3))

/-- Save the masked bit count, its complement and all four initial operand limbs. No caller
    byte changes, so the limbs read are the original ones even when the output overlaps. -/
theorem shift_prepared (original entered current : Memory) (input output : Reference)
    (frame : Frame) (args : List Value) (count : BitVec 32)
    (inputArgument : args[0]? = some (.reference (.address input)))
    (countArgument : args[1]? = some (.scalar (.i32 count)))
    (originalCall : CallingConditions program original [input] [output])
    (homes : CompleteWritableHomes entered original.nextIdentity (numericKinds shiftSpecs)
      frame.locals)
    (known : Nat → Option CIL.Value)
    (state : VectorFrame program original entered current [input] output frame known none)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorFrame program original entered after [input] output frame
        (preparedLocals known count (inputLimb original input)) none →
      ∃ fuel final returned, run program fuel index 39 args frame [] after =
        .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned, run program fuel index 19 args frame [] current =
      .ok (final, returned) ∧ post final returned := by
  have found := bodyFound
  obtain ⟨allocation, present, _, _⟩ :=
    formed_reference_live _ _ _ (originalCall.input_formed (by simp : input ∈ [input]))
  have old := (originalCall.1.1.1 _ _ present).1
  have words := state.call.input_words_kept (.refl _ _) input (by simp)
  simp only [inputLimb, fun offset => state.caller input.allocation old offset (Or.inl rfl)]
    at words
  have kept := fun after (below : MemoryBelow original.nextIdentity current after) =>
    ArgumentView.word_below below ⟨input, 32⟩ old
  obtain ⟨enteredFormed, formed, authority, valid, preserved⟩ :=
    state.walk_facts original.nextIdentity
  cil_contract_steps (snapshots := state.locals) [inputArgument, countArgument]
  rw [kept storedLocal_1 (by assumption), kept storedLocal_2 (by assumption),
    kept storedLocal_3 (by assumption), kept storedLocal_4 (by assumption), words.1,
    words.2.1, words.2.2.1, words.2.2.2] at localSnapshots_5
  exact continuation _ (state.after_stores originalCall localSnapshots_5)

end UInt256Proof.Shift.Safety
