import UInt256.Methods.Shift.ScalarBody
import CIL.Safety.StepComposition
import UInt256.Safety.NumericStore

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety
variable {profile : CIL.FeatureProfile} {direction : Direction} {storage : Nat}
  {program : CIL.Program} {index : Nat}
  (bodyFound : program[index]? = some (scalarBody profile direction storage))
include bodyFound

omit bodyFound in
private theorem step_arg_scalar {body : CIL.Method} {pc index : Nat} {args stack : List Value}
    {frame : Frame} {memory : Memory} {value : CIL.Value}
    (found : args[index]? = some (.scalar value)) (numeric : numericValue value = true) :
    step body (.arg index) pc args frame stack memory =
      .ok (.next (pc + 1) (.scalar value :: stack) frame memory) := by
  delta step
  dsimp only
  rw [found]
  simp only [checkedValue, numeric, ite_true, Bind.bind, Except.bind, Pure.pure, Except.pure]

macro "shift_pure_step" "[" facts:term,* "]" : tactic =>
  `(tactic| first
    | rfl
    $[| exact step_arg_scalar $facts:term rfl]*
    | (simp (config := { implicitDefEqProofs := false })
        [step, checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.binary,
          Bind.bind, Except.bind, Pure.pure, Except.pure, $[$facts:term],*]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))
/-- Compute the signed whole-limb count from the actual Int32 argument and
    initialize its private home before any count-dependent branch. -/
theorem shift_count_start (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value) (count : BitVec 32)
    (argument : args[1]? = some (.scalar (.i32 count)))
    (call : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary shiftSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[0]? = some (.bytes .word32 reference) →
      read after reference 4 1 = .ok (numberBytes (count.sshiftRight 6).toNat 4) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (count.sshiftRight 6).toNat 4) 1 = .ok after →
      ∃ fuel final returned,
        run program fuel index (4) args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index 0 args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨reference, after, slot, loaded, preserved, afterCall, afterAuthority, written, stored⟩ :=
    checked_numeric_store program (scalarBody profile direction storage) shiftSpecs boundary entered current inputs outputs
      frame call enteredWF homes authority 0 ⟨.word32, .i32 0, 0, rfl⟩ (by rfl)
      (.i32 (count.sshiftRight 6)) (count.sshiftRight 6).toNat rfl
  have done := continuation reference after slot loaded preserved afterCall afterAuthority written
  have found := bodyFound
  iterate 3
    apply run_next_exists post found (by rfl)
    shift_pure_step [argument]
  apply run_next_exists post found (by rfl) (stored _ _ _)
  exact done
/-- Both count comparisons read the initialized local and preserve memory.
    The unsigned comparison precedes the signed negative-count test. -/
theorem shift_count_guard (signed : Bool) (memory : Memory) (frame : Frame) (args : List Value)
    (word : BitVec 32) (home : Reference)
    (slot : frame.locals[0]? = some (.bytes .word32 home))
    (loaded : read memory home 4 1 = .ok (numberBytes word.toNat 4))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel index
        (if signed then (if 0 ≤ word.toInt then 14 else 10)
         else (if word < BitVec.ofNat 32 4 then 19 else 7))
        args frame [] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index (if signed then 7 else 4)
        args frame [] memory = .ok (final, returned) ∧ post final returned := by
  have load := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := (scalarBody profile direction storage)) (args := args) (pc := pc) (stack := stack)
    .word32 (.i32 word) word.toNat rfl slot loaded
  have found := bodyFound
  cases signed <;> simp only [Bool.false_eq_true, ite_false, ite_true] at continuation ⊢
  all_goals
    apply run_next_exists post found (by rfl) (load _ _)
    iterate 2
      apply run_next_exists post found (by rfl)
      shift_pure_step []
    exact continuation

/-- Negative counts use their masked low six bits to select zero output or
    the existing historical intra-limb shift convention. -/
theorem shift_negative_count_guard (memory : Memory) (frame : Frame) (args : List Value)
    (count : BitVec 32) (argument : args[1]? = some (.scalar (.i32 count)))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel index
        (if count &&& (63 : BitVec 32) != 0 then 17 else 14)
        args frame [] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index (10) args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  have found := bodyFound
  iterate 4
    apply run_next_exists post found (by rfl)
    shift_pure_step [argument]
  exact continuation

/-- Reset the whole-limb count only on the selected negative-count route. -/
theorem shift_negative_count_reset (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary shiftSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[0]? = some (.bytes .word32 reference) →
      read after reference 4 1 = .ok (numberBytes 0 4) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes 0 4) 1 = .ok after →
      ∃ fuel final returned,
        run program fuel index (19) args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index (17) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨reference, after, slot, loaded, preserved, afterCall, afterAuthority, written, stored⟩ :=
    checked_numeric_store program (scalarBody profile direction storage) shiftSpecs boundary entered current inputs outputs
      frame call enteredWF homes authority 0 ⟨.word32, .i32 0, 0, rfl⟩ (by rfl)
      (.i32 0) 0 rfl
  have done := continuation reference after slot loaded preserved afterCall afterAuthority written
  have found := bodyFound
  iterate 1
    apply run_next_exists post found (by rfl)
    shift_pure_step []
  apply run_next_exists post found (by rfl) (stored _ _ _)
  exact done

#print axioms shift_negative_count_reset
#print axioms shift_negative_count_guard
#print axioms shift_count_guard
#print axioms shift_count_start
end UInt256Proof.Shift.Safety
