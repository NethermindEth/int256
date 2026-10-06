import UInt256.Methods.Shift.SafetySetup
import CIL.Safety.CallComposition
import CIL.Safety.StepComposition
import UInt256.Safety.NumericStore

namespace UInt256Proof.Shift.Safety
open CIL.Safety

def countHelperIndex : Nat :=
  match shiftBody.code[1]? with
  | some (CIL.Op.call index 1) => index
  | _ => 0

def countHelperBody : CIL.Method := Extracted.program[countHelperIndex]?.getD
  { code := [], locals := [], returnsValue := false }

/-- Recheck the optional count helper's actual body. In the inline extraction,
    the fetched-call premise is impossible. No imported helper contract is assumed. -/
theorem shift_count_helper (memory : Memory) (count : BitVec 32)
    (helper : shiftBody.code[1]? = some (.call countHelperIndex 1)) :
    invoke Extracted.program 4 countHelperIndex [.scalar (.i32 count)] memory =
      .ok (memory, [.scalar (.i32 (count.sshiftRight 6))]) := by
  first
  | solve | cases helper
  | have found : Extracted.program[countHelperIndex]? = some countHelperBody := by rfl
    let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
    have setup : enterFrame countHelperBody [.scalar (.i32 count)] memory = .ok (frame, memory) := by
      have kinds : countHelperBody.localKinds = [] := by rfl
      have locals : countHelperBody.locals = [] := by rfl
      have arguments : countHelperBody.aggregateArgs = [] := by rfl
      simp [enterFrame, kinds, locals, arguments, makeLocals, makeArgumentHomes, frame,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    simp [invoke, found, checkedValue, numericValue, checkedAt, setup,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    iterate 3
      apply Eq.trans
      · apply run_next found (by rfl)
        simp [step, checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.binary,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    have returns : countHelperBody.returnsValue = true := by rfl
    have fetched : countHelperBody.code[3]? = some .ret := by rfl
    simp [run, found, fetched, returns, step, frame, leaveFrame,
      checkedValue, numericValue, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms shift_count_helper
end UInt256Proof.Shift.Safety

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety

/-- Compute the signed whole-limb count from the actual Int32 argument and
    initialize its private home before any count-dependent branch. -/
theorem shift_count_start (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value) (count : BitVec 32)
    (argument : args[1]? = some (.scalar (.i32 count)))
    (call : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary shiftSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[0]? = some (.bytes .word32 reference) →
      read after reference 4 1 = .ok (numberBytes (count.sshiftRight 6).toNat 4) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (count.sshiftRight 6).toNat 4) 1 = .ok after →
      ∃ fuel final returned,
        run Extracted.program fuel shiftIndex (shiftPc 4) args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel shiftIndex 0 args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨reference, after, slot, loaded, preserved, afterCall, afterAuthority, written, stored⟩ :=
    checked_numeric_store Extracted.program shiftBody shiftSpecs boundary entered current inputs outputs
      frame call enteredWF homes authority 0 ⟨.word32, .i32 0, 0, rfl⟩ (by rfl)
      (.i32 (count.sshiftRight 6)) (count.sshiftRight 6).toNat rfl
  have done := continuation reference after slot loaded preserved afterCall afterAuthority written
  have found : Extracted.program[shiftIndex]? = some shiftBody := by rfl
  first
  | iterate 3
      apply run_next_exists post found (by rfl)
      simp (config := { implicitDefEqProofs := false })
        [step, argument, checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.binary,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    apply run_next_exists post found (by rfl) (stored _ _ _)
    exact done
  | have helper : shiftBody.code[1]? = some (.call countHelperIndex 1) := by rfl
    have invocation := shift_count_helper current count helper
    have tail : ∃ fuel final returned,
        run Extracted.program fuel shiftIndex 2 args frame
          [.scalar (.i32 (count.sshiftRight 6))] current = .ok (final, returned) ∧
        post final returned := by
      apply run_next_exists post found (by rfl) (stored _ _ _)
      exact done
    obtain ⟨tailFuel, final, returned, resumed, satisfied⟩ := tail
    have stepped : step shiftBody (.call countHelperIndex 1) 1 args frame
        [.scalar (.i32 count)] current =
        .ok (.call countHelperIndex [.scalar (.i32 count)] [] current) := by
      simp [step, checkedValue, numericValue, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    obtain ⟨fuel, executed⟩ := run_call_exists found helper stepped
      ⟨4, invocation⟩ ⟨tailFuel, resumed⟩
    apply run_next_exists post found (by rfl)
    · simp [step, argument, checkedValue, numericValue,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨fuel, final, returned, executed, satisfied⟩

/-- Both count comparisons read the initialized local and preserve memory.
    The unsigned comparison precedes the signed negative-count test. -/
theorem shift_count_guard (signed : Bool) (memory : Memory) (frame : Frame) (args : List Value)
    (word : BitVec 32) (home : Reference)
    (slot : frame.locals[0]? = some (.bytes .word32 home))
    (loaded : read memory home 4 1 = .ok (numberBytes word.toNat 4))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run Extracted.program fuel shiftIndex
        (if signed then (if 0 ≤ word.toInt then shiftPc 14 else shiftPc 10)
         else (if word < BitVec.ofNat 32 4 then shiftPc 19 else shiftPc 7))
        args frame [] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel shiftIndex (if signed then shiftPc 7 else shiftPc 4)
        args frame [] memory = .ok (final, returned) ∧ post final returned := by
  have load := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := shiftBody) (args := args) (pc := pc) (stack := stack)
    .word32 (.i32 word) word.toNat rfl slot loaded
  have found : Extracted.program[shiftIndex]? = some shiftBody := by rfl
  cases signed <;> simp only [Bool.false_eq_true, ite_false, ite_true] at continuation ⊢
  all_goals
    apply run_next_exists post found (by rfl) (load _ _)
    iterate 2
      apply run_next_exists post found (by rfl)
      simp (config := { implicitDefEqProofs := false })
        [step, checkedValue, numericValue, pureArity, scalars, CIL.step,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    exact continuation

/-- Negative counts use their masked low six bits to select zero output or
    the existing historical intra-limb shift convention. -/
theorem shift_negative_count_guard (memory : Memory) (frame : Frame) (args : List Value)
    (count : BitVec 32) (argument : args[1]? = some (.scalar (.i32 count)))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run Extracted.program fuel shiftIndex
        (if count &&& (63 : BitVec 32) != 0 then shiftPc 17 else shiftPc 14)
        args frame [] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel shiftIndex (shiftPc 10) args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[shiftIndex]? = some shiftBody := by rfl
  iterate 4
    apply run_next_exists post found (by rfl)
    simp (config := { implicitDefEqProofs := false })
      [step, argument, checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.binary,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  exact continuation

/-- Reset the whole-limb count only on the selected negative-count route. -/
theorem shift_negative_count_reset (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary shiftSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[0]? = some (.bytes .word32 reference) →
      read after reference 4 1 = .ok (numberBytes 0 4) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes 0 4) 1 = .ok after →
      ∃ fuel final returned,
        run Extracted.program fuel shiftIndex (shiftPc 19) args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel shiftIndex (shiftPc 17) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨reference, after, slot, loaded, preserved, afterCall, afterAuthority, written, stored⟩ :=
    checked_numeric_store Extracted.program shiftBody shiftSpecs boundary entered current inputs outputs
      frame call enteredWF homes authority 0 ⟨.word32, .i32 0, 0, rfl⟩ (by rfl)
      (.i32 0) 0 rfl
  have done := continuation reference after slot loaded preserved afterCall afterAuthority written
  have found : Extracted.program[shiftIndex]? = some shiftBody := by rfl
  iterate 1
    apply run_next_exists post found (by rfl)
    simp (config := { implicitDefEqProofs := false })
      [step, checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.binary,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  apply run_next_exists post found (by rfl) (stored _ _ _)
  exact done

#print axioms shift_negative_count_reset
#print axioms shift_negative_count_guard
#print axioms shift_count_guard
#print axioms shift_count_start
end UInt256Proof.Shift.Safety
