import UInt256.Methods.Add.Vector128ARMParentCall
import UInt256.Safety.LimbAccess
import CIL.Safety.WordLocals

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

def armScalarSavedFrame (frame : Frame) (source : Reference) : Frame :=
  { frame with locals := frame.locals.set 7 (.root (some (.address source))) }

/-- Check the initial ARM feature guard before touching caller references. -/
theorem arm_scalar_dispatch (enabled : Extracted.profile.advSimd = true)
    (memory : Memory) (frame : Frame) (args : List Value) (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex 2 args frame [] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex 0 args frame [] memory = .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    have found : Extracted.program[Extracted.addScalarIndex]? = some Extracted.addScalarBody := by rfl
    repeat' first
      | exact continuation
      | (apply run_next_exists post found (by rfl)
         simp (config := { implicitDefEqProofs := false })
           [step, cil_code, pureArity, scalars, CIL.step, CIL.FeatureProfile.evaluate,
             checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
         first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

/-- Both selected source-reference assignments update a tracked root, without
    changing caller memory or any numeric local home. -/
theorem arm_scalar_save_source (enabled : Extracted.profile.advSimd = true) (swapped : Bool) (memory : Memory) (frame : Frame)
    (args : List Value) (source : Reference) (initial : Option ManagedReference)
    (slot : frame.locals[7]? = some (.root initial))
    (argument : args[if swapped then 1 else 0]? = some (.reference (.address source)))
    (formed : form memory source = .ok source) (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex (if swapped then 33 else 4)
        args (armScalarSavedFrame frame source) [] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex (if swapped then 31 else 2)
        args frame [] memory = .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    have found : Extracted.program[Extracted.addScalarIndex]? = some Extracted.addScalarBody := by rfl
    cases swapped <;> simp only [Bool.false_eq_true, ite_false, ite_true] at argument continuation ⊢
    all_goals
      repeat' first
        | exact continuation
        | (apply run_next_exists post found (by rfl)
           simp (config := { implicitDefEqProofs := false })
             [step, argument, slot, storeLocal, armScalarSavedFrame, checkedValue, formValue, formed,
               checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
           first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

/-- The selected low-word load is checked against the caller's input view. -/
theorem arm_scalar_low_load (enabled : Extracted.profile.advSimd = true) (swapped : Bool) (memory : Memory) (frame : Frame)
    (args : List Value) (inputs outputs : List Reference) (input : Reference)
    (call : CallingConditions Extracted.program memory inputs outputs) (member : input ∈ inputs)
    (argument : args[if swapped then 0 else 1]? = some (.reference (.address input)))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex (if swapped then 35 else 6)
        args frame [.scalar (.i64 (inputLimb memory input 0))] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex (if swapped then 33 else 4)
        args frame [] memory = .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    have found : Extracted.program[Extracted.addScalarIndex]? = some Extracted.addScalarBody := by rfl
    have formed := call.input_formed member
    have loaded := call.input_field_instruction member 0
    cases swapped <;> simp only [Bool.false_eq_true, ite_false, ite_true] at argument continuation ⊢
    all_goals
      repeat' first
        | exact continuation
        | (apply run_next_exists post found (by rfl)
           simp (config := { implicitDefEqProofs := false })
             [step, argument, checkedValue, formValue, formed, loaded,
               checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
           first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)


/-- Saving the selected root preserves the distinct numeric local used for the
    small operand. The checked store retains that frame and initializes its bytes. -/
theorem arm_scalar_word_store (frame : Frame) (source home : Reference)
    (memory : Memory) (word : BitVec 64) (pc : Nat) (args rest : List Value)
    (slot : frame.locals[8]? = some (.bytes .word64 home))
    (ready : access memory home 8 1 true = .ok ()) :
    ∃ result,
      step Extracted.addScalarBody (.setLocal 8) pc args (armScalarSavedFrame frame source)
        (.scalar (.i64 word) :: rest) memory =
          .ok (.next (pc + 1) rest (armScalarSavedFrame frame source) result) ∧
      write memory home (numberBytes word.toNat 8) 1 = .ok result ∧
      read result home 8 1 = .ok (numberBytes word.toNat 8) := by
  apply step_store_word64_same_frame word ?_ ready
  simpa only [armScalarSavedFrame, List.getElem?_set_ne (by decide : 7 ≠ 8)] using slot

/-- Both upper-limb tests read the original caller view through checked field
    instructions. The following branch still has to prove both continuations. -/
theorem arm_scalar_upper_loads (enabled : Extracted.profile.advSimd = true)
    (leftTest : Bool) (memory : Memory) (frame : Frame) (args : List Value)
    (inputs outputs : List Reference) (input : Reference)
    (call : CallingConditions Extracted.program memory inputs outputs) (member : input ∈ inputs)
    (argument : args[if leftTest then 0 else 1]? = some (.reference (.address input)))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex (if leftTest then 24 else 15)
        args frame [.scalar (.i64 (inputLimb memory input 1 ||| inputLimb memory input 2 |||
          inputLimb memory input 3))] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex (if leftTest then 16 else 7)
        args frame [] memory = .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    have found : Extracted.program[Extracted.addScalarIndex]? = some Extracted.addScalarBody := by rfl
    have formed := call.input_formed member
    have loaded := call.input_field_instruction member
    cases leftTest <;> simp only [Bool.false_eq_true, ite_false, ite_true] at argument continuation ⊢
    all_goals
      repeat' first
        | exact continuation
        | (apply run_next_exists post found (by rfl)
           simp (config := { implicitDefEqProofs := false })
             [step, argument, checkedValue, numericValue, formValue, formed, loaded,
               pureArity, scalars, CIL.step, CIL.binary,
               checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
           first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)


/-- Follow the actual right/left small-operand branch, without assuming its
    outcome or discarding either continuation. -/
theorem arm_scalar_upper_branch (enabled : Extracted.profile.advSimd = true)
    (leftTest : Bool) (memory : Memory) (frame : Frame) (args : List Value)
    (condition : BitVec 64) (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex
        (if condition = BitVec.ofNat 64 0 then (if leftTest then 31 else 36)
         else (if leftTest then 25 else 16))
        args frame [] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel Extracted.addScalarIndex (if leftTest then 24 else 15)
        args frame [.scalar (.i64 condition)] memory = .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    have found : Extracted.program[Extracted.addScalarIndex]? = some Extracted.addScalarBody := by rfl
    cases leftTest <;> by_cases zero : condition = BitVec.ofNat 64 0
    all_goals
      simp only [Bool.false_eq_true, ite_false, ite_true, zero] at continuation ⊢
      apply run_next_exists post found (by rfl) _ continuation
      simp [step, checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.truth,
        show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, zero,
        Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms arm_scalar_upper_branch

#print axioms arm_scalar_word_store
#print axioms arm_scalar_upper_loads

#print axioms arm_scalar_dispatch
#print axioms arm_scalar_save_source
#print axioms arm_scalar_low_load
end UInt256Proof.Add.Safety
