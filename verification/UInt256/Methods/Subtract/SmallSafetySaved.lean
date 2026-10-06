import UInt256.Methods.Subtract.SmallSafetyMemory
import CIL.Safety.WordFootprint
import CIL.Safety.StepComposition

namespace UInt256Proof.Subtract.Safety

open CIL.Safety UInt256Model.Safety

theorem small_input_spec (i : Fin 4) : smallWordSpecs[i.val]? = some (some 0) := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;>
    rfl

def smallSavedWord (original : Memory) (input : Reference) (word : BitVec 64) (i : Fin 4) : BitVec 64 :=
  if h : i.val < 3 then inputLimb original input ⟨i.val + 1, by omega⟩ else inputLimb original input 0 - word

structure SmallSaved (original entered current : CIL.Safety.Memory)
    (input output : Reference) (word : BitVec 64) (slots : List LocalSlot) (done : Nat) : Prop where
  call : CallingConditions Extracted.program current [input] [output]
  preserved : MemoryBelow original.nextIdentity original current
  authority : AccessBelow entered.nextIdentity entered current
  completed : ∀ i : Fin 4, i.val < done → ∃ reference,
    slots[i.val]? = some (.bytes .word64 reference) ∧ reference.allocation < entered.nextIdentity ∧
      read current reference 8 1 = .ok (numberBytes (smallSavedWord original input word i).toNat 8)

theorem SmallSaved.save {original entered current : CIL.Safety.Memory}
    {input output : Reference} {word : BitVec 64} {frame : Frame}
    (index : Fin 4)
    (state : SmallSaved original entered current input output word frame.locals index.val)
    (call : CallingConditions Extracted.program original [input] [output])
    (enteredWF : entered.WellFormed)
    (homes : WordHomes entered original.nextIdentity smallWordSpecs frame.locals) :
    ∃ after, SmallSaved original entered after input output word frame.locals (index.val + 1) ∧
      ∀ pc rest, step Extracted.subtractScalarUInt64Body (.setLocal index.val) pc
        (smallArguments input output word) frame
        (.scalar (.i64 (smallSavedWord original input word index)) :: rest) current =
          .ok (.next (pc + 1) rest frame after) := by
  obtain ⟨reference, after, fullSlot, loaded, preserved, afterCall, authority, written, stepped⟩ :=
    small_private_store original entered current input output word (smallSavedWord original input word index)
      frame call state.call enteredWF homes state.preserved state.authority
      index.val 0 (small_input_spec index)
  have slot := fullSlot
  obtain ⟨home, homeSlot, _, _, writable⟩ := homes.word_at index.val 0 (small_input_spec index)
  have same : home = reference := by rw [slot] at homeSlot; simpa using homeSlot.symm
  subst home
  obtain ⟨allocation, ready⟩ := access_requirements writable
  have old := (enteredWF.1 _ _ ready.present).1
  refine ⟨after, ⟨afterCall, preserved, authority, ?_⟩, stepped⟩
  intro i saved
  by_cases equal : i = index
  · subst i
    exact ⟨reference, slot, old, loaded⟩
  · have earlier : i.val < index.val := by
      have different : i.val ≠ index.val := fun h => equal (Fin.ext h)
      omega
    obtain ⟨previous, previousSlot, previousOld, previousRead⟩ := state.completed i earlier
    have different := Nat.ne_of_lt (homes.ordered i.val index.val previous reference earlier previousSlot slot)
    refine ⟨previous, previousSlot, previousOld,
      (write_preserves_access_below written entered.nextIdentity).read_eq previousRead previousOld ?_⟩
    intro offset _
    exact write_word_outside written _ _ (Or.inl different)

#print axioms small_input_spec
#print axioms SmallSaved.save

def smallFirstDecision : Nat := Extracted.subtractScalarUInt64Body.code.findIdx fun op =>
  match op with | .bltu _ => true | _ => false

/-- Save upper input limbs and the low difference along the actual extracted
    prefix, retaining the initial low word for the first borrow decision. -/
theorem small_input_prefix_checked (original entered : Memory)
    (input output : Reference) (word : BitVec 64) (frame : Frame)
    (call : CallingConditions Extracted.program original [input] [output])
    (setup : enterFrame Extracted.subtractScalarUInt64Body (smallArguments input output word) original =
      .ok (frame, entered))
    (homes : WordHomes entered original.nextIdentity smallWordSpecs frame.locals)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, SmallSaved original entered after input output word frame.locals 4 →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.subtractScalarUInt64Index smallFirstDecision
          (smallArguments input output word) frame
          [.scalar (.i64 word), .scalar (.i64 (inputLimb original input 0))] after = .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.subtractScalarUInt64Index 0
        (smallArguments input output word) frame [] entered = .ok (result, returned) ∧ post result returned := by
  have enteredCall := call.after_frame_setup setup
  have initial : SmallSaved original entered entered input output word frame.locals 0 :=
    ⟨enteredCall, enterFrame_preserves_caller_memory _ _ _ _ _ setup,
      (MemoryBelow.refl entered.nextIdentity entered).accessBelow, by intro i impossible; omega⟩
  obtain ⟨first, saved1, step0⟩ := initial.save 0 call enteredCall.1.1 homes
  obtain ⟨second, saved2, step1⟩ := saved1.save 1 call enteredCall.1.1 homes
  obtain ⟨third, saved3, step2⟩ := saved2.save 2 call enteredCall.1.1 homes
  obtain ⟨fourth, saved4, step3⟩ := saved3.save 3 call enteredCall.1.1 homes
  have done := continuation fourth saved4
  conv at done in smallFirstDecision => cbv
  have f0 := enteredCall.input_formed (reference := input) (by simp)
  have f1 := saved1.call.input_formed (reference := input) (by simp)
  have f2 := saved2.call.input_formed (reference := input) (by simp)
  have r0 := call.input_field_after_setup setup (by simp : input ∈ [input]) 0
  have r1 := call.input_field_after_setup setup (by simp : input ∈ [input]) 1
  have r2 (rest : List Value) : instruction (.field 2) (.reference (.address input) :: rest) first =
      .ok (first, .scalar (.i64 (inputLimb original input 2)) :: rest) := by
    rw [saved1.call.input_field_instruction (by simp) 2 rest]
    simp only [inputLimb, call.input_bytes_of_memory_below saved1.preserved (reference := input) (by simp)]
  have r3 (rest : List Value) : instruction (.field 3) (.reference (.address input) :: rest) second =
      .ok (second, .scalar (.i64 (inputLimb original input 3)) :: rest) := by
    rw [saved2.call.input_field_instruction (by simp) 3 rest]
    simp only [inputLimb, call.input_bytes_of_memory_below saved2.preserved (reference := input) (by simp)]
  simp only [smallSavedWord, Fin.val_zero, Fin.val_one, Fin.val_two, CIL.fin_val_three,
    Nat.reduceLT, ↓reduceDIte, Nat.reduceAdd] at step0 step1 step2 step3
  repeat' first
    | exact done
    | (simp (config := { failIfUnchanged := false })
       apply run_next_exists post
       · simp only [cil_code]; rfl
       · simp only [cil_code]; rfl
       · first
         | exact step0 _ _
         | exact step1 _ _
         | exact step2 _ _
         | exact step3 _ _
         | (simp (config := { implicitDefEqProofs := false })
             [cil_code, step, smallArguments, checkedValue, numericValue, formValue, f0, f1, f2,
               r0, r1, r2, r3, pureArity, scalars, CIL.step, CIL.binary, checkedAt,
               Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms small_input_prefix_checked
end UInt256Proof.Subtract.Safety
