import UInt256.Methods.Add.SmallMemory
import CIL.Safety.WordFootprint

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

theorem small_input_spec (i : Fin 4) : smallWordSpecs[i.val]? = some (some 0) := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;>
    simp [smallWordSpecs, smallWordCount, cil_code]

structure SmallSaved (original entered current : CIL.Safety.Memory)
    (input output : Reference) (slots : List LocalSlot) (done : Nat) : Prop where
  call : CallingConditions Extracted.program current [input] [output]
  preserved : MemoryBelow original.nextIdentity original current
  authority : AccessBelow entered.nextIdentity entered current
  completed : ∀ i : Fin 4, i.val < done → ∃ reference,
    slots[i.val]? = some (.bytes .word64 reference) ∧ reference.allocation < entered.nextIdentity ∧
      read current reference 8 1 = .ok (numberBytes (inputLimb original input i).toNat 8)

theorem SmallSaved.save {original entered current : CIL.Safety.Memory}
    {input output : Reference} {slots tailSlots : List LocalSlot} {frame : Frame}
    (index : Fin 4)
    (state : SmallSaved original entered current input output slots index.val)
    (word : BitVec 64)
    (call : CallingConditions Extracted.program original [input] [output])
    (enteredWF : entered.WellFormed)
    (layout : frame.locals = slots ++ tailSlots)
    (homes : WordHomes entered original.nextIdentity smallWordSpecs slots) :
    ∃ after, SmallSaved original entered after input output slots (index.val + 1) ∧
      ∀ pc rest, step Extracted.addScalarUInt64Body (.setLocal index.val) pc
        (smallArguments input output word) frame
        (.scalar (.i64 (inputLimb original input index)) :: rest) current =
          .ok (.next (pc + 1) rest frame after) := by
  obtain ⟨reference, after, fullSlot, loaded, preserved, afterCall, authority, written, stepped⟩ :=
    small_private_store original entered current input output word (inputLimb original input index)
      frame slots tailSlots call state.call enteredWF layout homes state.preserved state.authority
      index.val 0 (small_input_spec index)
  have inside : index.val < slots.length := by
    rw [homes.length]
    exact (List.getElem?_eq_some_iff.mp (small_input_spec index)).1
  have slot : slots[index.val]? = some (.bytes .word64 reference) := by
    rw [layout, List.getElem?_append_left inside] at fullSlot
    exact fullSlot
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

theorem small_input_prefix_checked (original entered : CIL.Safety.Memory)
    (input output : Reference) (word : BitVec 64) (frame : Frame) (slots tailSlots)
    (call : CallingConditions Extracted.program original [input] [output])
    (setup : enterFrame Extracted.addScalarUInt64Body (smallArguments input output word) original =
      .ok (frame, entered))
    (layout : frame.locals = slots ++ tailSlots)
    (homes : WordHomes entered original.nextIdentity smallWordSpecs slots)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ after, SmallSaved original entered after input output slots 4 →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarUInt64Index smallScalarStart
          (smallArguments input output word) frame [] after = .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index 0
        (smallArguments input output word) frame [] entered = .ok (result, returned) ∧
      post result returned := by
  have enteredCall := call.after_frame_setup setup
  have initial : SmallSaved original entered entered input output slots 0 :=
    ⟨enteredCall, enterFrame_preserves_caller_memory _ _ _ _ _ setup,
      (MemoryBelow.refl entered.nextIdentity entered).accessBelow, by intro i impossible; omega⟩
  obtain ⟨first, saved1, step0⟩ := initial.save 0 word call enteredCall.1.1 layout homes
  obtain ⟨second, saved2, step1⟩ := saved1.save 1 word call enteredCall.1.1 layout homes
  obtain ⟨third, saved3, step2⟩ := saved2.save 2 word call enteredCall.1.1 layout homes
  obtain ⟨fourth, saved4, step3⟩ := saved3.save 3 word call enteredCall.1.1 layout homes
  let states : Nat → CIL.Safety.Memory := fun n => match n with
    | 0 => entered | 1 => first | 2 => second | 3 => third | _ => fourth
  have saved : ∀ i : Fin 4, SmallSaved original entered (states i.val) input output slots i.val := by
    intro ⟨i, bound⟩
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · exact initial
    · exact saved1
    · exact saved2
    · exact saved3
  apply small_input_prefix input output word (inputLimb original input) frame states
    (fun i => (saved i).call.input_formed (by simp)) ?_ ?_ post
    (continuation fourth saved4)
  · intro i rest
    rw [(saved i).call.input_field_instruction (by simp) i rest]
    simp only [inputLimb,
      call.input_bytes_of_memory_below (saved i).preserved (reference := input) (by simp)]
  · intro ⟨i, bound⟩ pc rest
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · exact step0 pc rest
    · exact step1 pc rest
    · exact step2 pc rest
    · exact step3 pc rest

#print axioms small_input_prefix_checked

theorem small_saved_invocation (memory : CIL.Safety.Memory)
    (input output : Reference) (word : BitVec 64)
    (call : CallingConditions Extracted.program memory [input] [output])
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ frame entered slots tailSlots after,
      enterFrame Extracted.addScalarUInt64Body (smallArguments input output word) memory =
        .ok (frame, entered) →
      frame.locals = slots ++ tailSlots →
      WordHomes entered memory.nextIdentity smallWordSpecs slots →
      SmallSaved memory entered after input output slots 4 →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarUInt64Index smallScalarStart
          (smallArguments input output word) frame [] after = .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      invoke Extracted.program fuel Extracted.addScalarUInt64Index (smallArguments input output word)
        memory = .ok (result, returned) ∧ post result returned := by
  obtain ⟨frame, entered, slots, tailSlots, setup, layout, homes, _, _⟩ :=
    small_frame_setup memory (smallArguments input output word) call.1.1
  obtain ⟨fuel, result, returned, finished, satisfied⟩ := small_input_prefix_checked
    memory entered input output word frame slots tailSlots call setup layout homes post
      (fun after saved => continuation frame entered slots tailSlots after setup layout homes saved)
  have checked : (smallArguments input output word).mapM (checkedValue memory) =
      .ok (smallArguments input output word) := by
    have fi := call.input_formed (reference := input) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [smallArguments, checkedValue, numericValue, formValue, fi, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨fuel, result, returned, ?_, satisfied⟩
  simp only [cil_code] at setup
  simpa only [invoke, cil_code, checked, setup, Except.mapError, Bind.bind, Except.bind] using finished

#print axioms small_saved_invocation

end UInt256Proof.Safety
