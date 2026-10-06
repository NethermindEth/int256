import UInt256.Methods.Subtract.ScalarBorrowMemory
import UInt256.Methods.Subtract.ScalarSafetyPrefix

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety

/-- Follow the extracted large-right branch and scalar feature guards through
    borrow initialization to the first discovered borrow call. -/
theorem scalar_borrow_prefix (left right output : Reference) (frame : Frame) (before after : Memory)
    (upper a b : BitVec 64) (large : upper ≠ BitVec.ofNat 64 0)
    (rightHome borrowHome resultHome : Reference)
    (leftFormed : form after left = .ok left)
    (leftRead : ∀ rest, instruction (.field 0) (.reference (.address left) :: rest) after =
      .ok (after, .scalar (.i64 a) :: rest))
    (rightSlot : frame.locals[0]? = some (.bytes .word64 rightHome))
    (borrowSlot : frame.locals[1]? = some (.bytes .word64 borrowHome))
    (resultSlot : frame.locals[2]? = some (.bytes .word64 resultHome))
    (rightRead : read after rightHome 8 1 = .ok (numberBytes b.toNat 8))
    (borrowFormed : form after borrowHome = .ok borrowHome)
    (resultFormed : form after resultHome = .ok resultHome)
    (stored : ∀ pc rest, step scalarBody (.setLocal 1) pc (binaryArguments left right output) frame
      (.scalar (.i64 0) :: rest) before = .ok (.next (pc + 1) rest frame after))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel scalarIndex (scalarBorrowCall 0) (binaryArguments left right output) frame
        [.reference (.address resultHome), .reference (.address borrowHome), .scalar (.i64 b), .scalar (.i64 a)]
        after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel scalarIndex scalarFirstDecision (binaryArguments left right output) frame
        [.scalar (.i64 upper)] before = .ok (result, returned) ∧ post result returned := by
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  have adv : scalarBody.profile.advSimd = false := by rfl
  have sse : scalarBody.profile.sse42 = false := by rfl
  have rightLoaded := load_local_word64_of_read rightRead
  conv in scalarFirstDecision => cbv
  repeat' first
    | exact continuation
    | (simp (config := { failIfUnchanged := false }) [BitVec.ofNat_eq_ofNat, large]
       apply run_next_exists post found (by rfl)
       first
       | exact stored _ _
       | (simp (config := { implicitDefEqProofs := false })
           [step, binaryArguments, checkedValue, numericValue, formValue, leftFormed,
             borrowFormed, resultFormed, rightSlot, borrowSlot, resultSlot, rightLoaded,
             leftRead, localAddress, pureArity, scalars, CIL.step, CIL.FeatureProfile.evaluate, adv, sse,
              checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms scalar_borrow_prefix
/-- Execute the scalar body through its complete large-operand borrow chain.
    The continuation receives the four checked result words before output stores. -/
theorem scalar_general_borrows (original entered : Memory) (left right output : Reference) (frame : Frame)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame scalarBody (binaryArguments left right output) original = .ok (frame, entered))
    (homes : WordHomes entered original.nextIdentity scalarLocalSpecs frame.locals)
    (large : inputLimb original right 1 ||| inputLimb original right 2 |||
      inputLimb original right 3 ≠ BitVec.ofNat 64 0)
    (post : Memory → List Value → Prop)
    (continuation : ∀ borrowHome results after,
      ScalarBorrowState original after frame left right output borrowHome results 4 →
      ∃ fuel result returned,
        run Extracted.program fuel scalarIndex (scalarBorrowCall 3 + 1)
          (binaryArguments left right output) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel scalarIndex 0 (binaryArguments left right output) frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  apply scalar_right_prefix_checked original entered left right output frame call setup homes post
  intro rightHome before rightSlot rightRead preserved beforeCall authority
  have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  obtain ⟨borrowHome, results, prepared, state, savedRight, stored⟩ := scalar_borrow_store
    original entered before left right output rightHome frame call beforeCall enteredWF homes
    preserved authority rightSlot rightRead
  have leftRead (rest : List Value) :
      instruction (.field 0) (.reference (.address left) :: rest) prepared =
        .ok (prepared, .scalar (.i64 (inputLimb original left 0)) :: rest) := by
    rw [state.call.input_field_instruction (by simp) 0 rest]
    simp only [inputLimb, state.inputBytes left (by simp)]
  apply scalar_borrow_prefix left right output frame before prepared _ (inputLimb original left 0)
    (inputLimb original right 0) large rightHome borrowHome (results 0)
    (state.call.input_formed (by simp)) leftRead rightSlot state.borrowSlot (state.resultSlots 0)
    savedRight (access_reference_valid _ _ _ _ _ state.borrowWrite)
    (access_reference_valid _ _ _ _ _ (state.resultWrites 0)) stored post
  apply scalar_indexed_borrow 0 (binaryArguments left right output) frame prepared
    (inputLimb original left 0) (inputLimb original right 0)
    (scalarBorrowValue original left right 0) borrowHome (results 0)
    state.call.1.1 state.borrowBound state.borrowRead state.borrowWrite (state.resultWrites 0)
    (Or.inl (Ne.symm (state.borrowSeparate 0))) post
  intro after math
  exact (state.advance 0 math).run_remaining post (fun final completed =>
    continuation borrowHome results final completed)

#print axioms scalar_general_borrows
end UInt256Proof.Subtract.Safety
