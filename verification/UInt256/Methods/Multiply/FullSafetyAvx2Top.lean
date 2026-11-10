import UInt256.Methods.Multiply.FullSafety
import UInt256.Methods.Multiply.VectorInputs
import UInt256.Methods.Multiply.VectorSteps
import CIL.Safety.LocalSnapshots

/-! The AVX2 product segment carries initialized word and vector locals in shared snapshots. -/

namespace UInt256Proof.Multiply.Full
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.BothTwo UInt256Proof.Multiply.VectorInputs

def inputPack (memory : Memory) (input : Reference) := CIL.Vector.pack256
  (inputLimb memory input 0) (inputLimb memory input 1) (inputLimb memory input 2) (inputLimb memory input 3)

def reverseInputPack (memory : Memory) (input : Reference) := CIL.Vector.pack256
  (inputLimb memory input 3) (inputLimb memory input 2) (inputLimb memory input 1) (inputLimb memory input 0)

/-- Initialized input words and the two vector operands; every other home remains unknown. -/
def avxOperandLocals (original : Memory) (left right : Reference) : Nat → Option CIL.Value :=
  rememberLocal (rememberLocal (wordLocals (fullInputs original left right))
    23 (.v256 (inputPack original left))) 24 (.v256 (reverseInputPack original right))

/-- The AVX2 operands and the previously initialized input words load their exact values. -/
def AvxOperands (original current : Memory) (frame : Frame) (left right : Reference) : Prop :=
  LocalSnapshots current frame.locals (avxOperandLocals original left right)

theorem full_avx2_inputs (profile : CIL.FeatureProfile) (program : CIL.Program)
    (methodIndex wordIndex countIndex storageIndex : Nat)
    (found : program[methodIndex]? = some (fullBody profile wordIndex countIndex storageIndex))
    (noAvx512 : profile.avx512DQVL = false) (avx2 : profile.avx2 = true)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : CompleteWritableHomes entered original.nextIdentity (fullBody profile wordIndex countIndex storageIndex).localKinds frame.locals)
    (state : PrivateWords program original entered current [left, right] [output] frame
      (fullInputs original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after [left, right] [output] frame
        (fullInputs original left right) →
      AvxOperands original after frame left right →
      ∃ fuel final returned,
        run program fuel methodIndex 56 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel methodIndex 18 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have profileEq : (fullBody profile wordIndex countIndex storageIndex).profile = profile := rfl
  have formedLeft := state.call.input_formed (by simp : left ∈ [left, right])
  have loadedLeft := input_vector_snapshot state originalCall left (by simp)
  iterate 14
    apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
    simp (config := { implicitDefEqProofs := false })
      [step, cil_guard, observerCount, pureArity, productArgs, checkedValue, numericValue, formValue, formedLeft,
        staticInstruction, memoryInstruction, otherMemoryInstruction, referenceAddInstruction, displaceReference, loadedLeft, checkedAt, profileEq, noAvx512, avx2,
        CIL.FeatureProfile.evaluate, scalars, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨middle, leftHome, leftSlot, storedLeft, middleState, _, writtenLeft⟩ :=
    state.store_vector enteredWF homes 23 (by rfl) (inputPack original left)
      48 (productArgs left right output) [] (body := (fullBody profile wordIndex countIndex storageIndex))
  have snapshots := state.snapshots.toLocalSnapshots.after_write homes.writable
    23 .vector256 leftHome (.v256 (inputPack original left)) _ rfl leftSlot writtenLeft
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl) storedLeft
  have formedRight := middleState.call.input_formed (by simp : right ∈ [left, right])
  have loadedRight := input_vector_snapshot middleState originalCall right (by simp)
  iterate 6
    apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
    simp (config := { implicitDefEqProofs := false })
      [step, cil_guard, observerCount, pureArity, productArgs, checkedValue, numericValue, formValue, formedRight,
        staticInstruction, memoryInstruction, otherMemoryInstruction, referenceAddInstruction, displaceReference, loadedRight, checkedAt, profileEq, avx2,
        CIL.Intrinsic.available, scalars, checkedIntrinsic, eval_reverse256, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨after, rightHome, rightSlot, storedRight, afterState, _, written⟩ :=
    middleState.store_vector enteredWF homes 24 (by rfl) (reverseInputPack original right)
      55 (productArgs left right output) [] (body := (fullBody profile wordIndex countIndex storageIndex))
  have operands := snapshots.after_write homes.writable
    24 .vector256 rightHome (.v256 (reverseInputPack original right)) _ rfl rightSlot written
  exact run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl) storedRight
    (continuation after afterState operands)

#print axioms full_avx2_inputs
end UInt256Proof.Multiply.Full

namespace UInt256Proof.Multiply.Full
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.BothTwo UInt256Proof.Multiply.VectorInputs

def avxCrossWord (a b : BitVec 64) := digitLow a * digitHigh b + digitHigh a * digitLow b

def avxCrossPack (memory : Memory) (left right : Reference) := CIL.Vector.pack256
  (avxCrossWord (inputLimb memory left 0) (inputLimb memory right 3))
  (avxCrossWord (inputLimb memory left 1) (inputLimb memory right 2))
  (avxCrossWord (inputLimb memory left 2) (inputLimb memory right 1))
  (avxCrossWord (inputLimb memory left 3) (inputLimb memory right 0))

/-- The cross products join the operand vectors and input words in initialized local homes. -/
def AvxCrossState (original current : Memory) (frame : Frame) (left right : Reference) : Prop :=
  LocalSnapshots current frame.locals
    (rememberLocal (avxOperandLocals original left right) 25 (.v256 (avxCrossPack original left right)))

theorem full_avx2_cross (profile : CIL.FeatureProfile) (program : CIL.Program)
    (methodIndex wordIndex countIndex storageIndex : Nat)
    (found : program[methodIndex]? = some (fullBody profile wordIndex countIndex storageIndex))
    (noAvx512 : profile.avx512DQVL = false) (avx2 : profile.avx2 = true)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (enteredWF : entered.WellFormed)
    (homes : CompleteWritableHomes entered original.nextIdentity (fullBody profile wordIndex countIndex storageIndex).localKinds frame.locals)
    (state : PrivateWords program original entered current [left, right] [output] frame
      (fullInputs original left right))
    (operands : AvxOperands original current frame left right)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after [left, right] [output] frame
        (fullInputs original left right) →
      AvxCrossState original after frame left right →
      ∃ fuel final returned,
        run program fuel methodIndex 72 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel methodIndex 56 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have profileEq : (fullBody profile wordIndex countIndex storageIndex).profile = profile := rfl
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact LocalSnapshots.load operands (.v256 (inputPack original left)) rfl
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact step_reinterpret256 _ _ _ _ _ _ _
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact LocalSnapshots.load operands (.v256 (reverseInputPack original right)) rfl
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · rfl
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · apply step_shift_right256; simpa only [profileEq] using avx2
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact step_reinterpret256 _ _ _ _ _ _ _
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · apply step_even_product256; simpa only [profileEq] using avx2
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact LocalSnapshots.load operands (.v256 (inputPack original left)) rfl
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · rfl
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · apply step_shift_right256; simpa only [profileEq] using avx2
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact step_reinterpret256 _ _ _ _ _ _ _
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact LocalSnapshots.load operands (.v256 (reverseInputPack original right)) rfl
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact step_reinterpret256 _ _ _ _ _ _ _
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · apply step_even_product256; simpa only [profileEq] using avx2
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · apply step_add256; simpa only [profileEq] using avx2
  simp only [digitLow_shift32]
  obtain ⟨after, crossHome, crossSlot, stored, afterState, _, written⟩ :=
    state.store_vector enteredWF homes 25 (by rfl) (avxCrossPack original left right)
      71 (productArgs left right output) [] (body := (fullBody profile wordIndex countIndex storageIndex))
  have vectors := LocalSnapshots.after_write operands homes.writable
    25 .vector256 crossHome (.v256 (avxCrossPack original left right)) _ rfl crossSlot written
  exact run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl) stored
    (continuation after afterState vectors)

#print axioms full_avx2_cross
end UInt256Proof.Multiply.Full

namespace UInt256Proof.Multiply.Full
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.BothTwo UInt256Proof.Multiply.VectorInputs

theorem full_avx2_finish (profile : CIL.FeatureProfile) (program : CIL.Program)
    (methodIndex wordIndex countIndex storageIndex : Nat)
    (found : program[methodIndex]? = some (fullBody profile wordIndex countIndex storageIndex))
    (noAvx512 : profile.avx512DQVL = false) (avx2 : profile.avx2 = true)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (enteredWF : entered.WellFormed)
    (homes : CompleteWritableHomes entered original.nextIdentity (fullBody profile wordIndex countIndex storageIndex).localKinds frame.locals)
    (state : PrivateWords program original entered current [left, right] [output] frame
      (fullInputs original left right))
    (vectors : AvxCrossState original current frame left right)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after [left, right] [output] frame
        (rememberWord (fullInputs original left right) 6 (fullTop original left right)) →
      ∃ fuel final returned,
        run program fuel methodIndex 96 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel methodIndex 72 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have profileEq : (fullBody profile wordIndex countIndex storageIndex).profile = profile := rfl
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact LocalSnapshots.load vectors (.v256 (inputPack original left)) rfl
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact step_reinterpret256 _ _ _ _ _ _ _
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact LocalSnapshots.load vectors (.v256 (reverseInputPack original right)) rfl
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact step_reinterpret256 _ _ _ _ _ _ _
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · apply step_even_product256; simpa only [profileEq] using avx2
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact LocalSnapshots.load vectors (.v256 (avxCrossPack original left right)) rfl
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · rfl
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · apply step_shift_left256; simpa only [profileEq] using avx2
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · apply step_add256; simpa only [profileEq] using avx2
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact step_sum256 _ _ _ _ _ _ _ _ _ _
  simp only [avxCrossWord, narrow_low_correct, lowProduct]
  obtain ⟨after, stored, finalState⟩ := state.store enteredWF homes 6 (by rfl)
    (fullTop original left right) 82 (productArgs left right output) [] (body := (fullBody profile wordIndex countIndex storageIndex))
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl) stored
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · simp [step, cil_guard, observerCount, pureArity, scalars, CIL.step.eq_def, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl, rfl⟩
  exact continuation after finalState

theorem full_avx2_top (profile : CIL.FeatureProfile) (program : CIL.Program)
    (methodIndex wordIndex countIndex storageIndex : Nat)
    (found : program[methodIndex]? = some (fullBody profile wordIndex countIndex storageIndex))
    (noAvx512 : profile.avx512DQVL = false) (avx2 : profile.avx2 = true) : FullTopContract profile program methodIndex wordIndex countIndex storageIndex := by
  intro original entered current left right output frame originalCall enteredWF homes state post continuation
  apply full_avx2_inputs profile program methodIndex wordIndex countIndex storageIndex found noAvx512 avx2 original entered current left right output frame originalCall enteredWF homes state post
  intro prepared preparedState operands
  apply full_avx2_cross profile program methodIndex wordIndex countIndex storageIndex found noAvx512 avx2 original entered prepared left right output frame enteredWF homes preparedState operands post
  intro cross crossState vectors
  exact full_avx2_finish profile program methodIndex wordIndex countIndex storageIndex found noAvx512 avx2 original entered cross left right output frame enteredWF homes crossState vectors post continuation

#print axioms full_avx2_finish
#print axioms full_avx2_top
end UInt256Proof.Multiply.Full
