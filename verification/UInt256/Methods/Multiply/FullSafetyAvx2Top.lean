import UInt256.Methods.Multiply.FullSafety
import UInt256.Methods.Multiply.VectorInputs
import UInt256.Methods.Multiply.VectorSteps

namespace UInt256Proof.Multiply.Full
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.BothTwo UInt256Proof.Multiply.VectorInputs

def inputPack (memory : Memory) (input : Reference) := CIL.Vector.pack256
  (inputLimb memory input 0) (inputLimb memory input 1) (inputLimb memory input 2) (inputLimb memory input 3)

def reverseInputPack (memory : Memory) (input : Reference) := CIL.Vector.pack256
  (inputLimb memory input 3) (inputLimb memory input 2) (inputLimb memory input 1) (inputLimb memory input 0)

structure AvxOperands (original current : Memory) (frame : Frame) (left right : Reference) where
  leftHome : Reference
  rightHome : Reference
  leftSlot : frame.locals[23]? = some (.bytes .vector256 leftHome)
  rightSlot : frame.locals[24]? = some (.bytes .vector256 rightHome)
  leftRead : read current leftHome 32 1 = .ok (numberBytes (inputPack original left).toNat 32)
  rightRead : read current rightHome 32 1 = .ok (numberBytes (reverseInputPack original right).toNat 32)

theorem full_avx2_inputs (profile : CIL.FeatureProfile) (program : CIL.Program)
    (methodIndex wordIndex countIndex storageIndex : Nat)
    (found : program[methodIndex]? = some (fullBody profile wordIndex countIndex storageIndex))
    (noAvx512 : profile.avx512DQVL = false) (avx2 : profile.avx2 = true)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (fullBody profile wordIndex countIndex storageIndex).localKinds frame.locals)
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
      [step, pureArity, productArgs, checkedValue, numericValue, formValue, formedLeft,
        staticInstruction, memoryInstruction, loadedLeft, checkedAt, profileEq, noAvx512, avx2,
        CIL.FeatureProfile.evaluate, scalars, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨middle, leftHome, leftSlot, storedLeft, middleState, leftRead, _⟩ :=
    state.store_vector enteredWF homes 23 (by rfl) (inputPack original left)
      48 (productArgs left right output) [] (body := (fullBody profile wordIndex countIndex storageIndex))
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl) storedLeft
  have formedRight := middleState.call.input_formed (by simp : right ∈ [left, right])
  have loadedRight := input_vector_snapshot middleState originalCall right (by simp)
  iterate 6
    apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
    simp (config := { implicitDefEqProofs := false })
      [step, pureArity, productArgs, checkedValue, numericValue, formValue, formedRight,
        staticInstruction, memoryInstruction, loadedRight, checkedAt, profileEq, avx2,
        CIL.Intrinsic.available, scalars, checkedIntrinsic, eval_reverse256, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨after, rightHome, rightSlot, storedRight, afterState, rightRead, written⟩ :=
    middleState.store_vector enteredWF homes 24 (by rfl) (reverseInputPack original right)
      55 (productArgs left right output) [] (body := (fullBody profile wordIndex countIndex storageIndex))
  have preservedLeft := write_preserves_disjoint_read written leftRead
    (Or.inl (homes.distinct 23 24 .vector256 .vector256 leftHome rightHome (by decide) leftSlot rightSlot))
  exact run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl) storedRight
    (continuation after afterState ⟨leftHome, rightHome, leftSlot, rightSlot, preservedLeft, rightRead⟩)

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

structure AvxCrossState (original current : Memory) (frame : Frame) (left right : Reference) where
  operands : AvxOperands original current frame left right
  crossHome : Reference
  crossSlot : frame.locals[25]? = some (.bytes .vector256 crossHome)
  crossRead : read current crossHome 32 1 = .ok (numberBytes (avxCrossPack original left right).toNat 32)

theorem full_avx2_cross (profile : CIL.FeatureProfile) (program : CIL.Program)
    (methodIndex wordIndex countIndex storageIndex : Nat)
    (found : program[methodIndex]? = some (fullBody profile wordIndex countIndex storageIndex))
    (noAvx512 : profile.avx512DQVL = false) (avx2 : profile.avx2 = true)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (fullBody profile wordIndex countIndex storageIndex).localKinds frame.locals)
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
  have loadLeft := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := (fullBody profile wordIndex countIndex storageIndex)) (args := productArgs left right output) (pc := pc) (stack := stack)
    .vector256 (.v256 (inputPack original left)) (inputPack original left).toNat rfl operands.leftSlot operands.leftRead
  have loadRight := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := (fullBody profile wordIndex countIndex storageIndex)) (args := productArgs left right output) (pc := pc) (stack := stack)
    .vector256 (.v256 (reverseInputPack original right)) (reverseInputPack original right).toNat rfl operands.rightSlot operands.rightRead
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact loadLeft _ _
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact step_reinterpret256 _ _ _ _ _ _ _
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact loadRight _ _
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · rfl
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · apply step_shift_right256; simpa only [profileEq] using avx2
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact step_reinterpret256 _ _ _ _ _ _ _
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · apply step_even_product256; simpa only [profileEq] using avx2
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact loadLeft _ _
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · rfl
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · apply step_shift_right256; simpa only [profileEq] using avx2
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact step_reinterpret256 _ _ _ _ _ _ _
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact loadRight _ _
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact step_reinterpret256 _ _ _ _ _ _ _
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · apply step_even_product256; simpa only [profileEq] using avx2
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · apply step_add256; simpa only [profileEq] using avx2
  simp only [digitLow_shift32]
  obtain ⟨after, crossHome, crossSlot, stored, afterState, crossRead, written⟩ :=
    state.store_vector enteredWF homes 25 (by rfl) (avxCrossPack original left right)
      71 (productArgs left right output) [] (body := (fullBody profile wordIndex countIndex storageIndex))
  have leftRead := write_preserves_disjoint_read written operands.leftRead
    (Or.inl (homes.distinct 23 25 .vector256 .vector256 operands.leftHome crossHome
      (by decide) operands.leftSlot crossSlot))
  have rightRead := write_preserves_disjoint_read written operands.rightRead
    (Or.inl (homes.distinct 24 25 .vector256 .vector256 operands.rightHome crossHome
      (by decide) operands.rightSlot crossSlot))
  exact run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl) stored
    (continuation after afterState
      ⟨⟨operands.leftHome, operands.rightHome, operands.leftSlot, operands.rightSlot, leftRead, rightRead⟩,
        crossHome, crossSlot, crossRead⟩)

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
    (homes : WritableHomes entered original.nextIdentity (fullBody profile wordIndex countIndex storageIndex).localKinds frame.locals)
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
  have loadLeft := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := (fullBody profile wordIndex countIndex storageIndex)) (args := productArgs left right output) (pc := pc) (stack := stack)
    .vector256 (.v256 (inputPack original left)) (inputPack original left).toNat rfl
      vectors.operands.leftSlot vectors.operands.leftRead
  have loadRight := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := (fullBody profile wordIndex countIndex storageIndex)) (args := productArgs left right output) (pc := pc) (stack := stack)
    .vector256 (.v256 (reverseInputPack original right)) (reverseInputPack original right).toNat rfl
      vectors.operands.rightSlot vectors.operands.rightRead
  have loadCross := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := (fullBody profile wordIndex countIndex storageIndex)) (args := productArgs left right output) (pc := pc) (stack := stack)
    .vector256 (.v256 (avxCrossPack original left right)) (avxCrossPack original left right).toNat rfl
      vectors.crossSlot vectors.crossRead
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact loadLeft _ _
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact step_reinterpret256 _ _ _ _ _ _ _
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact loadRight _ _
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact step_reinterpret256 _ _ _ _ _ _ _
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · apply step_even_product256; simpa only [profileEq] using avx2
  apply run_next_exists post found (by change some _ = _; first | (simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl) | rfl)
  · exact loadCross _ _
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
  · simp [step, pureArity, scalars, CIL.step.eq_def, Bind.bind, Except.bind, Pure.pure, Except.pure]
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