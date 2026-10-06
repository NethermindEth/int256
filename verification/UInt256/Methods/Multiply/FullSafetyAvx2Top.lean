import UInt256.Methods.Multiply.FullSafetyVectorInputs

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

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

theorem full_avx2_inputs
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions Extracted.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity fullBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (fullInputs original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (fullInputs original left right) →
      AvxOperands original after frame left right →
      ∃ fuel final returned,
        run Extracted.program fuel fullIndex 50 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel fullIndex 18 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[fullIndex]? = some fullBody := by rfl
  have profile : fullBody.profile = Extracted.profile := by rfl
  have formedLeft := state.call.input_formed (by simp : left ∈ [left, right])
  have loadedLeft := input_vector_snapshot state originalCall left (by simp)
  iterate 8
    apply run_next_exists post found (by rfl)
    simp (config := { implicitDefEqProofs := false })
      [step, pureArity, productArgs, checkedValue, numericValue, formValue, formedLeft,
        staticInstruction, memoryInstruction, loadedLeft, checkedAt, profile, Extracted.profile,
        CIL.FeatureProfile.evaluate, scalars, CIL.step, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨middle, leftHome, leftSlot, storedLeft, middleState, leftRead, _⟩ :=
    state.store_vector enteredWF homes 23 (by rfl) (inputPack original left)
      42 (productArgs left right output) [] (body := fullBody)
  apply run_next_exists post found (by rfl) storedLeft
  have formedRight := middleState.call.input_formed (by simp : right ∈ [left, right])
  have loadedRight := input_vector_snapshot middleState originalCall right (by simp)
  iterate 6
    apply run_next_exists post found (by rfl)
    simp (config := { implicitDefEqProofs := false })
      [step, pureArity, productArgs, checkedValue, numericValue, formValue, formedRight,
        staticInstruction, memoryInstruction, loadedRight, checkedAt, profile, Extracted.profile,
        CIL.Intrinsic.available, scalars, CIL.step, eval_reverse256, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨after, rightHome, rightSlot, storedRight, afterState, rightRead, written⟩ :=
    middleState.store_vector enteredWF homes 24 (by rfl) (reverseInputPack original right)
      49 (productArgs left right output) [] (body := fullBody)
  have preservedLeft := write_preserves_disjoint_read written leftRead
    (Or.inl (homes.distinct 23 24 .vector256 .vector256 leftHome rightHome (by decide) leftSlot rightSlot))
  exact run_next_exists post found (by rfl) storedRight
    (continuation after afterState ⟨leftHome, rightHome, leftSlot, rightSlot, preservedLeft, rightRead⟩)

#print axioms full_avx2_inputs
end UInt256Proof.Multiply.Safety

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

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

theorem full_avx2_cross
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity fullBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (fullInputs original left right))
    (operands : AvxOperands original current frame left right)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (fullInputs original left right) →
      AvxCrossState original after frame left right →
      ∃ fuel final returned,
        run Extracted.program fuel fullIndex 66 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel fullIndex 50 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[fullIndex]? = some fullBody := by rfl
  have profile : fullBody.profile = Extracted.profile := by rfl
  have loadLeft := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := fullBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    .vector256 (.v256 (inputPack original left)) (inputPack original left).toNat rfl operands.leftSlot operands.leftRead
  have loadRight := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := fullBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    .vector256 (.v256 (reverseInputPack original right)) (reverseInputPack original right).toNat rfl operands.rightSlot operands.rightRead
  iterate 15
    apply run_next_exists post found (by rfl)
    first
    | exact loadLeft _ _
    | exact loadRight _ _
    | simp (config := { implicitDefEqProofs := false })
        [step, pureArity, checkedValue, numericValue, scalars, CIL.step, profile, Extracted.profile,
          CIL.Intrinsic.available, inputPack, reverseInputPack,
          eval_reinterpret256, eval_shift_right256, eval_even_product256, eval_add256,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨after, crossHome, crossSlot, stored, afterState, crossRead, written⟩ :=
    state.store_vector enteredWF homes 25 (by rfl) (avxCrossPack original left right)
      65 (productArgs left right output) [] (body := fullBody)
  have leftRead := write_preserves_disjoint_read written operands.leftRead
    (Or.inl (homes.distinct 23 25 .vector256 .vector256 operands.leftHome crossHome
      (by decide) operands.leftSlot crossSlot))
  have rightRead := write_preserves_disjoint_read written operands.rightRead
    (Or.inl (homes.distinct 24 25 .vector256 .vector256 operands.rightHome crossHome
      (by decide) operands.rightSlot crossSlot))
  exact run_next_exists post found (by rfl) stored
    (continuation after afterState
      ⟨⟨operands.leftHome, operands.rightHome, operands.leftSlot, operands.rightSlot, leftRead, rightRead⟩,
        crossHome, crossSlot, crossRead⟩)

#print axioms full_avx2_cross
end UInt256Proof.Multiply.Safety

namespace UInt256Proof.Multiply.Safety
open CIL.Safety UInt256Model.Safety

theorem full_avx2_finish
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity fullBody.localKinds frame.locals)
    (state : PrivateWords Extracted.program original entered current [left, right] [output] frame
      (fullInputs original left right))
    (vectors : AvxCrossState original current frame left right)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords Extracted.program original entered after [left, right] [output] frame
        (rememberWord (fullInputs original left right) 6 (fullTop original left right)) →
      ∃ fuel final returned,
        run Extracted.program fuel fullIndex 96 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel fullIndex 66 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have found : Extracted.program[fullIndex]? = some fullBody := by rfl
  have profile : fullBody.profile = Extracted.profile := by rfl
  have loadLeft := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := fullBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    .vector256 (.v256 (inputPack original left)) (inputPack original left).toNat rfl
      vectors.operands.leftSlot vectors.operands.leftRead
  have loadRight := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := fullBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    .vector256 (.v256 (reverseInputPack original right)) (reverseInputPack original right).toNat rfl
      vectors.operands.rightSlot vectors.operands.rightRead
  have loadCross := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := fullBody) (args := productArgs left right output) (pc := pc) (stack := stack)
    .vector256 (.v256 (avxCrossPack original left right)) (avxCrossPack original left right).toNat rfl
      vectors.crossSlot vectors.crossRead
  iterate 10
    apply run_next_exists post found (by rfl)
    first
    | exact loadLeft _ _
    | exact loadRight _ _
    | exact loadCross _ _
    | simp (config := { implicitDefEqProofs := false })
        [step, pureArity, checkedValue, numericValue, scalars, CIL.step, profile, Extracted.profile,
          CIL.Intrinsic.available, inputPack, reverseInputPack, avxCrossPack, avxCrossWord,
          eval_reinterpret256, eval_shift_left256, eval_even_product256, eval_add256, eval_sum256,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  simp only [narrow_low_split, lowProduct]
  obtain ⟨after, stored, finalState⟩ := state.store enteredWF homes 6 (by rfl)
    (fullTop original left right) 76 (productArgs left right output) [] (body := fullBody)
  apply run_next_exists post found (by rfl) stored
  apply run_next_exists post found (by rfl)
  · simp [step, pureArity, scalars, CIL.step, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl, rfl⟩
  exact continuation after finalState

theorem full_avx2_top : FullTopContract := by
  intro original entered current left right output frame originalCall enteredWF homes state post continuation
  apply full_avx2_inputs original entered current left right output frame originalCall enteredWF homes state post
  intro prepared preparedState operands
  apply full_avx2_cross original entered prepared left right output frame enteredWF homes preparedState operands post
  intro cross crossState vectors
  exact full_avx2_finish original entered cross left right output frame enteredWF homes crossState vectors post continuation

#print axioms full_avx2_finish
#print axioms full_avx2_top
end UInt256Proof.Multiply.Safety
