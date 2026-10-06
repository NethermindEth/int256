import UInt256.Methods.Multiply.FullSafetyAvx2Inputs

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
