import UInt256.Methods.Multiply.FullSafety
import UInt256.Methods.Multiply.VectorInputs
import UInt256.Methods.Multiply.VectorSteps

/-! The AVX2 top product carries initialized word and vector homes through shared snapshots. -/

namespace UInt256Proof.Multiply.Full
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.BothTwo UInt256Proof.Multiply.VectorInputs

/-- The four input limbs in their vector lane order. -/
def inputPack (memory : Memory) (input : Reference) := CIL.Vector.pack256
  (inputLimb memory input 0) (inputLimb memory input 1) (inputLimb memory input 2) (inputLimb memory input 3)

/-- The reversed input lanes align the four top-word products. -/
def reverseInputPack (memory : Memory) (input : Reference) := CIL.Vector.pack256
  (inputLimb memory input 3) (inputLimb memory input 2) (inputLimb memory input 1) (inputLimb memory input 0)

/-- Initialized input words and the two vector operands; every other home remains unknown. -/
def avxOperandLocals (original : Memory) (left right : Reference) : Nat → Option CIL.Value :=
  rememberLocal (rememberLocal (wordLocals (fullInputs original left right))
    23 (.v256 (inputPack original left))) 24 (.v256 (reverseInputPack original right))

/-- Cross products of the low and high 32-bit digits of a limb pair. -/
def avxCrossWord (a b : BitVec 64) := digitLow a * digitHigh b + digitHigh a * digitLow b

/-- Cross products for the four limb pairs contributing to the top word. -/
def avxCrossPack (memory : Memory) (left right : Reference) := CIL.Vector.pack256
  (avxCrossWord (inputLimb memory left 0) (inputLimb memory right 3))
  (avxCrossWord (inputLimb memory left 1) (inputLimb memory right 2))
  (avxCrossWord (inputLimb memory left 2) (inputLimb memory right 1))
  (avxCrossWord (inputLimb memory left 3) (inputLimb memory right 0))

/-- The checked AVX2 path computes the top product while preserving caller and private words. -/
theorem full_avx2_top (profile : CIL.FeatureProfile) (program : CIL.Program)
    (methodIndex wordIndex countIndex storageIndex : Nat)
    (found : program[methodIndex]? = some (fullBody profile wordIndex countIndex storageIndex))
    (noAvx512 : profile.avx512DQVL = false) (avx2 : profile.avx2 = true) :
    FullTopContract profile program methodIndex wordIndex countIndex storageIndex := by
  intro original entered current left right output frame originalCall enteredWF homes state
    post continuation
  have profileEq : (fullBody profile wordIndex countIndex storageIndex).profile = profile := rfl
  have formedLeft := state.call.input_formed (by simp : left ∈ [left, right])
  have loadedLeft := input_vector_snapshot state originalCall left (by simp)
  cil_contract_steps 14 [found, productArgs, formedLeft, loadedLeft,
    profileEq, noAvx512, avx2, CIL.FeatureProfile.evaluate]
  obtain ⟨middle, leftHome, leftSlot, storedLeft, middleState, _, writtenLeft⟩ :=
    state.store_vector enteredWF homes 23 (by rfl) (inputPack original left)
      48 (productArgs left right output) []
      (body := fullBody profile wordIndex countIndex storageIndex)
  have snapshots := state.snapshots.toLocalSnapshots.after_write homes.writable
    23 .vector256 leftHome (.v256 (inputPack original left)) _ rfl leftSlot writtenLeft
  apply run_next_exists post found
    (by change some _ = _; simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl)
    storedLeft
  have formedRight := middleState.call.input_formed (by simp : right ∈ [left, right])
  have loadedRight := input_vector_snapshot middleState originalCall right (by simp)
  cil_contract_steps 6 [found, productArgs, formedRight, loadedRight,
    profileEq, noAvx512, avx2, eval_reverse256]
  obtain ⟨after, rightHome, rightSlot, storedRight, afterState, _, written⟩ :=
    middleState.store_vector enteredWF homes 24 (by rfl) (reverseInputPack original right)
      55 (productArgs left right output) []
      (body := fullBody profile wordIndex countIndex storageIndex)
  have operands := snapshots.after_write homes.writable
    24 .vector256 rightHome (.v256 (reverseInputPack original right)) _ rfl rightSlot written
  apply run_next_exists post found
    (by change some _ = _; simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl)
    storedRight
  have loaded (index : Nat) (value : CIL.Value)
      (known : avxOperandLocals original left right index = some value)
      (pc : Nat) (stack : List Value) := operands.load
    (body := fullBody profile wordIndex countIndex storageIndex)
    (pc := pc) (args := productArgs left right output) (stack := stack) value known
  cil_contract_steps 15 [found, profileEq, noAvx512, avx2,
    loaded 23 (.v256 (inputPack original left)) rfl,
    loaded 24 (.v256 (reverseInputPack original right)) rfl,
    inputPack, reverseInputPack, step_reinterpret256, step_shift_right256,
    step_even_product256, step_add256]
  simp only [digitLow_shift32]
  obtain ⟨cross, crossHome, crossSlot, stored, crossState, _, written⟩ :=
    afterState.store_vector enteredWF homes 25 (by rfl) (avxCrossPack original left right)
      71 (productArgs left right output) []
      (body := fullBody profile wordIndex countIndex storageIndex)
  have vectors := LocalSnapshots.after_write operands homes.writable
    25 .vector256 crossHome (.v256 (avxCrossPack original left right)) _ rfl crossSlot written
  apply run_next_exists post found
    (by change some _ = _; simp only [noAvx512, avx2, Bool.false_eq_true, ↓reduceIte] <;> rfl)
    stored
  have loaded (index : Nat) (value : CIL.Value)
      (known : rememberLocal (avxOperandLocals original left right) 25
        (.v256 (avxCrossPack original left right)) index = some value)
      (pc : Nat) (stack : List Value) := vectors.load
    (body := fullBody profile wordIndex countIndex storageIndex)
    (pc := pc) (args := productArgs left right output) (stack := stack) value known
  cil_contract_steps 10 [found, profileEq, noAvx512, avx2,
    loaded 23 (.v256 (inputPack original left)) rfl,
    loaded 24 (.v256 (reverseInputPack original right)) rfl,
    loaded 25 (.v256 (avxCrossPack original left right)) rfl,
    inputPack, reverseInputPack, avxCrossPack, step_reinterpret256,
    step_even_product256, step_shift_left256, step_add256, step_sum256]
  simp only [avxCrossWord, narrow_low_correct, lowProduct]
  obtain ⟨after, stored, finalState⟩ := crossState.store enteredWF homes 6 (by rfl)
    (fullTop original left right) 82 (productArgs left right output) []
      (body := fullBody profile wordIndex countIndex storageIndex)
  cil_contract_steps [found, noAvx512, avx2, stored, fullTop] until continuation after finalState

end UInt256Proof.Multiply.Full
