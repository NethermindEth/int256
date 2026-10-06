import UInt256.Methods.Add.Vector128ARMScalarSwap
import UInt256.Methods.Add.ARMSmallParentCall

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety

theorem arm_scalar_small_value (memory : Memory) (input : Reference)
    (small : armScalarUpper memory input = BitVec.ofNat 64 0) :
    inputValue memory input = BitVec.ofNat 256 (inputLimb memory input 0).toNat := by
  obtain ⟨upper, h3⟩ := BitVec.or_eq_zero_iff.mp small
  obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp upper
  have initial : UInt256Model.value (inputLimb memory input) = inputValue memory input :=
    UInt256Proof.input_value (fun offset => (memory.cells input.allocation offset).bits) input.offset
  rw [← initial, ← UInt256Proof.singleLimb_eq (inputLimb memory input) h1 h2 h3]
  simp [UInt256Model.value, UInt256Proof.singleLimb]

/-- Convert either selected small operand into the same initial two-input sum,
    including its unbounded natural sum for the exact overflow contract. -/
theorem arm_scalar_small_values (swapped : Bool) (original current : Memory)
    (left right output : Reference)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (small : armScalarUpper current (if swapped then left else right) = BitVec.ofNat 64 0) :
    let word := inputLimb current (if swapped then left else right) 0
    (inputValue current (if swapped then right else left) + BitVec.ofNat 256 word.toNat =
      inputValue original left + inputValue original right) ∧
    ((inputValue current (if swapped then right else left)).toNat + word.toNat =
      (inputValue original left).toNat + (inputValue original right).toNat) := by
  have smallValue := arm_scalar_small_value current (if swapped then left else right) small
  have wideBound : (inputLimb current (if swapped then left else right) 0).toNat < 2^256 :=
    Nat.lt_trans (inputLimb current (if swapped then left else right) 0).isLt (by decide)
  have kept : ∀ reference ∈ [left, right], inputValue current reference = inputValue original reference := by
    intro reference member
    simp only [inputValue, call.input_bytes_of_memory_below preserved member]
  have keptLeft := kept left (by simp)
  have keptRight := kept right (by simp)
  cases swapped
  · dsimp at smallValue wideBound ⊢
    rw [← keptLeft, ← keptRight, smallValue]
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt wideBound]
  · dsimp at smallValue wideBound ⊢
    rw [← keptLeft, ← keptRight, smallValue]
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt wideBound, BitVec.add_comm, Nat.add_comm]

/-- Select one existing readable input view without imposing alias restrictions. -/
theorem arm_scalar_select_input (memory : Memory) (inputs : List Reference) (input output : Reference)
    (call : CallingConditions Extracted.program memory inputs [output]) (member : input ∈ inputs) :
    CallingConditions Extracted.program memory [input] [output] := by
  refine ⟨⟨call.1.1, ?_, call.1.2.2⟩, call.2⟩
  intro view selected
  have same : view = wordView input := by simpa using selected
  subst view
  exact call.1.2.1 _ (List.mem_map.mpr ⟨input, member, rfl⟩)

/-- Original frame-home authority bounds the current allocation watermark. -/
theorem arm_scalar_watermark (original entered current : Memory) (frame : Frame)
    (homes : WordHomes entered original.nextIdentity scalarLocalSpecs frame.locals)
    (enteredWF : entered.WellFormed) (currentWF : current.WellFormed)
    (authority : AccessBelow entered.nextIdentity entered current) :
    original.nextIdentity ≤ current.nextIdentity := by
  obtain ⟨home, _, fresh, _, writable⟩ := homes.word_at 0 0 (by rfl)
  obtain ⟨allocation, ready⟩ := access_requirements writable
  have retained := authority.access writable (enteredWF.1 _ _ ready.present).1
  obtain ⟨currentAllocation, currentReady⟩ := access_requirements retained
  exact Nat.le_trans fresh (Nat.le_of_lt (currentWF.1 _ _ currentReady.present).1)

#print axioms arm_scalar_small_value
#print axioms arm_scalar_small_values
#print axioms arm_scalar_select_input
#print axioms arm_scalar_watermark
end UInt256Proof.Add.Safety
