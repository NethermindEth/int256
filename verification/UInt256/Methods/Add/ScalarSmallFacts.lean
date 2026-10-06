import UInt256.Methods.Add.ScalarSmallFinish

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

theorem input_small_value (memory : CIL.Safety.Memory) (reference : Reference)
    (small : inputLimb memory reference 1 ||| inputLimb memory reference 2 |||
      inputLimb memory reference 3 = 0) :
    inputValue memory reference = BitVec.ofNat 256 (inputLimb memory reference 0).toNat := by
  obtain ⟨h12, h3⟩ := BitVec.or_eq_zero_iff.mp small
  obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h12
  have initial : UInt256Model.value (inputLimb memory reference) = inputValue memory reference :=
    UInt256Proof.input_value (fun offset => (memory.cells reference.allocation offset).bits) reference.offset
  rw [← initial, ← UInt256Proof.singleLimb_eq (inputLimb memory reference) h1 h2 h3]
  simp [UInt256Model.value, UInt256Proof.singleLimb]

theorem scalar_small_values (swapped : Bool) (original current : CIL.Safety.Memory)
    (left right output : Reference)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (small : inputLimb original (if swapped then left else right) 1 |||
      inputLimb original (if swapped then left else right) 2 |||
      inputLimb original (if swapped then left else right) 3 = 0) :
    let word := inputLimb original (if swapped then left else right) 0
    (inputValue current (scalarSmallSource swapped left right) + BitVec.ofNat 256 word.toNat =
      inputValue original left + inputValue original right) ∧
    ((inputValue current (scalarSmallSource swapped left right)).toNat + word.toNat =
      (inputValue original left).toNat + (inputValue original right).toNat) := by
  have smallValue := input_small_value original (if swapped then left else right) small
  have wideBound : (inputLimb original (if swapped then left else right) 0).toNat < 2^256 :=
    Nat.lt_trans (inputLimb original (if swapped then left else right) 0).isLt (by decide)
  have preservedValue : ∀ reference ∈ [left, right], inputValue current reference = inputValue original reference := by
    intro reference member
    simp only [inputValue, call.input_bytes_of_memory_below preserved member]
  cases swapped
  · have kept := preservedValue left (by simp)
    dsimp at smallValue wideBound ⊢
    simp [scalarSmallSource, kept, smallValue, Nat.mod_eq_of_lt wideBound]
  · have kept := preservedValue right (by simp)
    dsimp at smallValue wideBound ⊢
    simp [scalarSmallSource, kept, smallValue, Nat.mod_eq_of_lt wideBound, BitVec.add_comm, Nat.add_comm]

theorem scalar_private_next (original entered current : CIL.Safety.Memory) (frame : Frame)
    (homes : WordHomes entered original.nextIdentity scalarLocalSpecs frame.locals)
    (enteredWF : entered.WellFormed) (currentWF : current.WellFormed)
    (authority : AccessBelow entered.nextIdentity entered current) : original.nextIdentity ≤ current.nextIdentity := by
  have specified : scalarLocalSpecs[0]? = some (some 0) := by simp [scalarLocalSpecs, cil_code]
  obtain ⟨reference, _, fresh, _, writable⟩ := homes.word_at 0 0 specified
  obtain ⟨allocation, ready⟩ := access_requirements writable
  have currentWrite := authority.access writable (enteredWF.1 _ _ ready.present).1
  obtain ⟨currentAllocation, currentReady⟩ := access_requirements currentWrite
  exact Nat.le_trans fresh (Nat.le_of_lt (currentWF.1 _ _ currentReady.present).1)

#print axioms input_small_value
#print axioms scalar_small_values
#print axioms scalar_private_next

end UInt256Proof.Safety
