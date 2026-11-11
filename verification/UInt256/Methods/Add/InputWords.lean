import UInt256.Safety.CallerSetup
import UInt256.Safety.LimbAccess

/-! Input words that stepping reads through a caller view are the caller's original limbs. -/

namespace UInt256Model.Safety

open CIL.Safety

/-- A word field read at any memory that keeps the caller's bytes is the original limb, at
    each of the four offsets a field load uses. -/
theorem CallingConditions.input_words_kept {program : CIL.Program} {original current : Memory}
    {inputs outputs : List Reference} (call : CallingConditions program original inputs outputs)
    (below : MemoryBelow original.nextIdentity original current) (input : Reference)
    (member : input ∈ inputs) :
    (⟨input, 32⟩ : ArgumentView).word current 0 = inputLimb original input 0 ∧
      (⟨input, 32⟩ : ArgumentView).word current 8 = inputLimb original input 1 ∧
      (⟨input, 32⟩ : ArgumentView).word current 16 = inputLimb original input 2 ∧
      (⟨input, 32⟩ : ArgumentView).word current 24 = inputLimb original input 3 := by
  have limb (index : Fin 4) :
      (⟨input, 32⟩ : ArgumentView).word current (8 * index.val) =
        inputLimb original input index := by
    have packed := byteNumber_snapshot
      (fun offset => (current.cells input.allocation offset).bits) (input.offset + 8 * index.val) 8
    rw [call.input_bytes_of_memory_below below member] at packed
    unfold inputLimb
    rw [← packed]
    obtain ⟨index, bound⟩ := index
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> rfl
  exact ⟨limb 0, limb 1, limb 2, limb 3⟩

end UInt256Model.Safety
