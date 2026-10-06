import UInt256.Methods.AddSubtract.Vector128Setup
import UInt256.Safety.NumericStore
import UInt256.Safety.HalfAccess

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety

/-- The reference root may change while the numeric homes retain their addresses.
    Stores use the actual shifted local index from the mixed frame. -/
theorem vector128_local_store (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (index : Nat) (spec : NumericLocalSpec)
    (specified : vector128Specs[index]? = some spec)
    (value : CIL.Value) (number : Nat)
    (fits : localNumber spec.kind value = .ok number) :
    ∃ reference after,
      frame.locals[index + 1]? = some (.bytes spec.kind reference) ∧
      read after reference (localWidth spec.kind) 1 =
        .ok (numberBytes number (localWidth spec.kind)) ∧
      MemoryBelow boundary current after ∧
      CallingConditions Extracted.program after inputs outputs ∧
      AccessBelow entered.nextIdentity entered after ∧
      write current reference (numberBytes number (localWidth spec.kind)) 1 = .ok after ∧
      ∀ pc args rest, step vector128Body (.setLocal (index + 1)) pc args frame
        (.scalar value :: rest) current = .ok (.next (pc + 1) rest frame after) := by
  obtain ⟨reference, slot, bound, _, writable⟩ := homes.home_at index spec specified
  have actual : frame.locals[index + 1]? = some (.bytes spec.kind reference) := by
    simpa [layout] using slot
  obtain ⟨after, result⟩ := checked_numeric_home_store Extracted.program vector128Body boundary
    entered current inputs outputs frame currentCall enteredWF authority (index + 1)
    spec reference actual bound writable value number fits
  exact ⟨reference, after, actual, result⟩

/-- Private writes preserve the initial operand halves, including when caller
    operands overlap each other or the output. -/
theorem vector128_input_load (original current : Memory)
    (inputs outputs : List Reference) (input : Reference) (half : Fin 2)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (member : input ∈ inputs)
    (preserved : MemoryBelow original.nextIdentity original current) :
    loadValue current (.address { input with offset := input.offset + 16 * half.val }) 16 =
      .ok (.v128 (inputHalf original input half)) := by
  rw [currentCall.input_half_load member half]
  simp only [inputHalf, call.input_bytes_of_memory_below preserved member]

#print axioms vector128_local_store
#print axioms vector128_input_load

/-- A write to a later private home preserves an earlier snapshot. The ordering
    comes from actual frame allocation, with no separation premise on callers. -/
theorem vector128_prior_read (entered before after : Memory) (boundary : Nat)
    (slots : List LocalSlot) (homes : NumericHomes entered boundary vector128Specs slots)
    (i j : Nat) (earlier : i < j) (source target : Reference)
    (sourceSlot : slots[i]? = some (.bytes .vector128 source))
    (targetSlot : slots[j]? = some (.bytes .vector128 target))
    (bytes value : List (BitVec 8))
    (written : write before target bytes 1 = .ok after)
    (loaded : read before source 16 1 = .ok value) :
    read after source 16 1 = .ok value := by
  have ordered := homes.ordered i j .vector128 .vector128 source target earlier sourceSlot targetSlot
  exact write_preserves_disjoint_read written loaded (Or.inl (Nat.ne_of_lt ordered))

#print axioms vector128_prior_read
end UInt256Proof.AddSubtract.Safety
