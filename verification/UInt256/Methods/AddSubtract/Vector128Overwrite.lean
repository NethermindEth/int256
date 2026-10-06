import UInt256.Methods.AddSubtract.Vector128Memory

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety

/-- Overwriting any private vector home preserves every other vector home.
    Distinctness is derived from actual frame allocation order. -/
theorem vector128_other_read (entered before after : Memory) (boundary : Nat)
    (slots : List LocalSlot) (homes : NumericHomes entered boundary vector128Specs slots)
    (i j : Nat) (different : i ≠ j) (source target : Reference)
    (sourceSlot : slots[i]? = some (.bytes .vector128 source))
    (targetSlot : slots[j]? = some (.bytes .vector128 target))
    (bytes value : List (BitVec 8))
    (written : write before target bytes 1 = .ok after)
    (loaded : read before source 16 1 = .ok value) :
    read after source 16 1 = .ok value := by
  by_cases earlier : i < j
  · exact vector128_prior_read entered before after boundary slots homes i j earlier
      source target sourceSlot targetSlot bytes value written loaded
  · have ordered := homes.ordered j i .vector128 .vector128 target source (by omega) targetSlot sourceSlot
    exact write_preserves_disjoint_read written loaded (Or.inl (Nat.ne_of_gt ordered))

#print axioms vector128_other_read
end UInt256Proof.AddSubtract.Safety
