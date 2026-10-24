import UInt256.Methods.Compare.PortableSafetyContract
import UInt256.Methods.Compare.InclusiveSafety
import UInt256.Safety.ProfileContracts

namespace UInt256Proof.Compare.Safety
open UInt256Model.Safety

/-- Bind the discovered comparison chain to the extracted public entry and the
independent unsigned ordering of its two initial inputs. -/
theorem checked_greater_equal_contract :
    ReadOnlyContract
      (fun values => .i32 (if (values[1]?.getD 0).toNat ≤ (values[0]?.getD 0).toNat then 1 else 0))
      Extracted.program Extracted.entryIndex 2 := by
  have value (x y : BitVec 256) : inclusiveValue y x =
      .i32 (if y.toNat ≤ x.toNat then 1 else 0) := by
    simp [inclusiveValue, middleFlag, show middleSwaps = true from rfl, strictFlag]
  have entry : BinaryReadOnlyInvocation
      (fun x y => .i32 (if y.toNat ≤ x.toNat then 1 else 0))
      Extracted.program Extracted.entryIndex := by
    simpa only [value, show wrapperIndex .entry = Extracted.entryIndex from rfl] using (inclusive_entry_checked (portable_checked Extracted.profile Extracted.program wrapperLeafIndex (wrapperLeafIndex + 1) rfl rfl))
  exact entry.to_contract

theorem checked_greater_equal_binding :
    ReadOnlyContract
      (fun values => .i32 (if (values[1]?.getD 0).toNat ≤ (values[0]?.getD 0).toNat then 1 else 0))
      Extracted.program Extracted.entryIndex 2 := checked_greater_equal_contract

#print axioms checked_greater_equal_contract
#print axioms checked_greater_equal_binding

end UInt256Proof.Compare.Safety
