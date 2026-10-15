import UInt256.Methods.Compare.ScalarSafetyContract
import UInt256.Methods.Compare.WrapperSafetyContract
import UInt256.Safety.ProfileContracts

namespace UInt256Proof.Compare.Safety
open UInt256Model.Safety

/-- Bind the discovered comparison chain to the extracted public entry and the
independent unsigned ordering of its two initial inputs. -/
theorem checked_greater_contract :
    ReadOnlyContract
      (fun values => .i32 (if (values[1]?.getD 0).toNat < (values[0]?.getD 0).toNat then 1 else 0))
      Extracted.program Extracted.entryIndex 2 := by
  have entry : BinaryReadOnlyInvocation (fun left right => lessValue right left) Extracted.program Extracted.entryIndex :=
    entry_checked scalar_checked
  simpa only [lessValue] using entry.to_contract

theorem checked_greater_binding :
    ReadOnlyContract
      (fun values => .i32 (if (values[1]?.getD 0).toNat < (values[0]?.getD 0).toNat then 1 else 0))
      Extracted.program Extracted.entryIndex 2 := checked_greater_contract

#print axioms checked_greater_contract
#print axioms checked_greater_binding

end UInt256Proof.Compare.Safety
