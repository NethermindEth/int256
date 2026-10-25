import UInt256.Methods.Compare.PortableSafetyContract
import UInt256.Methods.Compare.WrapperSafetyContract
import UInt256.Safety.ProfileContracts

namespace UInt256Proof.Compare.Safety
open UInt256Model.Safety

/-- Bind the discovered comparison chain to the extracted public entry and the
independent unsigned ordering of its two initial inputs. -/
theorem checked_less_contract :
    ReadOnlyContract
      (fun values => .i32 (if (values[0]?.getD 0).toNat < (values[1]?.getD 0).toNat then 1 else 0))
      Extracted.program Extracted.entryIndex 2 := by
  have entry : BinaryReadOnlyInvocation lessValue Extracted.program Extracted.entryIndex :=
    entry_checked (portable_checked Extracted.profile Extracted.program wrapperLeafIndex (wrapperLeafIndex + 1) rfl rfl)
  simpa only [lessValue] using entry.to_contract

theorem checked_less_binding :
    ReadOnlyContract
      (fun values => .i32 (if (values[0]?.getD 0).toNat < (values[1]?.getD 0).toNat then 1 else 0))
      Extracted.program Extracted.entryIndex 2 := checked_less_contract

#print axioms checked_less_contract
#print axioms checked_less_binding

end UInt256Proof.Compare.Safety
