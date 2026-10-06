import UInt256.Methods.Bitwise.ReturnSafety
import UInt256.Methods.Bitwise.VectorEntrySafety

namespace UInt256Proof.Bitwise.Safety
open UInt256Model.Safety

theorem return_contract : ReadOnlyContract
    (fun values => .v256 (UInt256Model.Bitwise.applyBinary vectorOperation
      (values[0]?.getD 0) (values[1]?.getD 0))) Extracted.program Extracted.entryIndex 2 :=
  UInt256Proof.Bitwise.Safety.return_contract_for
    (UInt256Model.Bitwise.applyBinary vectorOperation) binaryIndex vector_entry_initialized (by rfl)

#print axioms return_contract
end UInt256Proof.Bitwise.Safety
