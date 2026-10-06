import UInt256.Methods.Bitwise.NotReturnSafety
import UInt256.Methods.Bitwise.NotEntrySafety

namespace UInt256Proof.Bitwise.NotSafety
open UInt256Model.Safety

theorem return_contract : ReadOnlyContract
    (fun values => .v256 (~~~(values[0]?.getD 0))) Extracted.program Extracted.entryIndex 1 :=
  UInt256Proof.Bitwise.NotSafety.return_contract_for unaryIndex vector_entry_initialized (by rfl)

#print axioms return_contract
end UInt256Proof.Bitwise.NotSafety
