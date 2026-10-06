import UInt256.Methods.Bitwise.NotReturnSafety
import UInt256.Methods.Bitwise.NotScalarSafetyContract

namespace UInt256Proof.Bitwise.ScalarSafety
open UInt256Model.Safety

theorem not_return_contract : ReadOnlyContract
    (fun values => .v256 (~~~(values[0]?.getD 0))) Extracted.program Extracted.entryIndex 1 :=
  UInt256Proof.Bitwise.NotSafety.return_contract_for scalarIndex not_initialized (by rfl)

#print axioms not_return_contract
end UInt256Proof.Bitwise.ScalarSafety
