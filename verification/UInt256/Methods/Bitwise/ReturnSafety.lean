import Extracted
import UInt256.Safety.BinaryReturn

namespace UInt256Proof.Bitwise.Safety
open CIL.Safety UInt256Model.Safety

variable (operation : BitVec 256 → BitVec 256 → BitVec 256) (binaryIndex : Nat)
    (child : InitializedBinaryContract operation Extracted.program binaryIndex)
    (fetched : Extracted.entryBody.code[3]? = some (.call binaryIndex 3))

include child fetched

omit child in
private theorem return_code : Extracted.entryBody.code =
    [.arg 0, .arg 1, .aggregateLocalAddr 0, .call binaryIndex 3, .aggregateLocal 0, .ret] := by
  simp only [cil_code] at fetched
  cases fetched
  rfl

theorem return_checked_for : BinaryReadOnlyInvocation
    (fun left right => .v256 (operation left right)) Extracted.program Extracted.entryIndex :=
  binary_return_checked Extracted.program Extracted.entryIndex Extracted.entryBody operation binaryIndex child
    (by rfl) (return_code binaryIndex fetched) (by rfl) (by rfl) (by rfl) (by rfl)

theorem return_contract_for : ReadOnlyContract
    (fun values => .v256 (operation (values[0]?.getD 0) (values[1]?.getD 0)))
      Extracted.program Extracted.entryIndex 2 :=
  binary_return_contract Extracted.program Extracted.entryIndex Extracted.entryBody operation binaryIndex child
    (by rfl) (return_code binaryIndex fetched) (by rfl) (by rfl) (by rfl) (by rfl)

#print axioms return_contract_for
#print axioms return_checked_for
end UInt256Proof.Bitwise.Safety
