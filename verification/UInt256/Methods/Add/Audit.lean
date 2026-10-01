import UInt256.Methods.Add.Examples

-- This gate deliberately cannot compile until the full, unrestricted public
-- contract is proved. A weaker helper statement cannot satisfy this type.
namespace UInt256Proof
theorem checked_contract : ∀ (initial : UInt256Model.Bytes) (left right out : Nat),
    UInt256Model.Contract Extracted.program Extracted.entryIndex initial left right out := add_correct
end UInt256Proof

-- The final theorem's audit includes its transitive proof dependencies.
#print axioms UInt256Proof.checked_contract
