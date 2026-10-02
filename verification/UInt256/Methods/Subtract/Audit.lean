import UInt256.Methods.Subtract.Correctness
import Tests.SubtractSemantics

namespace UInt256Proof
-- This exact gate cannot be satisfied by a helper or a narrowed aliasing theorem.
theorem checked_subtract_contract : ∀ (initial : UInt256Model.Bytes) (left right out : Nat),
    UInt256Model.SubtractContract Extracted.program Extracted.entryIndex initial left right out := subtract_correct
end UInt256Proof

#print axioms UInt256Proof.checked_subtract_contract
