import UInt256.Methods.Add.Examples

-- This gate deliberately cannot compile until the full, unrestricted public
-- contract is proved. A weaker helper statement cannot satisfy this type.
namespace UInt256Proof
theorem checked_contract : ∀ (initial : UInt256Model.Bytes) (left right out : Nat),
    UInt256Model.Contract Extracted.program initial left right out := add_correct
end UInt256Proof

namespace UInt256Proof
#print axioms execute_store
#print axioms execute_carry
#print axioms carry_nat
#print axioms carry_bound
#print axioms carry_word_nat
#print axioms telescope
#print axioms mod_total
#print axioms four_limb_sum
#print axioms representation_injective
#print axioms value_decode
#print axioms read_initial
#print axioms byteNumber_bound
#print axioms writeBytes_outside
#print axioms readBytes_congr
#print axioms readBytes_write_local
#print axioms initLocals_bytes
#print axioms readBytes_initLocals
#print axioms byteNumber_append
#print axioms input_limb_nat
#print axioms read64_initial
#print axioms input_value
#print axioms writeBytes_append
#print axioms writeBytes_mod
#print axioms store4_value
#print axioms writeBytes_congr
#print axioms store4_bytes
#print axioms execute_store_result
#print axioms writeBytes_write_local
#print axioms execute_small_no_carry
#print axioms execute_small_carry1
#print axioms execute_small_carry2
#print axioms execute_small_carry3
#print axioms execute_small_overflow
#print axioms increment_lt
#print axioms small_result_sum
#print axioms execute_small
#print axioms execute_scalar_right_small
#print axioms execute_scalar_left_small
#print axioms execute_carry_at
#print axioms execute_entry
#print axioms execute_parent_carry
#print axioms execute_scalar_general
#print axioms execute_scalar
#print axioms add_correct
end UInt256Proof

#print axioms UInt256Proof.checked_contract
