import UInt256.Arithmetic.SignMasks
import UInt256.Arithmetic.RippleMasks
import UInt256.Arithmetic.CascadeVectors
import UInt256.LookupTable
import UInt256.ProfileContracts

open CIL UInt256Proof UInt256Proof.SIMD

-- A carry/borrow generated in lane zero propagates across both middle lanes.
example : cascadeIndex 1 6 = 14 := by decide
example : incomingMask 1 6 = 14 := by decide
example : finalCarry 1 14 = true := by decide
example : cascadeIndex 0 15 = 0 := by decide

-- The disjointness premise is essential: these masks do not obey the recurrence.
example : cascadeIndex 3 2 ≠ incomingMask 3 2 := by decide

example : ¬ LookupValid [] := by
  intro h
  have impossible := h 0
  contradiction

#print axioms packed_cascade
#print axioms read_lookup
#print axioms readStaticBytes_sequential
#print axioms ternary_carry_mask
#print axioms ternary_borrow_mask
#print axioms carry_generated_propagated
#print axioms borrow_generated_propagated
#print axioms cascade_flags
#print axioms add_cascade_words
#print axioms subtract_cascade_words
#print axioms add_cascade_vector
#print axioms subtract_cascade_vector
#print axioms add_contract_profiles
#print axioms subtract_contract_profiles
