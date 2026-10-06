import UInt256.Methods.Add.VectorStorageContract
import UInt256.Safety.OutputReadability

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

/-- Safety and the mathematical output describe the same extracted invocation. -/
theorem store_limbs_readable_contract (memory : Memory) (inputs : List Reference) (output : Reference)
    (w0 w1 w2 w3 : BitVec 64)
    (call : CallingConditions Extracted.program memory inputs [output]) :
    ∃ fuel result,
      invoke Extracted.program fuel storageIndex
        (storageArguments output w0 w1 w2 w3)
        memory = .ok (result, []) ∧
      CallingConditions Extracted.program result inputs [output] ∧
      (∀ id offset, OutsideOutput output id offset → result.cells id offset = memory.cells id offset) ∧
      AccessBelow memory.nextIdentity memory result ∧
      inputValue result output = BitVec.ofNat 256
        (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192) ∧
      (∃ bytes, read result output 32 1 = .ok bytes) := by
  first
  | exact vector_store_limbs_readable_contract memory inputs output w0 w1 w2 w3 call (by rfl)
  |
    obtain ⟨fuel, result, executed, valid, outside, authority, r0, r1, r2, r3⟩ :=
      store_limbs_safe memory inputs output w0 w1 w2 w3 call (by rfl)
    refine ⟨fuel, result, executed, valid, outside, authority,
      output_value_of_limb_reads result output w0 w1 w2 w3 r0 r1 r2 r3, ?_⟩
    apply output_readable_of_limbs result output (valid.1.2.2 (wordView output) (by simp))
    intro i
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · exact ⟨_, by simpa using r0⟩
    · exact ⟨_, r1⟩
    · exact ⟨_, r2⟩
    · exact ⟨_, r3⟩

theorem store_limbs_contract (memory : Memory) (inputs : List Reference) (output : Reference)
    (w0 w1 w2 w3 : BitVec 64)
    (call : CallingConditions Extracted.program memory inputs [output]) :
    ∃ fuel result,
      invoke Extracted.program fuel storageIndex
        (storageArguments output w0 w1 w2 w3)
        memory = .ok (result, []) ∧
      CallingConditions Extracted.program result inputs [output] ∧
      (∀ id offset, OutsideOutput output id offset → result.cells id offset = memory.cells id offset) ∧
      AccessBelow memory.nextIdentity memory result ∧
      inputValue result output = BitVec.ofNat 256
        (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192) := by
  obtain ⟨fuel, result, executed, valid, outside, authority, value, _⟩ :=
    store_limbs_readable_contract memory inputs output w0 w1 w2 w3 call
  exact ⟨fuel, result, executed, valid, outside, authority, value⟩

#print axioms store_limbs_readable_contract
#print axioms store_limbs_contract

end UInt256Proof.Safety
