import UInt256.Methods.Equality.ConstructorSafety
import UInt256.Safety.OutputLoad

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

/-- Safety and the mathematical output describe the same extracted invocation. -/
theorem constructor_contract (memory : Memory) (inputs : List Reference) (output : Reference)
    (w0 w1 w2 w3 : BitVec 64)
    (call : CallingConditions Extracted.program memory inputs [output]) :
    ∃ fuel result,
      invoke Extracted.program fuel constructorIndex
        [.reference (.address output), .scalar (.i64 w0), .scalar (.i64 w1), .scalar (.i64 w2), .scalar (.i64 w3)]
        memory = .ok (result, []) ∧
      CallingConditions Extracted.program result inputs [output] ∧
      (∀ id offset, OutsideOutput output id offset → result.cells id offset = memory.cells id offset) ∧
      AccessBelow memory.nextIdentity memory result ∧
      inputValue result output = BitVec.ofNat 256
        (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192) ∧
      loadValue result (.address output) 32 = .ok (.v256 (BitVec.ofNat 256
        (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192))) := by
  obtain ⟨fuel, result, executed, valid, outside, authority, r0, r1, r2, r3⟩ :=
    constructor_safe memory inputs output w0 w1 w2 w3 call
  exact ⟨fuel, result, executed, valid, outside, authority,
    output_value_of_limb_reads result output w0 w1 w2 w3 r0 r1 r2 r3,
    output_load_of_limb_reads result output w0 w1 w2 w3
      (valid.1.2.2 (wordView output) (by simp)) r0 r1 r2 r3⟩

#print axioms constructor_contract

end UInt256Proof.Equality.Safety
