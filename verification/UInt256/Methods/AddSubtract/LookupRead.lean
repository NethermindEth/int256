import UInt256.Methods.AddSubtract.LookupSafety
import UInt256.LookupTable

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety

/-- Kernel-check every entry against the actual extracted descriptor bytes. -/
theorem lookup_table_values : ∀ index : Fin 16,
    byteNumber ((lookupDescriptor.bytes.drop (32 * index.val)).take 32) =
      (UInt256Proof.SIMD.cascadeVector (BitVec.ofNat 32 index.val)).toNat := by decide +kernel

/-- Provenance, readable extent and exact table contents justify the actual
    native offset and complete 32-byte vector load. -/
theorem lookup_vector_read (memory : Memory) (reference : Reference) (index : BitVec 32)
    (wellFormed : memory.WellFormed) (valid : StaticBindingValid memory lookupDescriptor reference)
    (bound : index.toNat < 16) :
    add memory reference 32 (BitVec.ofNat 64 index.toNat) =
      .ok { reference with offset := reference.offset + 32 * index.toNat } ∧
    loadValue memory (.address { reference with offset := reference.offset + 32 * index.toNat }) 32 =
      .ok (.v256 (UInt256Proof.SIMD.cascadeVector index)) := by
  obtain ⟨_, _, _, _, _, _, loaded⟩ := valid
  have within : 32 * index.toNat + 32 ≤ lookupDescriptor.bytes.length := by
    rw [lookup_descriptor_length]
    omega
  have reading := read_slice_bytes wellFormed loaded (32 * index.toNat) 32 (by decide) within
  have allowed : access memory reference lookupDescriptor.bytes.length 1 false = .ok () := by
    unfold CIL.Safety.read at loaded
    cases h : access memory reference lookupDescriptor.bytes.length 1 false with
    | error fault => simp [h, Bind.bind, Except.bind] at loaded
    | ok unit => cases unit; rfl
  obtain ⟨allocation, ready⟩ := access_requirements allowed
  refine ⟨ready.add_slice wellFormed 32 index.toNat 32 (by decide) within, ?_⟩
  have bytes := lookup_table_values ⟨index.toNat, bound⟩
  simp only [BitVec.ofNat_toNat] at bytes
  simp [loadValue, dereference, reading, bytes, checkedAt, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms lookup_table_values
#print axioms lookup_vector_read
end UInt256Proof.AddSubtract.Safety
