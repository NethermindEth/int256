import UInt256.RepresentationLemmas

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof

def store4 (m : Memory) (out : Nat) (r0 r1 r2 r3 : W64) : Memory :=
  writeBytes (writeBytes (writeBytes (writeBytes m out r0.toNat 8)
    (out + 8) r1.toNat 8) (out + 16) r2.toNat 8) (out + 24) r3.toNat 8

@[simp] theorem store4_local (m : Memory) (out frame index : Nat) (r0 r1 r2 r3 : W64) :
    store4 m out r0 r1 r2 r3 (.local frame index) = m (.local frame index) := by
  simp [store4]
theorem store4_value (m : Memory) (out : Nat) (r0 r1 r2 r3 : W64) :
    store4 m out r0 r1 r2 r3 = writeBytes m out
      (value (fun i => if i.val = 0 then r0 else if i.val = 1 then r1 else
        if i.val = 2 then r2 else r3)).toNat 32 := by
  let word := r0.toNat + r1.toNat * 2^64 + r2.toNat * 2^128 + r3.toNat * 2^192
  have h0 := r0.isLt
  have h1 := r1.isLt
  have h2 := r2.isLt
  have h3 := r3.isLt
  have p0 : word % 2^64 = r0.toNat := by dsimp [word]; omega
  have p1 : word / 2^64 % 2^64 = r1.toNat := by dsimp [word]; omega
  have p2 : word / 2^64 / 2^64 % 2^64 = r2.toNat := by dsimp [word]; omega
  have p3 : word / 2^64 / 2^64 / 2^64 % 2^64 = r3.toNat := by dsimp [word]; omega
  have pow8 : (256 : Nat)^8 = 2^64 := by decide
  have pow32 : (256 : Nat)^32 = 2^256 := by decide
  simp only [value, BitVec.toNat_ofNat,
    show (0 : Fin 4).val = 0 from rfl, show (1 : Fin 4).val = 1 from rfl,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl, ↓reduceIte]
  change store4 m out r0 r1 r2 r3 = writeBytes m out (word % 2^256) 32
  rw [← pow32, writeBytes_mod]
  rw [writeBytes_append m out word 8 24]
  rw [writeBytes_append _ (out+8) _ 8 16]
  rw [writeBytes_append _ (out+8+8) _ 8 8]
  simp only [pow8]
  rw [← writeBytes_mod m out word 8, pow8, p0]
  rw [← writeBytes_mod _ (out+8) (word / 2^64) 8, pow8, p1]
  rw [← writeBytes_mod _ (out+8+8) (word / 2^64 / 2^64) 8, pow8, p2]
  rw [← writeBytes_mod _ (out+8+8+8) (word / 2^64 / 2^64 / 2^64) 8, pow8, p3]
  simp only [store4, Nat.add_assoc]
theorem store4_bytes (m n : Memory)
    (h : ∀ address, m (.byte address) = n (.byte address)) (out : Nat)
    (r0 r1 r2 r3 : W64) :
    ∀ address, store4 m out r0 r1 r2 r3 (.byte address) =
      store4 n out r0 r1 r2 r3 (.byte address) := by
  simp only [store4_value]
  exact writeBytes_congr m n h _ _ _

end UInt256Proof
