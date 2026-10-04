import UInt256.StorageLemmas
open CIL UInt256Model UInt256Proof
namespace UInt256Proof.Multiply

theorem store4_bytes_of_word_eq (m n : Memory) (out : Nat)
    (r0 r1 r2 r3 s0 s1 s2 s3 : W64)
    (h0 : r0 = s0) (h1 : r1 = s1) (h2 : r2 = s2) (h3 : r3 = s3)
    (bytes : ∀ address, m (.byte address) = n (.byte address)) (address : Nat) :
    store4 m out r0 r1 r2 r3 (.byte address) = store4 n out s0 s1 s2 s3 (.byte address) := by
  cases h0
  cases h1
  cases h2
  cases h3
  exact store4_bytes m n bytes out r0 r1 r2 r3 address

end UInt256Proof.Multiply
