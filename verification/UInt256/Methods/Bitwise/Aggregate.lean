import CIL.AggregateMemory
import CIL.MemoryLemmas
import UInt256.Representation

open CIL UInt256Model
namespace UInt256Proof.Bitwise

theorem aggregate_fourWrites (m : Memory) (frame kind index : Nat) (r0 r1 r2 r3 : W64) :
 readAggregate (writeHomeBytes (writeHomeBytes (writeHomeBytes (writeHomeBytes m
 frame kind index 0 r0.toNat 8) frame kind index 8 r1.toNat 8)
 frame kind index 16 r2.toNat 8) frame kind index 24 r3.toNat 8) frame kind index =
 some (.v256 (value (fun i => if i=0 then r0 else if i=1 then r1 else if i=2 then r2 else r3))) := by
  exact readAggregate_storeHomeWords m frame kind index r0 r1 r2 r3

/-- Check output arithmetic before comparing expanded byte-memory functions. -/
theorem writeBytes_equal (m n : Memory) (base left right count : Nat)
    (words : left = right) (bytes : ∀ address, m (.byte address) = n (.byte address)) :
    ∀ address, writeBytes m base left count (.byte address) =
      writeBytes n base right count (.byte address) := by
  rw [words]
  exact writeBytes_congr m n bytes base right count
end UInt256Proof.Bitwise
