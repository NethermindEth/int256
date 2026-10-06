import UInt256.Methods.Add.CarryInvoke
import UInt256.Methods.Add.CarryResult
import CIL.Safety.ExecutionStaticWorld

namespace UInt256Proof.Safety

open CIL.Safety

/-- Independent arithmetic, actual byte readbacks, and retained caller storage. -/
structure CarryPost (a b c : BitVec 64) (carryRef output : Reference) (before after : Memory) : Prop where
  wellFormed : after.WellFormed
  outputBytes : read after output 8 1 = .ok (numberBytes (a + b + c).toNat 8)
  carryBytes : read after carryRef 8 1 = .ok (numberBytes (UInt256Proof.carry a b c).toNat 8)
  carryBound : (UInt256Proof.carry a b c).toNat ≤ 1
  arithmetic : (a + b + c).toNat + 2^64 * (UInt256Proof.carry a b c).toNat = a.toNat + b.toNat + c.toNat
  footprint : ∀ id offset, id < before.nextIdentity → OutsideWord carryRef id offset → OutsideWord output id offset →
    after.cells id offset = before.cells id offset
  access : AccessBelow before.nextIdentity before after
  staticWorld : StaticWorldValid (programStaticDescriptors Extracted.program) before →
    StaticWorldValid (programStaticDescriptors Extracted.program) after

theorem CarryPost.output_load {a b c : BitVec 64} {carryRef output : Reference} {before after : Memory}
    (post : CarryPost a b c carryRef output before after) :
    loadValue after (.address output) 8 = .ok (.i64 (a + b + c)) := load_word64_of_read post.outputBytes

theorem CarryPost.carry_load {a b c : BitVec 64} {carryRef output : Reference} {before after : Memory}
    (post : CarryPost a b c carryRef output before after) :
    loadValue after (.address carryRef) 8 = .ok (.i64 (UInt256Proof.carry a b c)) := load_word64_of_read post.carryBytes

/-- Simultaneous carry/result readback requires nonoverlapping output words. -/
theorem carry_checked_contract (a b c : BitVec 64) (carryRef output : Reference) (memory : Memory)
    (wellFormed : memory.WellFormed) (incoming : c.toNat ≤ 1)
    (carryReadable : read memory carryRef 8 1 = .ok (numberBytes c.toNat 8))
    (carryWritable : access memory carryRef 8 1 true = .ok ())
    (outputWritable : access memory output 8 1 true = .ok ())
    (disjoint : WordsDisjoint carryRef output) :
    ∃ fuel result,
      invoke Extracted.program fuel Extracted.addWithCarryIndex
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address carryRef), .reference (.address output)]
        memory = .ok (result, []) ∧ CarryPost a b c carryRef output memory result := by
  obtain ⟨fuel, result, invoked, _, _, footprint, retainedAccess, outputBytes, carryBytes⟩ :=
    carry_invoke_succeeds a b c carryRef output memory wellFormed carryReadable carryWritable outputWritable
  have carryBytes := carryBytes disjoint
  rw [carryWord_correct a b c incoming] at carryBytes
  exact ⟨fuel, result, invoked,
    ⟨invoke_preserves_wellFormed _ _ _ _ _ _ _ wellFormed invoked,
      outputBytes, carryBytes, UInt256Proof.carry_bound a b c incoming,
      UInt256Proof.carry_word_nat a b c incoming, footprint, retainedAccess,
      fun world => invoke_preserves_static_world _ _ _ _ _ _ _ wellFormed world invoked⟩⟩

#print axioms CarryPost.output_load
#print axioms CarryPost.carry_load
#print axioms carry_checked_contract

end UInt256Proof.Safety
