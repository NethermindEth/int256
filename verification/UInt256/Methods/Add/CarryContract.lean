import UInt256.Methods.Add.CarryHelper

namespace UInt256Proof.Add.CarrySafety
variable {program : CIL.Program} {index : Nat} {body : CIL.Method}

open CIL.Safety

/-- The parent needs only a checked carry-helper invocation; each extraction proves
    this from its own helper body. Simultaneous readback requires disjoint words. -/
def CarryHelperContract (program : CIL.Program) (index : Nat) : Prop :=
  ∀ (a b c : BitVec 64) (carryRef output : Reference) (memory : Memory),
    memory.WellFormed → c.toNat ≤ 1 →
    read memory carryRef 8 1 = .ok (numberBytes c.toNat 8) →
    access memory carryRef 8 1 true = .ok () →
    access memory output 8 1 true = .ok () →
    WordsDisjoint carryRef output →
    ∃ fuel result,
      invoke program fuel index
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address carryRef), .reference (.address output)]
        memory = .ok (result, []) ∧ CarryPost (program := program) a b c carryRef output memory result

/-- A two-local carry body with a proved run and a carry word equal to the
    mathematical carry for incoming carries of at most one. -/
theorem carry_contract_of_run (cw : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64)
    (found : program[index]? = some body) (shape : CarryShape body) (runs : CarryRun program index body cw)
    (correct : ∀ a b c : BitVec 64, c.toNat ≤ 1 → cw a b c = UInt256Proof.carry a b c) :
    CarryHelperContract program index := by
  intro a b c carryRef output memory wellFormed incoming carryReadable carryWritable outputWritable disjoint
  obtain ⟨fuel, result, invoked, _, _, footprint, retainedAccess, outputBytes, carryBytes⟩ :=
    carry_invoke_succeeds_of_run cw found shape runs a b c carryRef output memory wellFormed carryReadable
      carryWritable outputWritable
  have carryBytes := carryBytes disjoint
  rw [correct a b c incoming] at carryBytes
  exact ⟨fuel, result, invoked,
    ⟨invoke_preserves_wellFormed _ _ _ _ _ _ _ wellFormed invoked,
      outputBytes, carryBytes, UInt256Proof.carry_bound a b c incoming,
      UInt256Proof.carry_word_nat a b c incoming, footprint, retainedAccess,
      fun world => invoke_preserves_static_world _ _ _ _ _ _ _ wellFormed world invoked⟩⟩

/-- The production helper body satisfies the parent contract at any index that fetches it. -/
theorem carry_helper_contract {profile : CIL.FeatureProfile} (found : program[index]? = some (carryBody profile)) :
    CarryHelperContract program index :=
  carry_checked_contract found

#print axioms carry_contract_of_run
#print axioms carry_helper_contract

end UInt256Proof.Add.CarrySafety
