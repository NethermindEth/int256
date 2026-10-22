import UInt256.Methods.Add.CarryHelper
import CIL.Safety.MethodContract

namespace UInt256Proof.Add.CarrySafety
variable {program : CIL.Program} {index : Nat} {body : CIL.Method}

open CIL.Safety

structure CarryInput where
  a : BitVec 64
  b : BitVec 64
  c : BitVec 64
  carryRef : Reference
  output : Reference

/-- The carry helper writes only its carry and output words. Simultaneous readback
    requires disjoint words. -/
def carryContract (program : CIL.Program) : MethodContract CarryInput where
  args i := [.scalar (.i64 i.a), .scalar (.i64 i.b), .reference (.address i.carryRef), .reference (.address i.output)]
  pre i m := m.WellFormed ∧ i.c.toNat ≤ 1 ∧ read m i.carryRef 8 1 = .ok (numberBytes i.c.toNat 8) ∧
    access m i.carryRef 8 1 true = .ok () ∧ access m i.output 8 1 true = .ok () ∧ WordsDisjoint i.carryRef i.output
  footprint i := [(i.carryRef, 8), (i.output, 8)]
  post i before after values := values = [] ∧ CarryPost (program := program) i.a i.b i.c i.carryRef i.output before after

/-- The parent needs only this contract; each extraction proves it from its own helper body. -/
abbrev CarryHelperContract (program : CIL.Program) (index : Nat) : Prop :=
  (carryContract program).Holds program index

/-- A two-local carry body with a proved run and a carry word equal to the
    mathematical carry for incoming carries of at most one. -/
theorem carry_contract_of_run (cw : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64)
    (found : program[index]? = some body) (shape : CarryShape body) (runs : CarryRun program index body cw)
    (correct : ∀ a b c : BitVec 64, c.toNat ≤ 1 → cw a b c = UInt256Proof.carry a b c) :
    CarryHelperContract program index := by
  rintro ⟨a, b, c, carryRef, output⟩ memory ⟨wellFormed, incoming, carryReadable, carryWritable, outputWritable, disjoint⟩
  obtain ⟨fuel, result, invoked, _, _, framed, outputBytes, carryBytes⟩ :=
    carry_invoke_succeeds_of_run cw found shape runs a b c carryRef output memory wellFormed carryReadable
      carryWritable outputWritable
  have carryBytes := carryBytes disjoint
  rw [correct a b c incoming] at carryBytes
  exact ⟨fuel, result, [], invoked, framed, rfl,
    invoke_preserves_wellFormed _ _ _ _ _ _ _ wellFormed invoked,
    outputBytes, carryBytes, UInt256Proof.carry_bound a b c incoming,
    UInt256Proof.carry_word_nat a b c incoming,
    fun world => invoke_preserves_static_world _ _ _ _ _ _ _ wellFormed world invoked⟩

/-- The production helper body satisfies the parent contract at any index that fetches it. -/
theorem carry_helper_contract {profile : CIL.FeatureProfile} (found : program[index]? = some (carryBody profile)) :
    CarryHelperContract program index := by
  rintro ⟨a, b, c, carryRef, output⟩ memory ⟨wellFormed, incoming, carryReadable, carryWritable, outputWritable, disjoint⟩
  obtain ⟨fuel, result, invoked, framed, post⟩ := carry_checked_contract found a b c carryRef output memory
    wellFormed incoming carryReadable carryWritable outputWritable disjoint
  exact ⟨fuel, result, [], invoked, framed, rfl, post⟩

#print axioms carry_contract_of_run
#print axioms carry_helper_contract

end UInt256Proof.Add.CarrySafety
