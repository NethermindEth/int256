import UInt256.Methods.Subtract.BorrowHelper
import CIL.Safety.MethodContract

namespace UInt256Proof.Subtract.Profile
variable {program : CIL.Program} {index : Nat} {body : CIL.Method}

open CIL.Safety

structure BorrowInput where
  a : BitVec 64
  b : BitVec 64
  c : BitVec 64
  borrowRef : Reference
  output : Reference

/-- The borrow helper writes only its borrow and output words, which must be disjoint. -/
def borrowContract : MethodContract BorrowInput Unit where
  args i := [.scalar (.i64 i.a), .scalar (.i64 i.b), .reference (.address i.borrowRef), .reference (.address i.output)]
  pre i m := m.WellFormed ∧ i.c.toNat ≤ 1 ∧ read m i.borrowRef 8 1 = .ok (numberBytes i.c.toNat 8) ∧
    access m i.borrowRef 8 1 true = .ok () ∧ access m i.output 8 1 true = .ok () ∧ WordsDisjoint i.borrowRef i.output
  results _ := []
  footprint i := [(i.borrowRef, 8), (i.output, 8)]
  post i _ after _ := BorrowPost i.a i.b i.c i.borrowRef i.output after

/-- The parent needs only this contract; each extraction proves it from its own helper body. -/
abbrev BorrowHelperContract (program : CIL.Program) (index : Nat) : Prop :=
  borrowContract.Holds program index

/-- Any frameless body whose run writes the mathematical borrow for incoming borrows of at most one. -/
theorem borrow_contract_of_run (bw : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64)
    (found : program[index]? = some body) (shape : BorrowShape body) (runs : BorrowRun program index body bw)
    (correct : ∀ a b c : BitVec 64, c.toNat ≤ 1 → bw a b c = UInt256Proof.borrow a b c) :
    BorrowHelperContract program index := by
  rintro ⟨a, b, c, borrowRef, output⟩ memory ⟨_, incoming, readable, writable, outputWritable, disjoint⟩
  obtain ⟨fuel, final, invoked, framed, outputBytes, borrowBytes⟩ :=
    borrow_invoke_succeeds_of_run bw found shape runs a b c borrowRef output memory readable writable
      outputWritable disjoint
  rw [correct a b c incoming] at borrowBytes
  exact ⟨fuel, final, [], invoked, framed, (), rfl, outputBytes, borrowBytes,
    UInt256Proof.borrow_bound a b c, UInt256Proof.borrow_word_nat a b c incoming⟩

/-- The production helper body satisfies the parent contract at any index that fetches it. -/
theorem borrow_helper_contract {profile : CIL.FeatureProfile} (found : program[index]? = some (borrowBody profile)) :
    BorrowHelperContract program index :=
  borrow_contract_of_run borrowWord found borrowBody_shape (borrow_run_of_memory_steps found) borrowWord_correct

#print axioms borrow_contract_of_run
#print axioms borrow_helper_contract

end UInt256Proof.Subtract.Profile
