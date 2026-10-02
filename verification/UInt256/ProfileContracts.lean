import CIL.ProfileEquivalence
import UInt256.Methods.Add.Contract
import UInt256.Methods.Subtract.Contract

open CIL UInt256Model

namespace UInt256Proof

/-- Execution equivalence transports the entire public contract, including
    termination and the exact caller-memory postcondition. -/
theorem add_contract_profiles (program : Program) (p q : FeatureProfile)
    (hp : p.Valid) (hq : q.Valid) (family : p.classify = q.classify)
    (uniform : ∀ body ∈ program, body.profile = q)
    (classified : program.Classified q.classify)
    (entry : Nat) (initial : Bytes) (left right out : Nat) :
    Contract program entry initial left right out ↔
      Contract (reprofile program p) entry initial left right out := by
  unfold Contract
  simp only [← invoke_same_family_eq program p q hp hq family uniform classified]

theorem subtract_contract_profiles (program : Program) (p q : FeatureProfile)
    (hp : p.Valid) (hq : q.Valid) (family : p.classify = q.classify)
    (uniform : ∀ body ∈ program, body.profile = q)
    (classified : program.Classified q.classify)
    (entry : Nat) (initial : Bytes) (left right out : Nat) :
    SubtractContract program entry initial left right out ↔
      SubtractContract (reprofile program p) entry initial left right out := by
  unfold SubtractContract
  simp only [← invoke_same_family_eq program p q hp hq family uniform classified]

end UInt256Proof
