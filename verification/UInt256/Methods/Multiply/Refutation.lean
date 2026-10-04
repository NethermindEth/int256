import UInt256.Methods.Multiply.Contract
import CIL.ExecutionLemmas
open CIL UInt256Model
namespace UInt256Proof.Multiply

/-- A concrete byte observation excludes the full contract at every successful fuel. -/
theorem byte_observation_refuted (program : Program) (entry witnessFuel : Nat)
    (initial : Bytes) (left right out address : Nat) (actual : Option Value)
    (observed : (invoke program witnessFuel entry [.object left, .object right, .object out]
      (byteMemory initial)).map (fun outcome => outcome.1 (.byte address)) = some actual)
    (different : actual ≠ writeBytes (byteMemory initial) out
      (byteValue initial left * byteValue initial right).toNat 32 (.byte address)) :
    ¬ Contract program entry initial left right out := by
  rintro ⟨fuel, final, normal, bytes⟩
  have byte := invoke_observation_unique program fuel witnessFuel entry
    [.object left, .object right, .object out] (byteMemory initial)
    (fun outcome => outcome.1 (.byte address)) (final, []) actual observed normal
  exact different (byte.symm.trans (bytes address))

end UInt256Proof.Multiply
