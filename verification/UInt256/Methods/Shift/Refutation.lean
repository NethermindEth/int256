import UInt256.Methods.Shift.OperatorContract
import CIL.ExecutionLemmas
open CIL UInt256Model
namespace UInt256Proof.Shift

/-- A mapped byte witness excludes the complete contract at every fuel. -/
theorem byte_observation_refuted (program : Program) (entry witnessFuel : Nat)
    (direction : Direction) (initial : Bytes) (input out : Nat) (count : W32)
    (address : Nat) (actual : Option Value)
    (observed : (invoke program witnessFuel entry [.object input, .i32 count, .object out]
      (byteMemory initial)).map (fun outcome => outcome.1 (.byte address)) = some actual)
    (different : actual ≠ writeBytes (byteMemory initial) out
      (result direction (byteValue initial input) count).toNat 32 (.byte address)) :
    ¬ Contract direction program entry initial input out count := by
  rintro ⟨fuel, final, normal, bytes⟩
  have byte := invoke_observation_unique program fuel witnessFuel entry
    [.object input, .i32 count, .object out] (byteMemory initial)
    (fun outcome => outcome.1 (.byte address)) (final, []) actual observed normal
  exact different (byte.symm.trans (bytes address))

theorem operator_observation_refuted (program : Program) (entry witnessFuel : Nat)
    (direction : Direction) (initial : Bytes) (input : Nat) (count : W32)
    (actual : BitVec 256)
    (observed : (invoke program witnessFuel entry [.object input, .i32 count]
      (byteMemory initial)).map Prod.snd = some [.v256 actual])
    (different : actual ≠ result direction (byteValue initial input) count) :
    ¬ OperatorContract direction program entry initial input count := by
  rintro ⟨fuel, final, normal, _⟩
  have values := invoke_observation_unique program fuel witnessFuel entry
    [.object input, .i32 count] (byteMemory initial) Prod.snd
    (final, [.v256 (result direction (byteValue initial input) count)])
    [.v256 actual] observed normal
  exact different (Value.v256.inj (List.cons.inj values).1).symm

end UInt256Proof.Shift
#print axioms UInt256Proof.Shift.byte_observation_refuted
