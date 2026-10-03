import UInt256.Methods.Shift.OperatorContract
import CIL.ExecutionLemmas
open CIL UInt256Model
namespace UInt256Proof.Shift
/-- Successful execution with one incorrect caller byte refutes the entire
    public contract, independently of its existential choice of fuel. -/
theorem contract_refuted (program : Program) (entry witnessFuel : Nat)
    (direction : Direction) (initial : Bytes) (input out : Nat) (count : W32)
    (observedMemory : Memory) (returned : List Value) (address : Nat)
    (execution : invoke program witnessFuel entry
      [.object input, .i32 count, .object out] (byteMemory initial) =
      some (observedMemory, returned))
    (different : observedMemory (.byte address) ≠
      writeBytes (byteMemory initial) out (result direction (byteValue initial input) count).toNat 32
        (.byte address)) :
    ¬ Contract direction program entry initial input out count := by
  rintro ⟨fuel, final, normal, bytes⟩
  have unique := invoke_result_unique program fuel witnessFuel entry
    [.object input, .i32 count, .object out] (byteMemory initial)
    (final, []) (observedMemory, returned) normal execution
  have memory := congrArg Prod.fst unique
  change final = observedMemory at memory
  have correct := bytes address
  rw [memory] at correct
  exact different correct
theorem operator_contract_refuted (program : Program) (entry witnessFuel : Nat)
    (direction : Direction) (initial : Bytes) (input : Nat) (count : W32)
    (observedMemory : Memory) (actual : BitVec 256)
    (execution : invoke program witnessFuel entry [.object input, .i32 count] (byteMemory initial) =
      some (observedMemory, [.v256 actual]))
    (different : actual ≠ result direction (byteValue initial input) count) :
    ¬ OperatorContract direction program entry initial input count := by
  rintro ⟨fuel, final, normal, _⟩
  have unique := invoke_result_unique program fuel witnessFuel entry
    [.object input, .i32 count] (byteMemory initial)
    (final, [.v256 (result direction (byteValue initial input) count)])
    (observedMemory, [.v256 actual]) normal execution
  have returned := congrArg Prod.snd unique
  have bits := Value.v256.inj (List.cons.inj returned).1
  exact different bits.symm

end UInt256Proof.Shift
#print axioms UInt256Proof.Shift.contract_refuted
