import UInt256.Methods.Equality.Contract

open CIL UInt256Model
namespace UInt256Proof.Equality

/-- One successful wrong return refutes the full contract at every possible fuel. -/
theorem result_contract_refuted (p : Program) (entry witnessFuel : Nat)
    (args : List Value) (initial : Bytes) (expected : Bool) (actual : W32)
    (observedMemory : Memory)
    (execution : invoke p witnessFuel entry args (byteMemory initial) =
      some (observedMemory, [.i32 actual]))
    (different : actual ≠ UInt256Model.Equality.booleanWord expected) :
    ¬ UInt256Model.Equality.ResultContract p entry args initial expected := by
  rintro ⟨fuel, final, normal, _⟩
  have unique := invoke_result_unique p fuel witnessFuel entry args (byteMemory initial)
    (final, [.i32 (UInt256Model.Equality.booleanWord expected)])
    (observedMemory, [.i32 actual]) normal execution
  have values := congrArg Prod.snd unique
  have words := Value.i32.inj (List.cons.inj values).1
  exact different words.symm

end UInt256Proof.Equality
