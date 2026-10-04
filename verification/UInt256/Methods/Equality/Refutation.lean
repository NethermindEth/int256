import UInt256.Methods.Equality.Contract

open CIL UInt256Model
namespace UInt256Proof.Equality

/-- A mapped return witness refutes the full contract at every fuel. -/
theorem result_observation_refuted (p : Program) (entry witnessFuel : Nat)
    (args : List Value) (initial : Bytes) (expected : Bool) (actual : W32)
    (observed : (invoke p witnessFuel entry args (byteMemory initial)).map Prod.snd =
      some [.i32 actual])
    (different : actual ≠ UInt256Model.Equality.booleanWord expected) :
    ¬ UInt256Model.Equality.ResultContract p entry args initial expected := by
  rintro ⟨fuel, final, normal, _⟩
  have values := invoke_observation_unique p fuel witnessFuel entry args (byteMemory initial)
    Prod.snd (final, [.i32 (UInt256Model.Equality.booleanWord expected)])
    [.i32 actual] observed normal
  exact different (Value.i32.inj (List.cons.inj values).1).symm

end UInt256Proof.Equality
