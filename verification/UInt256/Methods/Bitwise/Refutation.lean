import UInt256.Methods.Bitwise.Contract

open CIL UInt256Model
namespace UInt256Proof.Bitwise

/-- A returned-value witness refutes arithmetic even when every caller byte is preserved. -/
theorem return_observation_refuted (p : Program) (entry witnessFuel : Nat)
    (operation : UInt256Model.Bitwise.Binary) (initial : Bytes) (left right : Nat)
    (actual : List Value)
    (observed : (invoke p witnessFuel entry [.object left,.object right] (byteMemory initial)).map
      Prod.snd = some actual)
    (different : actual ≠ [.v256 (UInt256Model.Bitwise.applyBinary operation
      (byteValue initial left) (byteValue initial right))]) :
    ¬UInt256Model.Bitwise.ReturnContract p entry operation initial left right := by
  rintro ⟨fuel,final,execution,_⟩
  have observation := invoke_observation_unique p fuel witnessFuel entry
    [.object left,.object right] (byteMemory initial) Prod.snd
    (final,[.v256 (UInt256Model.Bitwise.applyBinary operation
      (byteValue initial left) (byteValue initial right))]) actual observed execution
  exact different observation.symm

/-- A mapped caller-byte witness refutes the full contract at every fuel. -/
theorem byte_observation_refuted (p : Program) (entry witnessFuel : Nat)
    (operation : UInt256Model.Bitwise.Binary) (initial : Bytes) (left right out address : Nat)
    (actual : Option Value)
    (observed : (invoke p witnessFuel entry [.object left, .object right, .object out]
      (byteMemory initial)).map (fun outcome => (outcome.2, outcome.1 (.byte address))) =
      some ([], actual))
    (different : actual ≠ (writeBytes (byteMemory initial) out
      (UInt256Model.Bitwise.applyBinary operation (byteValue initial left)
        (byteValue initial right)).toNat 32) (.byte address)) :
    ¬ UInt256Model.Bitwise.Contract p entry operation initial left right out := by
  rintro ⟨fuel, final, normal, memory⟩
  have observation := invoke_observation_unique p fuel witnessFuel entry
    [.object left, .object right, .object out] (byteMemory initial)
    (fun outcome => (outcome.2, outcome.1 (.byte address))) (final, [])
    ([], actual) observed normal
  exact different ((congrArg Prod.snd observation).symm.trans (memory address))

theorem not_return_observation_refuted (p : Program) (entry witnessFuel : Nat)
    (initial : Bytes) (input : Nat) (actual : List Value)
    (observed : (invoke p witnessFuel entry [.object input] (byteMemory initial)).map
      Prod.snd = some actual)
    (different : actual ≠ [.v256 (~~~byteValue initial input)]) :
    ¬UInt256Model.Bitwise.NotReturnContract p entry initial input := by
  rintro ⟨fuel,final,execution,_⟩
  have observation := invoke_observation_unique p fuel witnessFuel entry
    [.object input] (byteMemory initial) Prod.snd
    (final,[.v256 (~~~byteValue initial input)]) actual observed execution
  exact different observation.symm

end UInt256Proof.Bitwise
