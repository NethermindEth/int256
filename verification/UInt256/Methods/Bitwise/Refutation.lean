import UInt256.Methods.Bitwise.Contract

open CIL UInt256Model
namespace UInt256Proof.Bitwise

/-- A wrong caller byte refutes the same full contract for all successful fuels. -/
theorem contract_refuted (p : Program) (entry witnessFuel : Nat)
    (operation : UInt256Model.Bitwise.Binary) (initial : Bytes) (left right out address : Nat)
    (observedMemory : Memory)
    (execution : invoke p witnessFuel entry [.object left, .object right, .object out]
      (byteMemory initial) = some (observedMemory, []))
    (different : observedMemory (.byte address) ≠
      (writeBytes (byteMemory initial) out
        (UInt256Model.Bitwise.applyBinary operation (byteValue initial left)
          (byteValue initial right)).toNat 32) (.byte address)) :
    ¬ UInt256Model.Bitwise.Contract p entry operation initial left right out := by
  rintro ⟨fuel, final, normal, memory⟩
  have unique := invoke_result_unique p fuel witnessFuel entry
    [.object left, .object right, .object out] (byteMemory initial)
    (final, []) (observedMemory, []) normal execution
  have memories := congrArg Prod.fst unique
  change final = observedMemory at memories
  subst final
  exact different (memory address)

end UInt256Proof.Bitwise
