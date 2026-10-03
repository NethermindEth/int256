import UInt256.Methods.Reporting.Contract

open CIL UInt256Model
namespace UInt256Proof.Reporting

/-- One successful wrong flag excludes the complete contract at every fuel. -/
theorem flag_contract_refuted (p : Program) (entry witnessFuel : Nat)
    (operation : Operation) (initial : Bytes) (left right out : Nat)
    (observedMemory : Memory) (actual : W32)
    (execution : invoke p witnessFuel entry [.object left, .object right, .object out]
      (byteMemory initial) = some (observedMemory, [.i32 actual]))
    (different : actual ≠ if flag operation (byteValue initial left)
      (byteValue initial right) then 1 else 0) :
    ¬ Contract operation p entry initial left right out := by
  rintro ⟨fuel, final, normal, _⟩
  have unique := invoke_result_unique p fuel witnessFuel entry
    [.object left, .object right, .object out] (byteMemory initial)
    (final, [.i32 (if flag operation (byteValue initial left) (byteValue initial right) then 1 else 0)])
    (observedMemory, [.i32 actual]) normal execution
  have values := congrArg Prod.snd unique
  have words := Value.i32.inj (List.cons.inj values).1
  exact different words.symm

/-- A wrong output or preserved byte also excludes every successful fuel. -/
theorem byte_contract_refuted (p : Program) (entry witnessFuel : Nat)
    (operation : Operation) (initial : Bytes) (left right out address : Nat)
    (observedMemory : Memory) (actual : W32)
    (execution : invoke p witnessFuel entry [.object left, .object right, .object out]
      (byteMemory initial) = some (observedMemory, [.i32 actual]))
    (different : observedMemory (.byte address) ≠
      (writeBytes (byteMemory initial) out
        (result operation (byteValue initial left) (byteValue initial right)).toNat 32) (.byte address)) :
    ¬ Contract operation p entry initial left right out := by
  rintro ⟨fuel, final, normal, memory⟩
  have unique := invoke_result_unique p fuel witnessFuel entry
    [.object left, .object right, .object out] (byteMemory initial)
    (final, [.i32 (if flag operation (byteValue initial left) (byteValue initial right) then 1 else 0)])
    (observedMemory, [.i32 actual]) normal execution
  have memories := congrArg Prod.fst unique
  change final = observedMemory at memories
  subst final
  exact different (memory address)

end UInt256Proof.Reporting
