import UInt256.Methods.Reporting.Contract

open CIL UInt256Model
namespace UInt256Proof.Reporting

/-- A computed return observation refutes the full contract at every fuel. -/
theorem flag_observation_refuted (p : Program) (entry witnessFuel : Nat)
    (operation : Operation) (initial : Bytes) (left right out : Nat) (actual : W32)
    (observed : (invoke p witnessFuel entry [.object left, .object right, .object out]
      (byteMemory initial)).map Prod.snd = some [.i32 actual])
    (different : actual ≠ if flag operation (byteValue initial left)
      (byteValue initial right) then 1 else 0) :
    ¬ Contract operation p entry initial left right out := by
  rintro ⟨fuel, final, normal, _⟩
  have values := invoke_observation_unique p fuel witnessFuel entry
    [.object left, .object right, .object out] (byteMemory initial) Prod.snd
    (final, [.i32 (if flag operation (byteValue initial left) (byteValue initial right) then 1 else 0)])
    [.i32 actual] observed normal
  exact different (Value.i32.inj (List.cons.inj values).1).symm

/-- A computed caller-byte observation also excludes every successful fuel. -/
theorem byte_observation_refuted (p : Program) (entry witnessFuel : Nat)
    (operation : Operation) (initial : Bytes) (left right out address : Nat)
    (actual : Option Value)
    (observed : (invoke p witnessFuel entry [.object left, .object right, .object out]
      (byteMemory initial)).map (fun outcome => outcome.1 (.byte address)) = some actual)
    (different : actual ≠ (writeBytes (byteMemory initial) out
      (result operation (byteValue initial left) (byteValue initial right)).toNat 32) (.byte address)) :
    ¬ Contract operation p entry initial left right out := by
  rintro ⟨fuel, final, normal, memory⟩
  have byte := invoke_observation_unique p fuel witnessFuel entry
    [.object left, .object right, .object out] (byteMemory initial)
    (fun outcome => outcome.1 (.byte address))
    (final, [.i32 (if flag operation (byteValue initial left) (byteValue initial right) then 1 else 0)])
    actual observed normal
  exact different (byte.symm.trans (memory address))

end UInt256Proof.Reporting
