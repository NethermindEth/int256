import UInt256.Safety.ContractRefutation
import UInt256.Safety.ReadOnlyContract
import UInt256.Safety.ScalarOperatorContract
import UInt256.Safety.OrderedScalarContract

namespace UInt256Model.Safety.ContractRefutation
open CIL.Safety

/-- One checked observation that differs from the result refutes the read-only contract. -/
theorem checked_readonly_refuted (operation : List (BitVec 256) → CIL.Value)
    (program : CIL.Program) (entry arity observedFuel : Nat)
    (memory : Memory) (inputs : List Reference) (actual : List Value)
    (length : inputs.length = arity) (call : CallingConditions program memory inputs [])
    (observed : (invoke program observedFuel entry (readOnlyArguments inputs) memory).map Prod.snd = .ok actual)
    (different : actual ≠ [.scalar (operation (inputs.map (inputValue memory)))]) :
    ¬ ReadOnlyContract operation program entry arity := by
  intro contract
  obtain ⟨fuel, final, certificate, _⟩ := contract memory inputs length call
  have result := checked_observation_unique program entry observedFuel fuel
    (readOnlyArguments inputs) memory final _ Prod.snd actual observed certificate.1
  exact different result.symm

/-- Reference receiver with a scalar or by-value argument. -/
theorem checked_readonly_scalar_refuted {α : Type} (encode : α → CIL.Value)
    (operation : BitVec 256 → α → CIL.Value) (program : CIL.Program) (entry observedFuel : Nat)
    (memory : Memory) (input : Reference) (scalar : α) (actual : List Value)
    (call : CallingConditions program memory [input] [])
    (observed : (invoke program observedFuel entry (scalarArguments input (encode scalar)) memory).map Prod.snd = .ok actual)
    (different : actual ≠ [.scalar (operation (inputValue memory input) scalar)]) :
    ¬ ReadOnlyScalarContract encode operation program entry := by
  intro contract
  obtain ⟨fuel, final, certificate, _⟩ := contract memory input scalar call
  have result := checked_observation_unique program entry observedFuel fuel
    (scalarArguments input (encode scalar)) memory final _ Prod.snd actual observed certificate.1
  exact different result.symm

/-- Operand order and polarity are fixed by the refuted operator contract. -/
theorem checked_scalar_operator_refuted {α : Type} (scalarFirst negate : Bool)
    (encode : α → CIL.Value) (equal : BitVec 256 → α → Bool)
    (program : CIL.Program) (entry observedFuel : Nat) (memory : Memory)
    (input : Reference) (scalar : α) (actual : List Value)
    (call : CallingConditions program memory [input] [])
    (observed : (invoke program observedFuel entry (scalarOperatorArguments scalarFirst input (encode scalar)) memory).map Prod.snd = .ok actual)
    (different : actual ≠ [.scalar (.i32 (if equal (inputValue memory input) scalar != negate then 1 else 0))]) :
    ¬ ScalarOperatorContract scalarFirst negate encode equal program entry := by
  intro contract
  obtain ⟨fuel, final, certificate, _⟩ := contract memory input scalar call
  have result := checked_observation_unique program entry observedFuel fuel
    (scalarOperatorArguments scalarFirst input (encode scalar)) memory final _ Prod.snd actual observed certificate.1
  exact different result.symm

/-- Ordered primitive comparisons with a declared operand order. -/
theorem checked_ordered_scalar_refuted {α : Type} (scalarFirst : Bool)
    (encode : α → CIL.Value) (operation : BitVec 256 → α → CIL.Value)
    (program : CIL.Program) (entry observedFuel : Nat) (memory : Memory)
    (input : Reference) (scalar : α) (actual : List Value)
    (call : CallingConditions program memory [input] [])
    (observed : (invoke program observedFuel entry (scalarOperatorArguments scalarFirst input (encode scalar)) memory).map Prod.snd = .ok actual)
    (different : actual ≠ [.scalar (operation (inputValue memory input) scalar)]) :
    ¬ OrderedScalarContract scalarFirst encode operation program entry := by
  intro contract
  obtain ⟨fuel, final, certificate, _⟩ := contract memory input scalar call
  have result := checked_observation_unique program entry observedFuel fuel
    (scalarOperatorArguments scalarFirst input (encode scalar)) memory final _ Prod.snd actual observed certificate.1
  exact different result.symm

#print axioms checked_readonly_refuted
#print axioms checked_readonly_scalar_refuted
#print axioms checked_scalar_operator_refuted
#print axioms checked_ordered_scalar_refuted
end UInt256Model.Safety.ContractRefutation
