import UInt256.Safety.AggregateReturn
import CIL.Safety.FuelLemmas
namespace UInt256Model.Safety.ContractRefutation
open CIL.Safety UInt256Model.Safety

/-- A successful checked observation is independent of the successful fuel budget. -/
theorem checked_observation_unique {α : Type} (program : CIL.Program)
    (entry observedFuel fuel : Nat) (args : List Value) (memory final : Memory)
    (values : List Value) (observe : Memory × List Value → α) (actual : α)
    (observed : (invoke program observedFuel entry args memory).map observe = .ok actual)
    (execution : invoke program fuel entry args memory = .ok (final, values)) :
    observe (final, values) = actual := by
  cases firstExecution : invoke program observedFuel entry args memory with
  | error fault => simp [firstExecution, Except.map] at observed
  | ok outcome =>
    have first := invoke_mono program observedFuel fuel entry args memory (.ok outcome) trivial firstExecution
    have second := invoke_mono program fuel observedFuel entry args memory (.ok (final, values)) trivial execution
    rw [Nat.add_comm] at second
    have same := Except.ok.inj (first.symm.trans second)
    subst outcome
    simpa [firstExecution, Except.map] using observed

/-- An overlapping-input counterexample refutes the full checked contract. -/
theorem checked_binary_refuted (program : CIL.Program) (entry observedFuel : Nat)
    (operation : BitVec 256 → BitVec 256 → BitVec 256) (memory : Memory)
    (left right output : Reference) (actual : BitVec 256)
    (call : CallingConditions program memory [left, right] [output])
    (observed : (invoke program observedFuel entry (binaryArguments left right output) memory).map
      (fun outcome => inputValue outcome.1 output) = .ok actual)
    (different : actual ≠ operation (inputValue memory left) (inputValue memory right)) :
    ¬ WrappingBinaryContract operation program entry := by
  intro contract
  obtain ⟨fuel, final, certificate, result, _⟩ := contract memory left right output call
  have actualValue := checked_observation_unique program entry observedFuel fuel
    (binaryArguments left right output) memory final [] (fun outcome => inputValue outcome.1 output)
    actual observed certificate.1
  exact different (actualValue.symm.trans result)

/-- A wrong returned aggregate refutes the arithmetic part of the checked return contract. -/
theorem checked_binary_return_refuted (program : CIL.Program) (entry observedFuel : Nat)
    (operation : BitVec 256 → BitVec 256 → BitVec 256) (memory : Memory)
    (left right : Reference) (actual : List (BitVec 8))
    (call : CallingConditions program memory [left, right] [])
    (observed : (invoke program observedFuel entry (AggregateReturn.binaryArgs left right) memory).map
      Prod.snd = .ok [.scalar (.aggregate actual)])
    (different : BitVec.ofNat 256 (CIL.Safety.byteNumber actual) ≠ operation (inputValue memory left) (inputValue memory right)) :
    ¬ AggregateReturn.BinaryContract operation program entry := by
  intro contract
  obtain ⟨fuel, final, bytes, certificate, _, result, _⟩ := contract memory left right call
  have values := checked_observation_unique program entry observedFuel fuel
    (AggregateReturn.binaryArgs left right) memory final [.scalar (.aggregate bytes)] Prod.snd
    [.scalar (.aggregate actual)] observed certificate.1
  have same : bytes = actual := CIL.Value.aggregate.inj (Value.scalar.inj (List.cons.inj values).1)
  subst bytes
  exact different result

/-- An overlapping-input counterexample refutes the full checked contract. -/
theorem checked_unary_refuted (program : CIL.Program) (entry observedFuel : Nat)
    (operation : BitVec 256 → BitVec 256) (memory : Memory)
    (input output : Reference) (actual : BitVec 256)
    (call : CallingConditions program memory [input] [output])
    (observed : (invoke program observedFuel entry (unaryArguments input output) memory).map
      (fun outcome => inputValue outcome.1 output) = .ok actual)
    (different : actual ≠ operation (inputValue memory input)) :
    ¬ WrappingUnaryContract operation program entry := by
  intro contract
  obtain ⟨fuel, final, certificate, result, _⟩ := contract memory input output call
  have actualValue := checked_observation_unique program entry observedFuel fuel
    (unaryArguments input output) memory final [] (fun outcome => inputValue outcome.1 output)
    actual observed certificate.1
  exact different (actualValue.symm.trans result)

/-- A wrong returned aggregate refutes the arithmetic part of the checked return contract. -/
theorem checked_unary_return_refuted (program : CIL.Program) (entry observedFuel : Nat)
    (operation : BitVec 256 → BitVec 256) (memory : Memory)
    (input : Reference) (actual : List (BitVec 8))
    (call : CallingConditions program memory [input] [])
    (observed : (invoke program observedFuel entry (AggregateReturn.unaryArgs input) memory).map
      Prod.snd = .ok [.scalar (.aggregate actual)])
    (different : BitVec.ofNat 256 (CIL.Safety.byteNumber actual) ≠ operation (inputValue memory input)) :
    ¬ AggregateReturn.UnaryContract operation program entry := by
  intro contract
  obtain ⟨fuel, final, bytes, certificate, _, result, _⟩ := contract memory input call
  have values := checked_observation_unique program entry observedFuel fuel
    (AggregateReturn.unaryArgs input) memory final [.scalar (.aggregate bytes)] Prod.snd
    [.scalar (.aggregate actual)] observed certificate.1
  have same : bytes = actual := CIL.Value.aggregate.inj (Value.scalar.inj (List.cons.inj values).1)
  subst bytes
  exact different result


#print axioms checked_unary_refuted
#print axioms checked_unary_return_refuted
#print axioms checked_binary_refuted
#print axioms checked_binary_return_refuted
end UInt256Model.Safety.ContractRefutation

namespace UInt256Model.Safety.ContractRefutation
open CIL.Safety

theorem checked_binary_byte_refuted (program : CIL.Program) (entry observedFuel : Nat)
    (operation : BitVec 256 → BitVec 256 → BitVec 256) (memory : Memory)
    (left right output : Reference) (byteIndex : Nat) (actual : BitVec 8)
    (call : CallingConditions program memory [left, right] [output])
    (observed : (invoke program observedFuel entry (binaryArguments left right output) memory).map
      (fun outcome => (inputValue outcome.1 output).extractLsb' (8 * byteIndex) 8) = .ok actual)
    (different : actual ≠ (operation (inputValue memory left) (inputValue memory right)).extractLsb' (8 * byteIndex) 8) :
    ¬ WrappingBinaryContract operation program entry := by
  intro contract
  obtain ⟨fuel, final, certificate, result, _⟩ := contract memory left right output call
  have observation := checked_observation_unique program entry observedFuel fuel
    (binaryArguments left right output) memory final []
    (fun outcome => (inputValue outcome.1 output).extractLsb' (8 * byteIndex) 8) actual observed certificate.1
  rw [result] at observation
  exact different observation.symm
#print axioms checked_binary_byte_refuted
end UInt256Model.Safety.ContractRefutation