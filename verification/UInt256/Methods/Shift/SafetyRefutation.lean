import UInt256.Safety.ShiftContract
import UInt256.Safety.ReadOnlyScalarContract
import CIL.Safety.FuelLemmas
namespace UInt256Proof.Shift
open CIL.Safety UInt256Model.Safety

/-- A concrete checked wrong result refutes the full shift contract at every fuel. -/
theorem checked_result_refuted (program : CIL.Program) (entry observedFuel : Nat)
    (direction : Direction) (memory : Memory) (input output : Reference) (count : BitVec 32)
    (actual : BitVec 256) (call : CallingConditions program memory [input] [output])
    (observed : (invoke program observedFuel entry (shiftArguments input count output) memory).map
      (fun outcome => inputValue outcome.1 output) = .ok actual)
    (different : actual ≠ result direction (inputValue memory input) count) :
    ¬ ShiftContract direction program entry := by
  intro contract
  obtain ⟨fuel, final, certificate, value, _⟩ := contract memory input count output call
  cases execution : invoke program observedFuel entry (shiftArguments input count output) memory with
  | error fault => simp [execution, Except.map] at observed
  | ok outcome =>
    have first := invoke_mono program observedFuel fuel entry (shiftArguments input count output) memory (.ok outcome) trivial execution
    have second := invoke_mono program fuel observedFuel entry (shiftArguments input count output) memory (.ok (final, [])) trivial certificate.1
    rw [Nat.add_comm] at second
    have same := Except.ok.inj (first.symm.trans second)
    subst outcome
    have actualValue : inputValue final output = actual := by simpa [execution, Except.map] using observed
    exact different (actualValue.symm.trans value)

/-- Returning operators expose the actual aggregate bytes, not an unchecked vector surrogate. -/
theorem checked_operator_refuted (program : CIL.Program) (entry observedFuel : Nat)
    (direction : Direction) (memory : Memory) (input : Reference) (count : BitVec 32)
    (actual : CIL.Value) (call : CallingConditions program memory [input] [])
    (observed : (invoke program observedFuel entry (scalarArguments input (.i32 count)) memory).map
      Prod.snd = .ok [.scalar actual])
    (different : actual ≠ .aggregate (numberBytes (result direction (inputValue memory input) count).toNat 32)) :
    ¬ ReadOnlyScalarContract CIL.Value.i32
      (fun value count => .aggregate (numberBytes (result direction value count).toNat 32)) program entry := by
  intro contract
  obtain ⟨fuel, final, certificate, _⟩ := contract memory input count call
  cases execution : invoke program observedFuel entry (scalarArguments input (.i32 count)) memory with
  | error fault => simp [execution, Except.map] at observed
  | ok outcome =>
    have first := invoke_mono program observedFuel fuel entry (scalarArguments input (.i32 count)) memory (.ok outcome) trivial execution
    have second := invoke_mono program fuel observedFuel entry (scalarArguments input (.i32 count)) memory (.ok (final, [.scalar (.aggregate (numberBytes (result direction (inputValue memory input) count).toNat 32))])) trivial certificate.1
    rw [Nat.add_comm] at second
    have same := Except.ok.inj (first.symm.trans second)
    subst outcome
    have values := Except.ok.inj (by simpa only [execution, Except.map] using observed)
    exact different (Value.scalar.inj (List.cons.inj values).1).symm

#print axioms checked_result_refuted
#print axioms checked_operator_refuted
end UInt256Proof.Shift
