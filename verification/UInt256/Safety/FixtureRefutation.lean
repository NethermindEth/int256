import UInt256.Safety.ContractRefutation
import UInt256.Safety.ReportingContract

namespace UInt256Model.Safety.ContractRefutation
open CIL.Safety UInt256Model.Safety

/-- A located non-fuel fault from a valid call refutes the checked wrapping contract for every fuel. -/
theorem checked_binary_fault_refuted (program : CIL.Program) (entry observedFuel : Nat)
    (operation : BitVec 256 → BitVec 256 → BitVec 256) (memory : Memory)
    (left right output : Reference) (fault : LocatedFault)
    (call : CallingConditions program memory [left, right] [output])
    (semantic : fault.fault ≠ .fuelExhausted)
    (witness : invoke program observedFuel entry (binaryArguments left right output) memory = .error fault) :
    ¬ WrappingBinaryContract operation program entry := by
  intro contract
  obtain ⟨fuel, final, certificate, _⟩ := contract memory left right output call
  exact invoke_fault_refutes_success program observedFuel entry _ memory fault semantic witness
    fuel (final, []) certificate.1

/-- A wrong returned flag refutes the checked reporting contract. -/
theorem checked_reporting_flag_refuted (program : CIL.Program) (entry observedFuel : Nat)
    (operation : BitVec 256 → BitVec 256 → BitVec 256) (flag : BitVec 256 → BitVec 256 → Bool)
    (memory : Memory) (left right output : Reference) (actual : List Value)
    (call : CallingConditions program memory [left, right] [output])
    (observed : (invoke program observedFuel entry (binaryArguments left right output) memory).map
      Prod.snd = .ok actual)
    (different : actual ≠
      [.scalar (.i32 (if flag (inputValue memory left) (inputValue memory right) then 1 else 0))]) :
    ¬ ReportingBinaryContract operation flag program entry := by
  intro contract
  obtain ⟨fuel, final, certificate, _⟩ := contract memory left right output call
  have values := checked_observation_unique program entry observedFuel fuel
    (binaryArguments left right output) memory final _ Prod.snd actual observed certificate.1
  exact different values.symm

/-- A wrong stored byte refutes the checked reporting contract, whatever flag is returned. -/
theorem checked_reporting_byte_refuted (program : CIL.Program) (entry observedFuel : Nat)
    (operation : BitVec 256 → BitVec 256 → BitVec 256) (flag : BitVec 256 → BitVec 256 → Bool)
    (memory : Memory) (left right output : Reference) (byteIndex : Nat) (actual : BitVec 8)
    (call : CallingConditions program memory [left, right] [output])
    (observed : (invoke program observedFuel entry (binaryArguments left right output) memory).map
      (fun outcome => (inputValue outcome.1 output).extractLsb' (8 * byteIndex) 8) = .ok actual)
    (different : actual ≠
      (operation (inputValue memory left) (inputValue memory right)).extractLsb' (8 * byteIndex) 8) :
    ¬ ReportingBinaryContract operation flag program entry := by
  intro contract
  obtain ⟨fuel, final, certificate, result, _⟩ := contract memory left right output call
  have observation := checked_observation_unique program entry observedFuel fuel
    (binaryArguments left right output) memory final _
    (fun outcome => (inputValue outcome.1 output).extractLsb' (8 * byteIndex) 8) actual observed certificate.1
  rw [result] at observation
  exact different observation.symm

#print axioms checked_binary_fault_refuted
#print axioms checked_reporting_flag_refuted
#print axioms checked_reporting_byte_refuted
end UInt256Model.Safety.ContractRefutation
