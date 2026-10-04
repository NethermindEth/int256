import UInt256.Methods.Multiply.Returning
import UInt256.RepresentationLemmas
import CIL.MultiplyProfileCoverage
import CIL.MultiplyFeatures
open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply

theorem return_correct (initial : Bytes) (left right : Nat) :
    ReturnContract Extracted.program Extracted.entryIndex initial left right := by
  let memory := initFrame (byteMemory initial) 0 Extracted.entryBody [.object left, .object right]
  have caller : ∀ address, memory (.byte address) = byteMemory initial (.byte address) := by
    intro address
    simp [memory, initFrame, cil_code, clearHome_caller, writeAggregate, writeHomeBytes_caller, initLocals_bytes]
  have leftReads : ∀ i : Fin 4, read64 memory (.byte (left + 8*i.val)) =
      some (.i64 (inputLimbs initial left i)) := by
    intro i
    rw [read64_congr memory (byteMemory initial) caller]
    exact read64_initial initial left i
  have rightReads : ∀ i : Fin 4, read64 memory (.byte (right + 8*i.val)) =
      some (.i64 (inputLimbs initial right i)) := by
    intro i
    rw [read64_congr memory (byteMemory initial) caller]
    exact read64_initial initial right i
  obtain ⟨final, execution, bytes⟩ := execute_return_entry memory left right 0 0
    (inputLimbs initial left) (inputLimbs initial right) leftReads rightReads
  simp only [returnOutput] at execution
  rw [input_value, input_value] at execution
  refine ⟨executionBound Extracted.program Extracted.entryIndex, final, ?_, ?_⟩
  · simp only [invoke, cil_code, Option.bind_eq_bind, Option.bind_some]
    simpa only [Nat.zero_add, cil_code, memory] using execution
  · intro address
    exact (bytes address).trans (caller address)

theorem return_checked_contract : ∀ (initial : Bytes) (left right : Nat),
    ReturnContract Extracted.program Extracted.entryIndex initial left right := return_correct

theorem return_checked_profile_contract (profile : FeatureProfile)
    (_valid : profile.Valid) (agreement : Extracted.program.ProfileAgreement Extracted.profile profile)
    (initial : Bytes) (left right : Nat) :
    ReturnContract (reprofile Extracted.program profile) Extracted.entryIndex initial left right := by
  obtain ⟨fuel, final, execution, bytes⟩ := return_checked_contract initial left right
  refine ⟨fuel, final, ?_, bytes⟩
  rw [← Extracted.profileExecution_eq profile agreement]
  exact execution
theorem return_checked_family_contract (profile : FeatureProfile)
    (valid : profile.Valid)
    (same : Extracted.profile.classifyMultiply = profile.classifyMultiply)
    (storage : Extracted.profile.vector256Accelerated = profile.vector256Accelerated)
    (initial : Bytes) (left right : Nat) :
    ReturnContract (reprofile Extracted.program profile) Extracted.entryIndex initial left right := by
  have flags := FeatureProfile.multiply_classification_agreement Extracted.profile profile
    Extracted.profileValid valid same
  apply return_checked_profile_contract profile valid
  exact multiply_profile_agreement Extracted.program Extracted.profile profile
    Extracted.profileValid valid (by decide)
    (congrArg (fun flags => flags.1) flags)
    (congrArg (fun flags => flags.2.1) flags)
    (congrArg (fun flags => flags.2.2.1) flags)
    (congrArg (fun flags => flags.2.2.2) flags) storage

end UInt256Proof.Multiply




