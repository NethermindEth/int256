import UInt256.Methods.Multiply.ReturnValue
import Extracted
import UInt256.RepresentationLemmas
import CIL.MultiplyProfileCoverage
import CIL.MultiplyFeatures
open Lean Elab Command CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply

def scalarArguments (width : Nat) (wordLeft : Bool) (input : Nat) (word : BitVec width) : List Value :=
  let argument := if width = 32 then Value.i32 (word.setWidth 32) else Value.i64 (word.setWidth 64)
  if wordLeft then [argument, .object input] else [.object input, argument]

theorem scalar_return_of_execution (width : Nat) (wordLeft : Bool)
    (wordValue : ∀ word : BitVec width, (word.setWidth 64).toNat = word.toNat)
    (execute : ∀ (memory : Memory) (input frame fuel : Nat) (a : Limbs) (word : BitVec width),
      (∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) = some (.i64 (a i))) →
      ∃ final, run Extracted.program (fuel + executionBound Extracted.program Extracted.entryIndex)
          Extracted.entryIndex 0 (scalarArguments width wordLeft input word) frame [] memory =
            some (final, [.v256 (returnOutput a (singleWord (word.setWidth 64)))]) ∧
        ∀ address, final (.byte address) = memory (.byte address))
    (initial : Bytes) (input : Nat) (word : BitVec width) :
    ScalarReturnContract Extracted.program Extracted.entryIndex width wordLeft initial input word := by
  let memory := initFrame (byteMemory initial) 0 Extracted.entryBody (scalarArguments width wordLeft input word)
  have caller : ∀ address, memory (.byte address) = byteMemory initial (.byte address) := by
    intro address
    simp [memory, initFrame, cil_code, clearHome_caller, writeAggregate, writeHomeBytes_caller, initLocals_bytes]
  have reads : ∀ i : Fin 4, read64 memory (.byte (input + 8*i.val)) =
      some (.i64 (inputLimbs initial input i)) := by
    intro i
    rw [read64_congr memory (byteMemory initial) caller]
    exact read64_initial initial input i
  obtain ⟨final, execution, bytes⟩ := execute memory input 0 0 (inputLimbs initial input) word reads
  simp only [returnOutput, singleWord_value, wordValue] at execution
  rw [input_value] at execution
  refine ⟨executionBound Extracted.program Extracted.entryIndex, final, ?_, ?_⟩
  · change invoke Extracted.program (executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex (scalarArguments width wordLeft input word) (byteMemory initial) = _
    simp only [invoke, cil_code, Option.bind_eq_bind, Option.bind_some]
    simpa only [Nat.zero_add, cil_code, memory] using execution
  · intro address
    exact (bytes address).trans (caller address)

theorem scalar_return_profile_of_contract (width : Nat) (wordLeft : Bool)
    (correct : ∀ initial input word, ScalarReturnContract Extracted.program Extracted.entryIndex
      width wordLeft initial input word)
    (profile : FeatureProfile) (_valid : profile.Valid)
    (agreement : Extracted.program.ProfileAgreement Extracted.profile profile)
    (initial : Bytes) (input : Nat) (word : BitVec width) :
    ScalarReturnContract (reprofile Extracted.program profile) Extracted.entryIndex width wordLeft initial input word := by
  obtain ⟨fuel, final, execution, bytes⟩ := correct initial input word
  refine ⟨fuel, final, ?_, bytes⟩
  rw [← Extracted.profileExecution_eq profile agreement]
  exact execution

theorem scalar_return_family_of_contract (width : Nat) (wordLeft : Bool)
    (correct : ∀ initial input word, ScalarReturnContract Extracted.program Extracted.entryIndex
      width wordLeft initial input word)
    (profile : FeatureProfile) (valid : profile.Valid)
    (same : Extracted.profile.classifyMultiply = profile.classifyMultiply)
    (storage : Extracted.profile.vector256Accelerated = profile.vector256Accelerated)
    (initial : Bytes) (input : Nat) (word : BitVec width) :
    ScalarReturnContract (reprofile Extracted.program profile) Extracted.entryIndex width wordLeft initial input word := by
  have flags := FeatureProfile.multiply_classification_agreement Extracted.profile profile
    Extracted.profileValid valid same
  apply scalar_return_profile_of_contract width wordLeft correct profile valid
  exact multiply_profile_agreement Extracted.program Extracted.profile profile
    Extracted.profileValid valid (by decide)
    (congrArg (fun flags => flags.1) flags)
    (congrArg (fun flags => flags.2.1) flags)
    (congrArg (fun flags => flags.2.2.1) flags)
    (congrArg (fun flags => flags.2.2.2) flags) storage

elab "multiply_scalar_return_gates " width:num order:term " using " execution:ident
    " gates " checked:ident profileChecked:ident familyChecked:ident : command => do
  elabCommand (← `(command|
    theorem $checked (initial : Bytes) (input : Nat) (word : BitVec $width) :
        ScalarReturnContract Extracted.program Extracted.entryIndex $width $order initial input word := by
      apply scalar_return_of_execution $width $order _ $execution
      intro word
      simp only [BitVec.toNat_setWidth]
      have bound := word.isLt
      omega))

  elabCommand (← `(command|
    theorem $profileChecked (profile : FeatureProfile) (valid : profile.Valid)
        (agreement : Extracted.program.ProfileAgreement Extracted.profile profile)
        (initial : Bytes) (input : Nat) (word : BitVec $width) :
        ScalarReturnContract (reprofile Extracted.program profile) Extracted.entryIndex
          $width $order initial input word :=
      scalar_return_profile_of_contract $width $order $checked profile valid agreement initial input word))

  elabCommand (← `(command|
    theorem $familyChecked (profile : FeatureProfile) (valid : profile.Valid)
        (same : Extracted.profile.classifyMultiply = profile.classifyMultiply)
        (storage : Extracted.profile.vector256Accelerated = profile.vector256Accelerated)
        (initial : Bytes) (input : Nat) (word : BitVec $width) :
        ScalarReturnContract (reprofile Extracted.program profile) Extracted.entryIndex
          $width $order initial input word :=
      scalar_return_family_of_contract $width $order $checked profile valid same storage initial input word))

end UInt256Proof.Multiply
