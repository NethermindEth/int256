import UInt256.Generated.MethodTemplates
import UInt256.Safety.FourLimbWrites
import UInt256.Safety.OutputReadability
import CIL.Safety.StepComposition
import CIL.Safety.GuardNormalization
import CIL.Safety.ValueBitCasts
import CIL.Safety.SymbolicExecution

namespace UInt256Proof.Multiply.LimbStorage
open CIL.Safety UInt256Model.Safety
set_option maxRecDepth 4096

def body (profile : CIL.FeatureProfile) : CIL.Method := by_elab
  let body ← Lean.Elab.Term.elabTermAndSynthesize
    (← `(UInt256Proof.Generated.Method.method25 $(Lean.mkIdent `profile))) none
  let some unfolded ← Lean.Meta.unfoldDefinition? body
    | throwError "Expected generated template application"
  return ← Lean.Meta.withTransparency .default (Lean.Meta.reduce unfolded)

def arguments (output : Reference) (w0 w1 w2 w3 : BitVec 64) : List Value :=
  [.reference (.address output), .scalar (.i64 w0), .scalar (.i64 w1),
    .scalar (.i64 w2), .scalar (.i64 w3)]

/-- The complete limb storage body is checked once, independently of extraction.
    Readback, caller permissions and the write footprint share this execution. -/
theorem store_limbs_safe (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (body profile))
    (memory : Memory) (inputs : List Reference) (output : Reference)
    (w0 w1 w2 w3 : BitVec 64)
    (call : CallingConditions program memory inputs [output]) :
    ∃ result,
      invoke program 23 index (arguments output w0 w1 w2 w3) memory = .ok (result, []) ∧
      CallingConditions program result inputs [output] ∧
      (∀ id offset, OutsideOutput output id offset → result.cells id offset = memory.cells id offset) ∧
      AccessBelow memory.nextIdentity memory result ∧
      read result output 8 1 = .ok (numberBytes w0.toNat 8) ∧
      read result { output with offset := output.offset + 8 } 8 1 = .ok (numberBytes w1.toNat 8) ∧
      read result { output with offset := output.offset + 16 } 8 1 = .ok (numberBytes w2.toNat 8) ∧
      read result { output with offset := output.offset + 24 } 8 1 = .ok (numberBytes w3.toNat 8) := by
  obtain ⟨m1, m2, m3, m4, h0, h1, h2, h3, c1, c2, c3, c4, outside, authority, reads⟩ :=
    write_four_limbs program memory inputs output w0 w1 w2 w3 call
  refine ⟨m4, ?_, c4, outside, authority, reads⟩
  have f0 := call.output_formed (by simp : output ∈ [output])
  have f1 := c1.output_formed (by simp : output ∈ [output])
  have f2 := c2.output_formed (by simp : output ∈ [output])
  have f3 := c3.output_formed (by simp : output ∈ [output])
  have member : output ∈ [output] := by simp
  cil_checked_steps [found, body, arguments, f0, f1, f2, f3, h0, h1, h2, h3,
    call.output_limb_address member 0, c1.output_limb_address member 1,
    c2.output_limb_address member 2, c3.output_limb_address member 3,
    call.output_limb_formed member 0, c1.output_limb_formed member 1,
    c2.output_limb_formed member 2, c3.output_limb_formed member 3,
    storeValue, referenceAt, ordinaryAccessAlignment]

theorem store_limbs_readable_contract (profile : CIL.FeatureProfile)
    (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (body profile))
    (memory : Memory) (inputs : List Reference) (output : Reference)
    (w0 w1 w2 w3 : BitVec 64)
    (call : CallingConditions program memory inputs [output]) :
    ∃ fuel result,
      invoke program fuel index (arguments output w0 w1 w2 w3) memory = .ok (result, []) ∧
      CallingConditions program result inputs [output] ∧
      (∀ id offset, OutsideOutput output id offset → result.cells id offset = memory.cells id offset) ∧
      AccessBelow memory.nextIdentity memory result ∧
      inputValue result output = BitVec.ofNat 256
        (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192) ∧
      (∃ bytes, read result output 32 1 = .ok bytes) := by
  obtain ⟨result, executed, valid, outside, authority, r0, r1, r2, r3⟩ :=
    store_limbs_safe profile program index found memory inputs output w0 w1 w2 w3 call
  refine ⟨23, result, executed, valid, outside, authority,
    output_value_of_limb_reads result output w0 w1 w2 w3 r0 r1 r2 r3, ?_⟩
  apply output_readable_of_limbs result output (valid.1.writable (wordView output) (by simp))
  intro i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact ⟨_, by simpa using r0⟩
  · exact ⟨_, r1⟩
  · exact ⟨_, r2⟩
  · exact ⟨_, r3⟩

end UInt256Proof.Multiply.LimbStorage
