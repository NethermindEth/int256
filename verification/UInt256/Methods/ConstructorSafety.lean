import CIL.Safety.Equations
import UInt256.Safety.FourLimbWrites
import UInt256.Safety.OutputReadability
import CIL.Safety.StepComposition
import CIL.Safety.ValueBitCasts
import CIL.SymbolicExecution
import CIL.Safety.GuardNormalization

namespace UInt256Proof.ConstructorSafety
open CIL.Safety UInt256Model.Safety
set_option maxRecDepth 4096

def body (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile := profile, locals := [], returnsValue := false, code := [
    .arg 0, .arg 1, .setFieldAt 0 8,
    .arg 0, .arg 2, .setFieldAt 8 8,
    .arg 0, .arg 3, .setFieldAt 16 8,
    .arg 0, .arg 4, .setFieldAt 24 8, .ret] }

def arguments (output : Reference) (w0 w1 w2 w3 : BitVec 64) : List Value :=
  [.reference (.address output), .scalar (.i64 w0), .scalar (.i64 w1),
    .scalar (.i64 w2), .scalar (.i64 w3)]

macro "constructor_step" facts:term,* : tactic =>
  `(tactic| simp [step, cil_guard, observerCount, arguments, checkedValue, numericValue, formValue,
    pureArity, instruction, storeValue, referenceAt, ordinaryAccessAlignment,
    checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure,
    cil_code, $[$facts:term],*])

/-- The complete constructor body is checked once, independently of extraction.
    Readback, caller permissions and the write footprint share this execution. -/
theorem constructor_safe (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (body profile))
    (memory : Memory) (inputs : List Reference) (output : Reference)
    (w0 w1 w2 w3 : BitVec 64)
    (call : CallingConditions program memory inputs [output]) :
    ∃ result,
      invoke program 13 index (arguments output w0 w1 w2 w3) memory = .ok (result, []) ∧
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
  have a0 := call.output_limb_address (by simp : output ∈ [output]) 0
  have a1 := c1.output_limb_address (by simp : output ∈ [output]) 1
  have a2 := c2.output_limb_address (by simp : output ∈ [output]) 2
  have a3 := c3.output_limb_address (by simp : output ∈ [output]) 3
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, CIL.fin_val_three, Nat.reduceMul, Nat.add_zero] at a0 a1 a2 a3 h0
  apply invoke_of_run found
  · simp [arguments, checkedValue, numericValue, formValue, checkedAt, f0,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · rfl
  · iterate 12
      apply Eq.trans
      · apply run_next found
        · simp only [body]; rfl
        · constructor_step f0, f1, f2, f3, a0, a1, a2, a3, h0, h1, h2, h3
          try exact ⟨rfl, rfl, rfl, rfl⟩
          done
    simp [run, found, body, step, cil_guard, observerCount, leaveFrame, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms constructor_safe

def packed (w0 w1 w2 w3 : BitVec 64) : BitVec 256 := BitVec.ofNat 256
  (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192)

private theorem load_aggregate_of_read (memory : Memory) (output : Reference) (bytes : List (BitVec 8))
    (loaded : read memory output 32 1 = .ok bytes) :
    loadLocal memory (.bytes (.aggregate 32) output) = .ok (.scalar (.aggregate bytes)) := by
  exact loadLocal_of_read loaded

theorem constructor_contract (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (body profile))
    (memory : Memory) (inputs : List Reference) (output : Reference)
    (w0 w1 w2 w3 : BitVec 64)
    (call : CallingConditions program memory inputs [output]) :
    ∃ result,
      invoke program 13 index (arguments output w0 w1 w2 w3) memory = .ok (result, []) ∧
      CallingConditions program result inputs [output] ∧
      (∀ id offset, OutsideOutput output id offset → result.cells id offset = memory.cells id offset) ∧
      AccessBelow memory.nextIdentity memory result ∧
      read result output 32 1 = .ok (numberBytes (packed w0 w1 w2 w3).toNat 32) ∧
      loadLocal result (.bytes (.aggregate 32) output) =
        .ok (.scalar (.aggregate (numberBytes (packed w0 w1 w2 w3).toNat 32))) := by
  obtain ⟨result, executed, valid, outside, authority, r0, r1, r2, r3⟩ :=
    constructor_safe profile program index found memory inputs output w0 w1 w2 w3 call
  have value := output_value_of_limb_reads result output w0 w1 w2 w3 r0 r1 r2 r3
  obtain ⟨bytes, loaded⟩ := output_readable_of_limbs result output
    (valid.1.2.2 (wordView output) (by simp)) (by
      intro i
      have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
      rcases cases with h | h | h | h <;> simp only [h, Nat.reduceMul, Nat.add_zero]
      · exact ⟨_, r0⟩
      · exact ⟨_, r1⟩
      · exact ⟨_, r2⟩
      · exact ⟨_, r3⟩)
  have length : bytes.length = 32 := by rw [read_result_snapshot loaded]; simp
  have number := output_snapshot_value result output bytes loaded
  rw [value] at number
  change BitVec.ofNat 256 (byteNumber bytes) = packed w0 w1 w2 w3 at number
  have encoded : numberBytes (packed w0 w1 w2 w3).toNat 32 = bytes := by
    rw [← number]
    exact vector256_bytes_roundtrip bytes length
  have readback : read result output 32 1 = .ok (numberBytes (packed w0 w1 w2 w3).toNat 32) := by
    rw [encoded]; exact loaded
  exact ⟨result, executed, valid, outside, authority, readback, load_aggregate_of_read result output _ readback⟩

#print axioms constructor_contract
end UInt256Proof.ConstructorSafety
