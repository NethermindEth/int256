import CIL.Safety.Equations
import UInt256.Methods.Bitwise.ScalarPrefix
import UInt256.Safety.FourLimbWrites
import UInt256.Safety.OutputReadability
import CIL.Safety.StepComposition
import CIL.Safety.ValueBitCasts
import CIL.SymbolicExecution

namespace UInt256Proof.StorageScalar
open CIL.Safety UInt256Model.Safety
set_option maxRecDepth 4096

def body (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile := profile, locals := [], returnsValue := false, code := [
    .arg 0, .skipInit, .feature .vector256Accelerated, .brzero 13,
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .arg 0, .memory .asRef, .dup, .arg 1, .store64,
    .dup, .const32 1, .memory (.add 8 true), .arg 2, .store64,
    .dup, .const32 2, .memory (.add 8 true), .arg 3, .store64,
    .const32 3, .memory (.add 8 true), .arg 4, .store64, .ret] }
def arguments (output : Reference) (w0 w1 w2 w3 : BitVec 64) : List Value :=
  [.reference (.address output), .scalar (.i64 w0), .scalar (.i64 w1),
    .scalar (.i64 w2), .scalar (.i64 w3)]

private theorem limb_address {program : CIL.Program} {memory : Memory}
    {inputs : List Reference} {output : Reference}
    (call : CallingConditions program memory inputs [output]) (index : Fin 4) :
    add memory output 8 (BitVec.ofNat 64 index.val) =
      .ok { output with offset := output.offset + 8 * index.val } := by
  obtain ⟨allocation, ready⟩ := access_requirements (call.1.2.2 (wordView output) (by simp))
  exact ready.add_slice call.1.1 8 index.val 8 (by omega) (by dsimp [wordView] at ready ⊢; omega)

macro "storage_step" facts:term,* : tactic =>
  `(tactic| simp [step, arguments, checkedValue, numericValue, formValue,
    pureArity, instruction, staticInstruction, memoryInstruction, CIL.offsetValue, storeValue, referenceAt, ordinaryAccessAlignment,
    checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure,
    cil_code, $[$facts:term],*])

/-- The complete constructor body is checked once, independently of extraction.
    Readback, caller permissions and the write footprint share this execution. -/
theorem store_limbs_safe (profile : CIL.FeatureProfile) (scalar : profile.vector256Accelerated = false) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (body profile))
    (memory : Memory) (inputs : List Reference) (output : Reference)
    (w0 w1 w2 w3 : BitVec 64)
    (call : CallingConditions program memory inputs [output]) :
    ∃ result,
      invoke program 24 index (arguments output w0 w1 w2 w3) memory = .ok (result, []) ∧
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
  have a1 := limb_address c1 1
  have a2 := limb_address c2 2
  have a3 := limb_address c3 3
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, CIL.fin_val_three, Nat.reduceMul, Nat.add_zero] at a0 a1 a2 a3 h0
  apply invoke_of_run found
  · simp [arguments, checkedValue, numericValue, formValue, checkedAt, f0,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · rfl
  · iterate 23
      apply Eq.trans
      · apply run_next found
        · simp only [body]; rfl
        · first
          | exact UInt256Proof.Bitwise.feature_disabled (body profile) scalar _ _ _ _ _
          | exact UInt256Proof.Bitwise.scalar_branch _ _ _ _ _ _ _
          | storage_step f0, f1, f2, f3, a0, a1, a2, a3, h0, h1, h2, h3
            try exact ⟨rfl, rfl, rfl, rfl⟩
            done
    simp [run, found, body, step, leaveFrame, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms store_limbs_safe

def packed (w0 w1 w2 w3 : BitVec 64) : BitVec 256 := BitVec.ofNat 256
  (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192)

private theorem load_aggregate_of_read (memory : Memory) (output : Reference) (bytes : List (BitVec 8))
    (loaded : read memory output 32 1 = .ok bytes) :
    loadLocal memory (.bytes (.aggregate 32) output) = .ok (.scalar (.aggregate bytes)) := by
  exact loadLocal_of_read loaded

theorem store_limbs_contract (profile : CIL.FeatureProfile) (scalar : profile.vector256Accelerated = false) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (body profile))
    (memory : Memory) (inputs : List Reference) (output : Reference)
    (w0 w1 w2 w3 : BitVec 64)
    (call : CallingConditions program memory inputs [output]) :
    ∃ result,
      invoke program 24 index (arguments output w0 w1 w2 w3) memory = .ok (result, []) ∧
      CallingConditions program result inputs [output] ∧
      (∀ id offset, OutsideOutput output id offset → result.cells id offset = memory.cells id offset) ∧
      AccessBelow memory.nextIdentity memory result ∧
      read result output 32 1 = .ok (numberBytes (packed w0 w1 w2 w3).toNat 32) ∧
      loadLocal result (.bytes (.aggregate 32) output) =
        .ok (.scalar (.aggregate (numberBytes (packed w0 w1 w2 w3).toNat 32))) := by
  obtain ⟨result, executed, valid, outside, authority, r0, r1, r2, r3⟩ :=
    store_limbs_safe profile scalar program index found memory inputs output w0 w1 w2 w3 call
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

#print axioms store_limbs_contract

theorem store_limbs_readable_contract (profile : CIL.FeatureProfile)
    (scalar : profile.vector256Accelerated = false) (program : CIL.Program) (index : Nat)
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
    store_limbs_safe profile scalar program index found memory inputs output w0 w1 w2 w3 call
  refine ⟨24, result, executed, valid, outside, authority,
    output_value_of_limb_reads result output w0 w1 w2 w3 r0 r1 r2 r3, ?_⟩
  apply output_readable_of_limbs result output (valid.1.2.2 (wordView output) (by simp))
  intro i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact ⟨_, by simpa using r0⟩
  · exact ⟨_, r1⟩
  · exact ⟨_, r2⟩
  · exact ⟨_, r3⟩

#print axioms store_limbs_readable_contract
end UInt256Proof.StorageScalar
