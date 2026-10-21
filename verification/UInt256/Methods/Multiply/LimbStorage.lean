import UInt256.Safety.FourLimbWrites
import UInt256.Safety.OutputReadability
import CIL.Safety.StepComposition
import CIL.Safety.ValueBitCasts
import CIL.SymbolicExecution

namespace UInt256Proof.Multiply.LimbStorage
open CIL.Safety UInt256Model.Safety
set_option maxRecDepth 4096

private theorem s_arg {body : CIL.Method} {pc i : Nat} {args : List Value} {frame : Frame}
    {stack : List Value} {m : Memory} {r : Reference}
    (h : args[i]? = some (.reference (.address r))) (formed : form m r = .ok r) :
    step body (.arg i) pc args frame stack m = .ok (.next (pc + 1) (.reference (.address r) :: stack) frame m) := by
  unfold step
  simp only [h, checkedValue, formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

private theorem s_skipInit {body : CIL.Method} {pc : Nat} {args : List Value} {frame : Frame}
    {rest : List Value} {m : Memory} {r : Reference} (formed : form m r = .ok r) :
    step body .skipInit pc args frame (.reference (.address r) :: rest) m = .ok (.next (pc + 1) rest frame m) := by
  unfold step instruction
  simp only [show pureArity .skipInit = none from rfl, formValue, formed, checkedAt, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem s_fieldAddress {body : CIL.Method} {pc offset : Nat} {args : List Value} {frame : Frame}
    {rest : List Value} {m : Memory} {r result : Reference}
    (added : add m r 1 (BitVec.ofNat 64 offset) = .ok result) :
    step body (.fieldAddress offset) pc args frame (.reference (.address r) :: rest) m =
      .ok (.next (pc + 1) (.reference (.address result) :: rest) frame m) := by
  unfold step instruction
  simp only [show pureArity (.fieldAddress offset) = none from rfl, added, checkedAt, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem s_asRef {body : CIL.Method} {pc : Nat} {args : List Value} {frame : Frame}
    {rest : List Value} {m : Memory} {r : Reference} (formed : form m r = .ok r) :
    step body (.memory .asRef) pc args frame (.reference (.address r) :: rest) m =
      .ok (.next (pc + 1) (.reference (.address r) :: rest) frame m) := by
  unfold step staticInstruction memoryInstruction
  simp only [formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem s_store64 {body : CIL.Method} {pc : Nat} {args : List Value} {frame : Frame}
    {rest : List Value} {m m' : Memory} {r : Reference} {bits : BitVec 64}
    (written : write m r (numberBytes bits.toNat 8) 1 = .ok m') :
    step body .store64 pc args frame (.scalar (.i64 bits) :: .reference (.address r) :: rest) m =
      .ok (.next (pc + 1) rest frame m') := by
  unfold step instruction storeValue
  simp only [show pureArity .store64 = none from rfl, referenceAt, ordinaryAccessAlignment, written, checkedAt,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

def body (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile := profile, locals := [], returnsValue := false, code := [
    .arg 0, .skipInit, .arg 0, .fieldAddress 0, .memory .asRef, .arg 1, .store64,
    .arg 0, .fieldAddress 8, .memory .asRef, .arg 2, .store64,
    .arg 0, .fieldAddress 16, .memory .asRef, .arg 3, .store64,
    .arg 0, .fieldAddress 24, .memory .asRef, .arg 4, .store64, .ret] }

def arguments (output : Reference) (w0 w1 w2 w3 : BitVec 64) : List Value :=
  [.reference (.address output), .scalar (.i64 w0), .scalar (.i64 w1),
    .scalar (.i64 w2), .scalar (.i64 w3)]

macro "limb_storage_step" facts:term,* : tactic =>
  `(tactic| simp [step, arguments, checkedValue, numericValue, formValue,
    pureArity, instruction, staticInstruction, memoryInstruction, storeValue, referenceAt, ordinaryAccessAlignment,
    checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure,
    cil_code, $[$facts:term],*])

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
  apply invoke_of_run found
  · simp [arguments, checkedValue, numericValue, formValue, checkedAt, f0,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · rfl
  · refine (run_next found rfl (s_arg (by rfl) f0)).trans ?_
    refine (run_next found rfl (s_skipInit f0)).trans ?_
    refine (run_next found rfl (s_arg (by rfl) f0)).trans ?_
    refine (run_next found rfl (s_fieldAddress (call.output_limb_address (by simp : output ∈ [output]) 0))).trans ?_
    refine (run_next found rfl (s_asRef (call.output_limb_formed (by simp : output ∈ [output]) 0))).trans ?_
    refine (run_next found rfl (rfl)).trans ?_
    refine (run_next found rfl (s_store64 h0)).trans ?_
    refine (run_next found rfl (s_arg (by rfl) f1)).trans ?_
    refine (run_next found rfl (s_fieldAddress (c1.output_limb_address (by simp : output ∈ [output]) 1))).trans ?_
    refine (run_next found rfl (s_asRef (c1.output_limb_formed (by simp : output ∈ [output]) 1))).trans ?_
    refine (run_next found rfl (rfl)).trans ?_
    refine (run_next found rfl (s_store64 h1)).trans ?_
    refine (run_next found rfl (s_arg (by rfl) f2)).trans ?_
    refine (run_next found rfl (s_fieldAddress (c2.output_limb_address (by simp : output ∈ [output]) 2))).trans ?_
    refine (run_next found rfl (s_asRef (c2.output_limb_formed (by simp : output ∈ [output]) 2))).trans ?_
    refine (run_next found rfl (rfl)).trans ?_
    refine (run_next found rfl (s_store64 h2)).trans ?_
    refine (run_next found rfl (s_arg (by rfl) f3)).trans ?_
    refine (run_next found rfl (s_fieldAddress (c3.output_limb_address (by simp : output ∈ [output]) 3))).trans ?_
    refine (run_next found rfl (s_asRef (c3.output_limb_formed (by simp : output ∈ [output]) 3))).trans ?_
    refine (run_next found rfl (rfl)).trans ?_
    refine (run_next found rfl (s_store64 h3)).trans ?_
    refine (run_return found rfl rfl rfl).trans ?_
    rfl

#print axioms store_limbs_safe

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
  apply output_readable_of_limbs result output (valid.1.2.2 (wordView output) (by simp))
  intro i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact ⟨_, by simpa using r0⟩
  · exact ⟨_, r1⟩
  · exact ⟨_, r2⟩
  · exact ⟨_, r3⟩

#print axioms store_limbs_readable_contract
end UInt256Proof.Multiply.LimbStorage
