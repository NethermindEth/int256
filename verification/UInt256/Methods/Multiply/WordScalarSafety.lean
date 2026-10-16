import UInt256.Methods.Multiply.Product
import CIL.Safety.WordMemory
import CIL.Safety.AccessBelow
import CIL.Safety.StepComposition
import CIL.SymbolicExecution

namespace UInt256Proof.Multiply
open CIL.Safety

/-- Current scalar Multiply64 uses Math.BigMul; it no longer expands the old
    six-local software multiplication routine. -/
def scalarWordBody (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile := profile, locals := [], returnsValue := true, code := [
    .feature .bmi2, .brzero 11,
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .feature .armBase64, .brzero 22,
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .unsupported "Unreachable under selected profile",
    .arg 0, .arg 1, .arg 2, .memory .bigMul64, .ret] }

private theorem feature_step (body : CIL.Method) (feature : CIL.Feature) (pc : Nat)
    (args rest : List Value) (frame : Frame) (memory : Memory) :
    step body (.feature feature) pc args frame rest memory =
      .ok (.next (pc + 1) (.scalar (.i32 (if body.profile.evaluate feature then 1 else 0)) :: rest) frame memory) := rfl

private theorem feature_disabled (body : CIL.Method) (feature : CIL.Feature)
    (disabled : body.profile.evaluate feature = false) (pc : Nat)
    (args rest : List Value) (frame : Frame) (memory : Memory) :
    step body (.feature feature) pc args frame rest memory =
      .ok (.next (pc + 1) (.scalar (.i32 0) :: rest) frame memory) := by
  rw [feature_step, disabled]; rfl

private theorem branch_zero (body : CIL.Method) (pc target : Nat)
    (args rest : List Value) (frame : Frame) (memory : Memory) :
    step body (.brzero target) pc args frame (.scalar (.i32 0) :: rest) memory =
      .ok (.next target rest frame memory) := rfl

theorem scalar_word_invoke (profile : CIL.FeatureProfile)
    (bmi : profile.bmi2 = false) (arm : profile.armBase64 = false)
    (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (scalarWordBody profile))
    (memory : Memory) (a b : BitVec 64) (output : Reference)
    (wf : memory.WellFormed) (writable : access memory output 8 1 true = .ok ()) :
    ∃ final,
      invoke program 9 index [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)] memory =
        .ok (final, [.scalar (.i64 (highProduct a b))]) ∧
      final.WellFormed ∧
      read final output 8 1 = .ok (numberBytes (lowProduct a b).toNat 8) ∧
      AccessBelow memory.nextIdentity memory final ∧
      (∀ id offset, id ≠ output.allocation ∨ offset < output.offset ∨ output.offset + 8 ≤ offset →
        final.cells id offset = memory.cells id offset) := by
  let args : List Value := [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)]
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have formed := access_reference_valid _ _ _ _ _ writable
  have length : (numberBytes (lowProduct a b).toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨final, written⟩ := write_succeeds (bytes := numberBytes (lowProduct a b).toNat 8)
    (by simpa only [length] using writable)
  have loaded := write_readback _ _ _ _ _ written
  rw [length] at loaded
  refine ⟨final, ?_, write_preserves_wellFormed _ _ _ _ _ wf written, loaded,
    write_preserves_access_below written _, ?_⟩
  · have normalized : write memory output (numberBytes (a.toNat * b.toNat % 2^64) 8) 1 = .ok final := by
      simpa only [lowProduct, BitVec.toNat_mul] using written
    apply invoke_of_run found
    · simp [checkedValue, numericValue, formValue, formed, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · rfl
    · change run program 9 index 0 args frame [] memory = _
      iterate 7
        apply Eq.trans
        · apply run_next found
          · simp only [scalarWordBody]; rfl
          · first
            | exact feature_disabled (scalarWordBody profile) .bmi2 bmi _ _ _ _ _
            | exact feature_disabled (scalarWordBody profile) .armBase64 arm _ _ _ _ _
            | exact branch_zero _ _ _ _ _ _ _
            | (simp [step, args, checkedValue, numericValue, formValue, formed, checkedAt,
                 Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
               try exact ⟨rfl, rfl, rfl, rfl⟩
               done)
      apply Eq.trans
      · apply run_next (target := 26) (values := [.scalar (.i64 (highProduct a b))])
          (nextFrame := frame) (updated := final) found (by rfl)
        simp [step, staticInstruction, memoryInstruction, storeValue, referenceAt, normalized,
          BitVec.toNat_mul, CIL.WideMultiply.high64, highProduct, checkedAt,
          Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      · simp [run, found, scalarWordBody, step, highProduct, leaveFrame, frame, checkedValue, numericValue,
          Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · intro id offset outside
    apply write_outside _ _ _ _ _ _ _ written
    simpa only [length] using outside

#print axioms scalar_word_invoke
end UInt256Proof.Multiply
