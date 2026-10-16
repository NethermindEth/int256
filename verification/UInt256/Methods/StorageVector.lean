import UInt256.Methods.StorageScalar
import UInt256.VectorRepresentation
import UInt256.Safety.ArgumentValues

namespace UInt256Proof.StorageVector
open CIL.Safety UInt256Model.Safety

def body (profile : CIL.FeatureProfile) : CIL.Method := { profile := profile, returnsValue := false, locals := [], localKinds := [], parameterHomes := [], staticSites := [], code := [
  .arg 0,
  .skipInit,
  .feature .vector256Accelerated,
  .brzero 13,
  .arg 0,
  .memory .asRef,
  .arg 1,
  .arg 2,
  .arg 3,
  .arg 4,
  .intrinsic (.vector (.create64 256)) 4,
  .memory .store256,
  .ret,
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile"] }

theorem store_limbs_readable_contract (profile : CIL.FeatureProfile)
    (vector : profile.vector256Accelerated = true) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (body profile))
    (memory : Memory) (inputs : List Reference) (output : Reference)
    (w0 w1 w2 w3 : BitVec 64)
    (call : CallingConditions program memory inputs [output]) :
    ∃ fuel result,
      invoke program fuel index (StorageScalar.arguments output w0 w1 w2 w3) memory = .ok (result, []) ∧
      CallingConditions program result inputs [output] ∧
      (∀ id offset, OutsideOutput output id offset → result.cells id offset = memory.cells id offset) ∧
      AccessBelow memory.nextIdentity memory result ∧
      inputValue result output = BitVec.ofNat 256
        (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192) ∧
      (∃ bytes, read result output 32 1 = .ok bytes) := by
  let packed := CIL.Vector.pack256 w0 w1 w2 w3
  have length : (numberBytes packed.toNat 32).length = 32 := by simp [numberBytes]
  obtain ⟨after, written, valid, outside, loaded⟩ :=
    call.write_output_slice (by simp : output ∈ [output]) 0 (numberBytes packed.toNat 32)
      (by rw [length]; decide) (by rw [length]; decide)
  simp only [Nat.add_zero, length] at written loaded
  have formed := call.output_formed (by simp : output ∈ [output])
  have created : CIL.evalIntrinsic (.vector (.create64 256))
      [.i64 w0, .i64 w1, .i64 w2, .i64 w3] = some (.v256 packed) := rfl
  let args := StorageScalar.arguments output w0 w1 w2 w3
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have checked : args.mapM (checkedValue memory) = .ok args := by
    simp [args, StorageScalar.arguments, checkedValue, numericValue, formValue, formed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have setup : enterFrame (body profile) args memory = .ok (frame, memory) := rfl
  have enabled (pc : Nat) (stack : List Value) :
      step (body profile) (.feature .vector256Accelerated) pc args frame stack memory =
        .ok (.next (pc + 1) (.scalar (.i32 1) :: stack) frame memory) := by
    change Except.ok (FrameAction.next (pc + 1)
      (.scalar (.i32 (if profile.vector256Accelerated then 1 else 0)) :: stack) frame memory) = _
    rw [vector]
    rfl
  refine ⟨13, after, invoke_of_run found checked setup ?_, valid, outside,
    write_preserves_access_below written _, ?_, ⟨_, loaded⟩⟩
  · iterate 11
      apply Eq.trans
      · apply run_next found (by rfl)
        first
        | exact enabled _ _
        | rfl
        | (simp (config := { implicitDefEqProofs := false }) only
            [List.drop, List.getElem?_cons_zero, StorageScalar.arguments, step, checkedValue, formValue, checkedAt, formed, pureArity, instruction, staticInstruction, memoryInstruction, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
           first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)
    change run program 2 index 11 args frame [.scalar (.v256 packed), .reference (.address output)] memory = _
    apply Eq.trans
    · apply run_next (target := 12) (values := []) (nextFrame := frame) (updated := after) found (by rfl)
      simp only [step, staticInstruction, memoryInstruction, storeValue, referenceAt, ordinaryAccessAlignment,
        written, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact run_return found (by rfl) (by rfl) (by rfl)
  · rw [inputValue_of_encoded_read loaded]
    apply BitVec.eq_of_toNat_eq
    have bound := packed.isLt
    simp only [packed, UInt256Proof.pack256_number] at bound ⊢
    rw [BitVec.toNat_ofNat]
    simp only [Nat.mul_add] at bound ⊢
    omega

#print axioms store_limbs_readable_contract
end UInt256Proof.StorageVector
