import UInt256.Methods.StorageScalar
import UInt256.VectorRepresentation
import UInt256.Safety.ArgumentValues

namespace UInt256Proof.StorageVector
open CIL.Safety UInt256Model.Safety

def template (profile : CIL.FeatureProfile) (featureFirst : Bool) (padding : Nat) : CIL.Method :=
  { profile := profile, returnsValue := false, locals := [], code :=
    (if featureFirst then [.feature .vector256Accelerated, .brzero 13, .arg 0, .skipInit]
      else [.arg 0, .skipInit, .feature .vector256Accelerated, .brzero 13]) ++
    [.arg 0, .memory .asRef, .arg 1, .arg 2, .arg 3, .arg 4,
      .intrinsic (.vector (.create64 256)) 4, .memory .store256, .ret] ++
    List.replicate padding (.unsupported "Unreachable under selected profile") }
theorem store_template_contract (profile : CIL.FeatureProfile) (featureFirst : Bool) (padding : Nat)
    (vector : profile.vector256Accelerated = true) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (template profile featureFirst padding))
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
  let frame : Frame := {
        activation := memory.nextIdentity
        locals := []
        owned := []
        arguments := []
        stackBytes := 0 }
  have checked : args.mapM (checkedValue memory) = .ok args := by
    simp [args, StorageScalar.arguments, checkedValue, numericValue, formValue, formed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have setup : enterFrame (template profile featureFirst padding) args memory = .ok (frame, memory) := rfl
  refine ⟨13, after, invoke_of_run found checked setup ?_, valid, outside,
    write_preserves_access_below written _, ?_, ⟨_, loaded⟩⟩
  · cases featureFirst <;>
      cil_checked_steps [found, template, args, StorageScalar.arguments, frame,
        vector, formed, created, written, storeValue, referenceAt, ordinaryAccessAlignment]
  · rw [inputValue_of_encoded_read loaded]
    apply BitVec.eq_of_toNat_eq
    have bound := packed.isLt
    simp only [packed, UInt256Proof.pack256_number] at bound ⊢
    rw [BitVec.toNat_ofNat]
    simp only [Nat.mul_add] at bound ⊢
    omega

def body (profile : CIL.FeatureProfile) := template profile false 20
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
      (∃ bytes, read result output 32 1 = .ok bytes) :=
  store_template_contract profile false 20 vector program index found memory inputs output w0 w1 w2 w3 call
end UInt256Proof.StorageVector
