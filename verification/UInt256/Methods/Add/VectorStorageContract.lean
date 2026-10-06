import UInt256.Methods.Add.StorageSafety
import UInt256.Safety.OutputAccess
import UInt256.Safety.ArgumentValues
import UInt256.Safety.CallerSetup
import UInt256.VectorRepresentation
import CIL.Safety.AccessBelow
import CIL.Safety.StepComposition

namespace UInt256Proof.Safety
open CIL.Safety UInt256Model.Safety

theorem vector_store_limbs_readable_contract (memory : Memory) (inputs : List Reference) (output : Reference)
    (w0 w1 w2 w3 : BitVec 64)
    (call : CallingConditions Extracted.program memory inputs [output])
    (vector : vectorStorage = true) :
    ∃ fuel result,
      invoke Extracted.program fuel storageIndex
        (storageArguments output w0 w1 w2 w3)
        memory = .ok (result, []) ∧
      CallingConditions Extracted.program result inputs [output] ∧
      (∀ id offset, OutsideOutput output id offset → result.cells id offset = memory.cells id offset) ∧
      AccessBelow memory.nextIdentity memory result ∧
      inputValue result output = BitVec.ofNat 256
        (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192) ∧
      (∃ bytes, read result output 32 1 = .ok bytes) := by
  first
  | exact False.elim (Bool.noConfusion ((by rfl : vectorStorage = false).symm.trans vector))
  |
    let packed := CIL.Vector.pack256 w0 w1 w2 w3
    have length : (numberBytes packed.toNat 32).length = 32 := by simp [numberBytes]
    obtain ⟨after, written, valid, outside, loaded⟩ :=
      call.write_output_slice (by simp : output ∈ [output]) 0 (numberBytes packed.toNat 32)
        (by rw [length]; decide) (by rw [length]; decide)
    simp only [Nat.add_zero, length] at written loaded
    refine ⟨14, after, ?_, valid, outside, write_preserves_access_below written _, ?_, ⟨_, loaded⟩⟩
    · have formed := call.output_formed (by simp : output ∈ [output])
      have created : CIL.evalIntrinsic (.vector (.create64 256))
          [.i64 w0, .i64 w1, .i64 w2, .i64 w3] = some (.v256 packed) := rfl
      conv in (storageArguments _ _ _ _ _) => cbv
      conv in storageIndex => cbv
      simp [invoke, cil_code, enterFrame, makeLocals, makeArgumentHomes,
        checkedValue, numericValue, formValue, checkedAt, formed, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
      have found : Extracted.program[storageIndex]? = some storageBody := by rfl
      have profile : storageBody.profile = Extracted.profile := by rfl
      repeat'
        first
        | apply Eq.trans
          · apply run_next found (by rfl)
            simp (config := { implicitDefEqProofs := false })
              [cil_code, profile, Extracted.profile, step, checkedValue, numericValue, formValue, checkedAt, formed,
                pureArity, scalars, CIL.step, CIL.FeatureProfile.evaluate,
                instruction, staticInstruction, memoryInstruction, storeValue, referenceAt,
                CIL.Intrinsic.available, created, written,
                Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
        | solve
          | conv in storageIndex => cbv
            simp [run, cil_code, step, leaveFrame, checkedValue, numericValue,
              Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · rw [inputValue_of_encoded_read loaded]
      apply BitVec.eq_of_toNat_eq
      have bound := packed.isLt
      simp only [packed, UInt256Proof.pack256_number] at bound ⊢
      rw [BitVec.toNat_ofNat]
      simp only [Nat.mul_add] at bound ⊢
      omega

theorem vector_store_limbs_contract (memory : Memory) (inputs : List Reference) (output : Reference)
    (w0 w1 w2 w3 : BitVec 64)
    (call : CallingConditions Extracted.program memory inputs [output])
    (vector : vectorStorage = true) :
    ∃ fuel result,
      invoke Extracted.program fuel storageIndex
        (storageArguments output w0 w1 w2 w3)
        memory = .ok (result, []) ∧
      CallingConditions Extracted.program result inputs [output] ∧
      (∀ id offset, OutsideOutput output id offset → result.cells id offset = memory.cells id offset) ∧
      AccessBelow memory.nextIdentity memory result ∧
      inputValue result output = BitVec.ofNat 256
        (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192) := by
  obtain ⟨fuel, result, executed, valid, outside, authority, value, _⟩ :=
    vector_store_limbs_readable_contract memory inputs output w0 w1 w2 w3 call vector
  exact ⟨fuel, result, executed, valid, outside, authority, value⟩

#print axioms vector_store_limbs_readable_contract
#print axioms vector_store_limbs_contract
end UInt256Proof.Safety
