import UInt256.Methods.Subtract.ScalarDispatchWith

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety

/-- StoreLimbs taking its words high first: argument 4 lands at offset 0, argument 1 at offset 24. -/
def reversedStorageBody (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile := profile, locals := [], returnsValue := false, code := [
    .arg 0, .skipInit, .arg 0, .fieldAddress 0, .memory .asRef, .arg 4, .store64,
    .arg 0, .fieldAddress 8, .memory .asRef, .arg 3, .store64,
    .arg 0, .fieldAddress 16, .memory .asRef, .arg 2, .store64,
    .arg 0, .fieldAddress 24, .memory .asRef, .arg 1, .store64, .ret] }

/-- The reversed limb storage body is checked once, with the forward write lemma for the same words. -/
theorem reversed_store_limbs_safe (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (reversedStorageBody profile))
    (memory : Memory) (inputs : List Reference) (output : Reference)
    (w0 w1 w2 w3 : BitVec 64)
    (call : CallingConditions program memory inputs [output]) :
    ∃ result,
      invoke program 23 index (UInt256Proof.Multiply.LimbStorage.arguments output w3 w2 w1 w0) memory =
        .ok (result, []) ∧
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
  have l1 := c1.output_limb_formed (by simp : output ∈ [output]) 1
  have l2 := c2.output_limb_formed (by simp : output ∈ [output]) 2
  have l3 := c3.output_limb_formed (by simp : output ∈ [output]) 3
  have a0 := call.output_limb_address (by simp : output ∈ [output]) 0
  have a1 := c1.output_limb_address (by simp : output ∈ [output]) 1
  have a2 := c2.output_limb_address (by simp : output ∈ [output]) 2
  have a3 := c3.output_limb_address (by simp : output ∈ [output]) 3
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, CIL.fin_val_three, Nat.reduceMul, Nat.add_zero] at a0 a1 a2 a3 h0 l1 l2 l3
  apply invoke_of_run found
  · simp [UInt256Proof.Multiply.LimbStorage.arguments, checkedValue, numericValue, formValue, checkedAt, f0,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · rfl
  · iterate 22
      apply Eq.trans
      · apply run_next found
        · simp only [reversedStorageBody]; rfl
        · limb_storage_step f0, f1, f2, f3, l1, l2, l3, a0, a1, a2, a3, h0, h1, h2, h3
          try exact ⟨rfl, rfl, rfl, rfl⟩
          done
    simp [run, found, reversedStorageBody, step, leaveFrame, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem reversed_store_limbs_readable_contract (profile : CIL.FeatureProfile)
    (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (reversedStorageBody profile))
    (memory : Memory) (inputs : List Reference) (output : Reference)
    (w0 w1 w2 w3 : BitVec 64)
    (call : CallingConditions program memory inputs [output]) :
    ∃ fuel result,
      invoke program fuel index (UInt256Proof.Multiply.LimbStorage.arguments output w3 w2 w1 w0) memory =
        .ok (result, []) ∧
      CallingConditions program result inputs [output] ∧
      (∀ id offset, OutsideOutput output id offset → result.cells id offset = memory.cells id offset) ∧
      AccessBelow memory.nextIdentity memory result ∧
      inputValue result output = BitVec.ofNat 256
        (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192) ∧
      (∃ bytes, read result output 32 1 = .ok bytes) := by
  obtain ⟨result, executed, valid, outside, authority, r0, r1, r2, r3⟩ :=
    reversed_store_limbs_safe profile program index found memory inputs output w0 w1 w2 w3 call
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

#print axioms reversed_store_limbs_safe
#print axioms reversed_store_limbs_readable_contract
end UInt256Proof.Subtract.Profile
