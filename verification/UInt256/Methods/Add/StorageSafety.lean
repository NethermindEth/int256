import UInt256.Safety.StorageSelection
import UInt256.Safety.FourLimbWrites
import CIL.Safety.StepComposition

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

/-- Select proof data from the extracted helper; the execution theorem still
    checks every fetched instruction. -/
def vectorStorage : Bool := storageBody.code.any fun op =>
  match op with | .memory .store256 => true | _ => false

/-- A checked execution of the current extracted storage helper. This theorem
    supplies no arithmetic summary for unexamined helper code. -/
theorem store_limbs_safe (memory : Memory) (inputs : List Reference) (output : Reference)
    (w0 w1 w2 w3 : BitVec 64)
    (call : CallingConditions Extracted.program memory inputs [output])
    (scalar : vectorStorage = false) :
    ∃ fuel result,
      invoke Extracted.program fuel storageIndex
        (storageArguments output w0 w1 w2 w3)
        memory = .ok (result, []) ∧
      CallingConditions Extracted.program result inputs [output] ∧
      (∀ id offset, OutsideOutput output id offset → result.cells id offset = memory.cells id offset) ∧
      AccessBelow memory.nextIdentity memory result ∧
      read result output 8 1 = .ok (numberBytes w0.toNat 8) ∧
      read result { output with offset := output.offset + 8 } 8 1 = .ok (numberBytes w1.toNat 8) ∧
      read result { output with offset := output.offset + 16 } 8 1 = .ok (numberBytes w2.toNat 8) ∧
      read result { output with offset := output.offset + 24 } 8 1 = .ok (numberBytes w3.toNat 8) := by
  first
  | exact False.elim (Bool.noConfusion ((by rfl : vectorStorage = true).symm.trans scalar))
  |
    obtain ⟨m1, m2, m3, m4, h0, h1, h2, h3, c1, c2, c3, c4, outside, authority, reads⟩ :=
      write_four_limbs Extracted.program memory inputs output w0 w1 w2 w3 call
    refine ⟨storageBody.code.length + 1, m4, ?_, c4, outside, authority, reads⟩
    have f0 := call.output_formed (by simp : output ∈ [output])
    have f1 := c1.output_formed (by simp : output ∈ [output])
    have f2 := c2.output_formed (by simp : output ∈ [output])
    have f3 := c3.output_formed (by simp : output ∈ [output])
    have a0 := call.output_limb_address (by simp : output ∈ [output]) 0
    have a1 := c1.output_limb_address (by simp : output ∈ [output]) 1
    have a2 := c2.output_limb_address (by simp : output ∈ [output]) 2
    have a3 := c3.output_limb_address (by simp : output ∈ [output]) 3
    have l1 := c1.output_limb_formed (by simp : output ∈ [output]) 1
    have l2 := c2.output_limb_formed (by simp : output ∈ [output]) 2
    have l3 := c3.output_limb_formed (by simp : output ∈ [output]) 3
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, CIL.fin_val_three, Nat.reduceMul, Nat.add_zero] at a0 a1 a2 a3 l1 l2 l3 h0
    conv in storageBody.code.length => cbv
    conv in storageIndex => cbv
    conv in (storageArguments _ _ _ _ _) => cbv
    simp [invoke, cil_code, enterFrame, makeLocals, makeArgumentHomes,
      checkedValue, numericValue, formValue, checkedAt, f0, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    have found : Extracted.program[storageIndex]? = some storageBody := by rfl
    have profile : storageBody.profile = Extracted.profile := by rfl
    repeat'
      first
      | apply Eq.trans
        · apply run_next found (by rfl)
          simp (config := { implicitDefEqProofs := false })
            [cil_code, profile, Extracted.profile, CIL.fin_val_three, step, checkedValue, numericValue, formValue, checkedAt,
              pureArity, scalars, CIL.step, CIL.FeatureProfile.evaluate,
              instruction, staticInstruction, memoryInstruction, CIL.offsetValue, storeValue, referenceAt,
              f0, f1, f2, f3, a0, a1, a2, a3, l1, l2, l3, h0, h1, h2, h3,
              Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
      | solve
        | conv in storageIndex => cbv
          simp [run, cil_code, step, leaveFrame, checkedValue, numericValue,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
#print axioms store_limbs_safe

end UInt256Proof.Safety
