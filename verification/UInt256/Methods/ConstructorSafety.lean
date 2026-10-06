import Extracted
import UInt256.Safety.FourLimbWrites
import UInt256.Safety.OutputLoad

namespace UInt256Proof.ConstructorSafety

open CIL.Safety UInt256Model.Safety

def constructorIndex : Nat := Extracted.program.findIdx fun body =>
  body.code.any fun op => match op with | .setField _ => true | _ => false

def constructorBody : CIL.Method := Extracted.program[constructorIndex]?.getD
  { code := [], locals := [], returnsValue := false }

/-- A checked execution of the current extracted storage helper. This theorem
    supplies no arithmetic summary for unexamined helper code. -/
theorem constructor_safe (memory : Memory) (inputs : List Reference) (output : Reference)
    (w0 w1 w2 w3 : BitVec 64)
    (call : CallingConditions Extracted.program memory inputs [output]) :
    ∃ fuel result,
      invoke Extracted.program fuel constructorIndex
        [.reference (.address output), .scalar (.i64 w0), .scalar (.i64 w1), .scalar (.i64 w2), .scalar (.i64 w3)]
        memory = .ok (result, []) ∧
      CallingConditions Extracted.program result inputs [output] ∧
      (∀ id offset, OutsideOutput output id offset → result.cells id offset = memory.cells id offset) ∧
      AccessBelow memory.nextIdentity memory result ∧
      read result output 8 1 = .ok (numberBytes w0.toNat 8) ∧
      read result { output with offset := output.offset + 8 } 8 1 = .ok (numberBytes w1.toNat 8) ∧
      read result { output with offset := output.offset + 16 } 8 1 = .ok (numberBytes w2.toNat 8) ∧
      read result { output with offset := output.offset + 24 } 8 1 = .ok (numberBytes w3.toNat 8) := by
  obtain ⟨m1, m2, m3, m4, h0, h1, h2, h3, c1, c2, c3, c4, outside, authority, reads⟩ :=
    write_four_limbs Extracted.program memory inputs output w0 w1 w2 w3 call
  refine ⟨constructorBody.code.length + 1, m4, ?_, c4, outside, authority, reads⟩
  have f0 := call.output_formed (by simp : output ∈ [output])
  have f1 := c1.output_formed (by simp : output ∈ [output])
  have f2 := c2.output_formed (by simp : output ∈ [output])
  have f3 := c3.output_formed (by simp : output ∈ [output])
  have a0 := call.output_limb_address (by simp : output ∈ [output]) 0
  have a1 := c1.output_limb_address (by simp : output ∈ [output]) 1
  have a2 := c2.output_limb_address (by simp : output ∈ [output]) 2
  have a3 := c3.output_limb_address (by simp : output ∈ [output]) 3
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, CIL.fin_val_three, Nat.reduceMul, Nat.add_zero] at a0 a1 a2 a3 h0
  conv in constructorIndex => cbv
  conv in constructorBody => cbv
  simp [invoke, cil_code, enterFrame, makeLocals, makeArgumentHomes,
    checkedValue, numericValue, formValue, checkedAt, f0, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  repeat'
    rw [run]
    simp (config := { implicitDefEqProofs := false }) [cil_code, CIL.fin_val_three, step, checkedValue, numericValue, formValue, checkedAt,
      pureArity, instruction, storeValue, referenceAt, leaveFrame,
      f0, f1, f2, f3, a0, a1, a2, a3, h0, h1, h2, h3,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
#print axioms constructor_safe

end UInt256Proof.ConstructorSafety

namespace UInt256Proof.ConstructorSafety

open CIL.Safety UInt256Model.Safety

/-- Safety and the mathematical output describe the same extracted invocation. -/
theorem constructor_contract (memory : Memory) (inputs : List Reference) (output : Reference)
    (w0 w1 w2 w3 : BitVec 64)
    (call : CallingConditions Extracted.program memory inputs [output]) :
    ∃ fuel result,
      invoke Extracted.program fuel constructorIndex
        [.reference (.address output), .scalar (.i64 w0), .scalar (.i64 w1), .scalar (.i64 w2), .scalar (.i64 w3)]
        memory = .ok (result, []) ∧
      CallingConditions Extracted.program result inputs [output] ∧
      (∀ id offset, OutsideOutput output id offset → result.cells id offset = memory.cells id offset) ∧
      AccessBelow memory.nextIdentity memory result ∧
      inputValue result output = BitVec.ofNat 256
        (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192) ∧
      loadValue result (.address output) 32 = .ok (.v256 (BitVec.ofNat 256
        (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192))) := by
  obtain ⟨fuel, result, executed, valid, outside, authority, r0, r1, r2, r3⟩ :=
    constructor_safe memory inputs output w0 w1 w2 w3 call
  exact ⟨fuel, result, executed, valid, outside, authority,
    output_value_of_limb_reads result output w0 w1 w2 w3 r0 r1 r2 r3,
    output_load_of_limb_reads result output w0 w1 w2 w3
      (valid.1.2.2 (wordView output) (by simp)) r0 r1 r2 r3⟩

#print axioms constructor_contract

end UInt256Proof.ConstructorSafety
