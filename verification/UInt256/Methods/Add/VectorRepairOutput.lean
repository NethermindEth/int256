import UInt256.Methods.Add.VectorRepairLookup
import UInt256.Methods.AddSubtract.VectorOutputMemory

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Store the corrected sum from a by-value argument and the initialized table
    vector, without rereading either original input. -/
theorem repair_output_checked (original entered current : Memory)
    (inputs outputs : List Reference) (output correction : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (outputMember : output ∈ outputs)
    (authority : AccessBelow entered.nextIdentity entered current)
    (outputArgument : args[3]? = some (.reference (.address output)))
    (sumValue correctionValue : BitVec 256)
    (sumArgument : args[0]? = some (.scalar (.v256 sumValue)))
    (correctionSlot : frame.locals[2]? = some (.bytes .vector256 correction))
    (correctionRead : read current correction 32 1 = .ok (numberBytes correctionValue.toNat 32))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      write current output (numberBytes (CIL.Vector.zip256 (· + ·) sumValue correctionValue).toNat 32) 1 = .ok after →
      read after output 32 1 = .ok (numberBytes (CIL.Vector.zip256 (· + ·) sumValue correctionValue).toNat 32) →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = current.cells id offset) →
      (∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
        read current reference width alignment = .ok bytes → read after reference width alignment = .ok bytes) →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel repairIndex 38 args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel repairIndex 32 args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨after, written, readback, afterCall, afterAuthority, outside, privateReads, advanced⟩ :=
    vector_output_update original entered current inputs outputs output
      (CIL.Vector.zip256 (· + ·) sumValue correctionValue) call currentCall outputMember authority
  have done := continuation after written readback afterCall afterAuthority outside privateReads advanced
  have outputFormed := currentCall.output_formed outputMember
  have loadCorrection := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := repairBody) (args := args) (pc := pc) (stack := stack)
    .vector256 (.v256 correctionValue) correctionValue.toNat rfl correctionSlot correctionRead
  have found : Extracted.program[repairIndex]? = some repairBody := by rfl
  have profile : repairBody.profile = Extracted.profile := by rfl
  repeat' first
    | exact done
    | (apply run_next_exists post found (by rfl)
       first
       | exact loadCorrection _ _
       | (simp (config := { implicitDefEqProofs := false })
         [step, profile, cil_code, outputArgument, sumArgument, outputFormed,
           pureArity, scalars, CIL.step, CIL.Intrinsic.available, CIL.Vector.intrinsic_add256,
           checkedValue, numericValue, formValue, instruction, staticInstruction, memoryInstruction,
           storeValue, referenceAt, written, checkedAt, Except.mapError,
           Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

theorem repair_return (memory : Memory) (frame : Frame) (args : List Value)
    (sumHome : Reference) (sum : BitVec 32)
    (slot : frame.locals[0]? = some (.bytes .word32 sumHome))
    (loaded : read memory sumHome 4 1 = .ok (numberBytes sum.toNat 4)) :
    run Extracted.program 6 repairIndex 38 args frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (if sum &&& 16 > 0 then 1 else 0))]) := by
  have loadSum := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := repairBody) (args := args) (pc := pc) (stack := stack)
    .word32 (.i32 sum) sum.toNat rfl slot loaded
  have found : Extracted.program[repairIndex]? = some repairBody := by rfl
  have returns : repairBody.returnsValue = true := by rfl
  iterate 5
    apply Eq.trans
    · apply run_next found (by rfl)
      first
      | exact loadSum _ _
      | (simp (config := { implicitDefEqProofs := false })
          [step, pureArity, scalars, CIL.step, CIL.binary, checkedValue, numericValue,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
         first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)
  have fetched : repairBody.code[43]? = some .ret := by rfl
  simp [run, found, fetched, returns, step, checkedValue, numericValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms repair_return
#print axioms repair_output_checked
end UInt256Proof.Add.Safety
