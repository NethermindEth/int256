import UInt256.Methods.Add.VectorSafetyOutput

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def propagationMask (sum : BitVec 256) : BitVec 256 :=
  CIL.Vector.zip256 (fun x y => CIL.Vector.mask64 (x == y)) sum (~~~(BitVec.ofNat 256 0))

/-- The propagation test reads the saved lane sums after the caller-output write.
    Its initialized snapshot must therefore be preserved by that write. -/
theorem vector_propagation_checked (original entered current : Memory)
    (inputs outputs : List Reference) (sum propagation : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (sumMember : sum ∈ outputs) (propagationMember : propagation ∈ outputs)
    (authority : AccessBelow entered.nextIdentity entered current)
    (sumArgument : args[3]? = some (.reference (.address sum)))
    (propagationArgument : args[6]? = some (.reference (.address propagation)))
    (sumValue : BitVec 256)
    (sumRead : read current sum 32 1 = .ok (numberBytes sumValue.toNat 32))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      write current propagation (numberBytes (propagationMask sumValue).toNat 32) 1 = .ok after →
      read after propagation 32 1 = .ok (numberBytes (propagationMask sumValue).toNat 32) →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, OutsideOutput propagation id offset → after.cells id offset = current.cells id offset) →
      (∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
        read current reference width alignment = .ok bytes → read after reference width alignment = .ok bytes) →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vectorIndex (vectorOutputStart + 16) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex (vectorOutputStart + 10) args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨after, written, readback, afterCall, afterAuthority, outside, privateReads, advanced⟩ :=
    vector_output_update original entered current inputs outputs propagation (propagationMask sumValue)
      call currentCall propagationMember authority
  have done := continuation after written readback afterCall afterAuthority outside privateReads advanced
  simp [propagationMask] at written
  have sumFormed := currentCall.output_formed sumMember
  have propagationFormed := currentCall.output_formed propagationMember
  have reading := vector_load_snapshot current sum sumValue sumRead
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have profile : vectorBody.profile = Extracted.profile := by rfl
  conv at done in vectorOutputStart => cbv
  conv in vectorOutputStart => cbv
  repeat' first
    | exact done
    | (apply run_next_exists post found (by rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, profile, cil_code, sumArgument, propagationArgument, sumFormed, propagationFormed, reading,
           pureArity, scalars, CIL.step, CIL.Intrinsic.available, propagationMask,
           CIL.Vector.intrinsic_ones256, CIL.Vector.intrinsic_eq256,
           checkedValue, numericValue, formValue, staticInstruction, memoryInstruction,
           storeValue, referenceAt, written, checkedAt, Except.mapError,
           Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

theorem vector_prepare_return (memory : Memory) (frame : Frame) (args : List Value) :
    run Extracted.program 1 vectorIndex (vectorOutputStart + 16) args frame [] memory =
      .ok (leaveFrame frame memory, []) := by
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have fetched : vectorBody.code[vectorOutputStart + 16]? = some .ret := by rfl
  have returns : vectorBody.returnsValue = false := by rfl
  simp [run, found, fetched, returns, step, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms vector_propagation_checked
#print axioms vector_prepare_return
end UInt256Proof.Add.Safety
