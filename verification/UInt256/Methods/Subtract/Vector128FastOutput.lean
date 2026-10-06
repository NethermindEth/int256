import UInt256.Methods.Subtract.Vector128FastReturn
import UInt256.Safety.OutputHalves

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Store both corrected halves while preserving private snapshots and caller bytes outside output. -/
theorem vector128_fast_output (original entered current : Memory)
    (inputs outputs : List Reference) (output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (member : output ∈ outputs) (authority : AccessBelow entered.nextIdentity entered current)
    (argument : args[2]? = some (.reference (.address output)))
    (low high incomingLow incomingHigh : BitVec 128)
    (lowHome highHome incomingLowHome incomingHighHome : Reference)
    (lowSlot : frame.locals[5]? = some (.bytes .vector128 lowHome))
    (highSlot : frame.locals[6]? = some (.bytes .vector128 highHome))
    (highBound : original.nextIdentity ≤ highHome.allocation)
    (lowRead : read current lowHome 16 1 = .ok (numberBytes low.toNat 16))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (incomingLowSlot : frame.locals[9]? = some (.bytes .vector128 incomingLowHome))
    (incomingHighSlot : frame.locals[10]? = some (.bytes .vector128 incomingHighHome))
    (incomingHighBound : original.nextIdentity ≤ incomingHighHome.allocation)
    (incomingLowRead : read current incomingLowHome 16 1 = .ok (numberBytes incomingLow.toNat 16))
    (incomingHighRead : read current incomingHighHome 16 1 = .ok (numberBytes incomingHigh.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      (read after output 16 1 = .ok (numberBytes (CIL.Vector.zip128 (· + ·) low incomingLow).toNat 16) ∧
        read after { output with offset := output.offset + 16 } 16 1 = .ok (numberBytes (CIL.Vector.zip128 (· + ·) high incomingHigh).toNat 16)) →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = current.cells id offset) →
      (∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
        read current reference width alignment = .ok bytes → read after reference width alignment = .ok bytes) →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index 134 args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 119 args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨middle, after, firstWrite, secondWrite, firstRead, secondRead, middleCall, afterCall,
      afterAuthority, outside, privateReads, advanced⟩ :=
    output_halves_update Extracted.program original entered current inputs outputs output (CIL.Vector.zip128 (· + ·) low incomingLow) (CIL.Vector.zip128 (· + ·) high incomingHigh)
      call currentCall member authority
  have done := continuation after ⟨firstRead, secondRead⟩ afterCall afterAuthority outside
    (fun reference width alignment bytes bound loaded => (privateReads reference width alignment bytes bound loaded).2) advanced
  have loadLow := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 low) low.toNat rfl lowSlot lowRead
  have loadHigh := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 high) high.toNat rfl highSlot
    (privateReads highHome 16 1 _ highBound highRead).1
  have loadIncomingLow := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 incomingLow) incomingLow.toNat rfl incomingLowSlot incomingLowRead
  have loadIncomingHigh := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 incomingHigh) incomingHigh.toNat rfl incomingHighSlot
    (privateReads incomingHighHome 16 1 _ incomingHighBound incomingHighRead).1
  have formed := currentCall.output_formed member
  have address := middleCall.output_half_address member 1
  simp only [Fin.val_one, Nat.mul_one] at address
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  repeat' first
    | exact done
    | (apply run_next_exists post found (by rfl)
       first
       | exact loadLow _ _
       | exact loadHigh _ _
       | exact loadIncomingLow _ _
       | exact loadIncomingHigh _ _
       | (simp (config := { implicitDefEqProofs := false })
           [step, pureArity, scalars, CIL.step, CIL.Intrinsic.available, CIL.Vector.intrinsic_add128,
             cil_code, numericValue, argument, checkedValue, formValue, formed, instruction, staticInstruction, memoryInstruction,
             storeValue, referenceAt, firstWrite, secondWrite, address, CIL.offsetValue,
             checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))


#print axioms vector128_fast_output
end UInt256Proof.Subtract.Safety
