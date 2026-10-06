import UInt256.Methods.Add.Vector128OutputDispatch

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- ARM performs its two early output writes from saved private values; SSE
    reaches the common continuation without a write. Initial caller overlap is
    unrestricted, and all private snapshots survive the ARM stores. -/
theorem vector128_early_output (original entered current : Memory)
    (inputs outputs : List Reference) (output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (member : output ∈ outputs) (authority : AccessBelow entered.nextIdentity entered current)
    (argument : args[2]? = some (.reference (.address output)))
    (low high : BitVec 128) (lowHome highHome : Reference)
    (lowSlot : frame.locals[10]? = some (.bytes .vector128 lowHome))
    (highSlot : frame.locals[11]? = some (.bytes .vector128 highHome))
    (highBound : original.nextIdentity ≤ highHome.allocation)
    (lowRead : read current lowHome 16 1 = .ok (numberBytes low.toNat 16))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      (Extracted.profile.advSimd = true → read after output 16 1 = .ok (numberBytes low.toNat 16) ∧
        read after { output with offset := output.offset + 16 } 16 1 = .ok (numberBytes high.toNat 16)) →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = current.cells id offset) →
      (∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
        read current reference width alignment = .ok bytes → read after reference width alignment = .ok bytes) →
      current.nextIdentity ≤ after.nextIdentity →
      (Extracted.profile.advSimd = false → after = current) →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index 82 args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index vector128EarlyOutputStart args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  first
  | have disabled : Extracted.profile.advSimd = false := by rfl
    exact continuation current (by intro enabled; rw [disabled] at enabled; contradiction)
      currentCall authority (by intros; rfl) (by intros; assumption) (Nat.le_refl _) (fun _ => rfl)
  | obtain ⟨middle, after, firstWrite, secondWrite, firstRead, secondRead, middleCall, afterCall,
        afterAuthority, outside, privateReads, advanced⟩ :=
      output_halves_update Extracted.program original entered current inputs outputs output low high
        call currentCall member authority
    have done := continuation after (fun _ => ⟨firstRead, secondRead⟩) afterCall afterAuthority outside
      (fun reference width alignment bytes bound loaded => (privateReads reference width alignment bytes bound loaded).2) advanced
      (by intro disabled; simp [Extracted.profile] at disabled)
    have loadLow := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := vector128Body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 low) low.toNat rfl lowSlot lowRead
    have loadHigh := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := vector128Body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 high) high.toNat rfl highSlot
      (privateReads highHome 16 1 _ highBound highRead).1
    have formed := currentCall.output_formed member
    have address := middleCall.output_half_address member 1
    simp only [Fin.val_one, Nat.mul_one] at address
    have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
    conv in vector128EarlyOutputStart => cbv
    repeat' first
      | exact done
      | (apply run_next_exists post found (by rfl)
         first
         | exact loadLow _ _
         | exact loadHigh _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, argument, checkedValue, formValue, formed, staticInstruction, memoryInstruction,
               storeValue, referenceAt, firstWrite, secondWrite, address, CIL.offsetValue,
               checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_early_output
end UInt256Proof.Add.Safety
