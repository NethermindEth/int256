import UInt256.Methods.Add.Vector128Decision

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- The fast suffix returns the saved high-lane carry bit and retires its frame.
    The arithmetic meaning of this flag is established separately from stepping. -/
theorem vector128_fast_return (memory : Memory) (frame : Frame) (args : List Value)
    (home : Reference) (mask : BitVec 128)
    (slot : frame.locals[7]? = some (.bytes .vector128 home))
    (loaded : read memory home 16 1 = .ok (numberBytes mask.toNat 16)) :
    run Extracted.program 7 vector128Index 215 args frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if CIL.Vector.lane64 mask 1 > BitVec.ofNat 64 0 then 1 else 0))]) := by
  have load := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 mask) mask.toNat rfl slot loaded
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  have profile : vector128Body.profile = Extracted.profile := by rfl
  have returns : vector128Body.returnsValue = true := by rfl
  iterate 6
    apply Eq.trans
    · apply run_next found (by rfl)
      first
      | exact load _ _
      | (simp (config := { implicitDefEqProofs := false })
          [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.binary,
            CIL.Intrinsic.available, CIL.Vector.intrinsic_extract128,
            checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
         first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)
  have fetched : vector128Body.code[221]? = some .ret := by rfl
  simp [run, found, fetched, returns, step, checkedValue, numericValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms vector128_fast_return
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def vector128FastOutputStart : Nat := if Extracted.profile.advSimd then 215 else 206

/-- SSE writes the saved result halves on the fast path; ARM has already
    written them. Both paths preserve private snapshots and caller footprint.
    ARM supplies the already-written halves; the result is unconditional. -/
theorem vector128_fast_output (original entered current : Memory)
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
    (earlyRead : Extracted.profile.advSimd = true →
      read current output 16 1 = .ok (numberBytes low.toNat 16) ∧
      read current { output with offset := output.offset + 16 } 16 1 = .ok (numberBytes high.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      (read after output 16 1 = .ok (numberBytes low.toNat 16) ∧
        read after { output with offset := output.offset + 16 } 16 1 = .ok (numberBytes high.toNat 16)) →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = current.cells id offset) →
      (∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
        read current reference width alignment = .ok bytes → read after reference width alignment = .ok bytes) →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index 215 args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index vector128FastOutputStart args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  first
  | have disabled : Extracted.profile.advSimd = true := by rfl
    exact continuation current (earlyRead disabled)
      currentCall authority (by intros; rfl) (by intros; assumption) (Nat.le_refl _)
  | obtain ⟨middle, after, firstWrite, secondWrite, firstRead, secondRead, middleCall, afterCall,
        afterAuthority, outside, privateReads, advanced⟩ :=
      output_halves_update Extracted.program original entered current inputs outputs output low high
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
    have formed := currentCall.output_formed member
    have address := middleCall.output_half_address member 1
    simp only [Fin.val_one, Nat.mul_one] at address
    have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
    conv in vector128FastOutputStart => cbv
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

/-- Follow the actual fast-path feature guard before selecting output stores. -/
theorem vector128_fast_output_dispatch (memory : Memory) (frame : Frame) (args : List Value)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel vector128Index vector128FastOutputStart args frame [] memory =
        .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 204 args frame [] memory =
        .ok (result, returned) ∧ post result returned := by
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  have profile : vector128Body.profile = Extracted.profile := by rfl
  conv at continuation in vector128FastOutputStart => cbv
  repeat' first
    | exact continuation
    | (apply run_next_exists post found (by rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.FeatureProfile.evaluate,
           numericValue, checkedValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

#print axioms vector128_fast_output
#print axioms vector128_fast_output_dispatch
end UInt256Proof.Add.Safety
