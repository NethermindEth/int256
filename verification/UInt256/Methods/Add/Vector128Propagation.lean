import UInt256.Methods.Add.Vector128Snapshots
import UInt256.Safety.OutputHalves

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def vector128EarlyOutputStart : Nat := if Extracted.profile.advSimd then 73 else 82

/-- SkipInit checks the output reference but neither initializes nor reads its
    bytes. The extracted feature guard selects ARM's early stores or SSE's skip. -/
theorem vector128_output_dispatch (memory : Memory) (output : Reference)
    (frame : Frame) (args : List Value)
    (argument : args[2]? = some (.reference (.address output)))
    (formed : form memory output = .ok output)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel vector128Index vector128EarlyOutputStart args frame [] memory =
        .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 69 args frame [] memory =
        .ok (result, returned) ∧ post result returned := by
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  have profile : vector128Body.profile = Extracted.profile := by rfl
  conv at continuation in vector128EarlyOutputStart => cbv
  repeat' first
    | exact continuation
    | (apply run_next_exists post found (by rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, profile, cil_code, argument, checkedValue, formValue, formed, instruction,
           pureArity, scalars, CIL.step, CIL.FeatureProfile.evaluate,
           numericValue, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

#print axioms vector128_output_dispatch
end UInt256Proof.Add.Safety

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

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Execution from helper entry through the ISA-dependent early output stage.
    Saved operands remain initial-value snapshots even after overlapping writes. -/
theorem vector128_output_prefix (original entered : Memory)
    (inputs outputs : List Reference) (left right output : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (setup : enterFrame vector128Body args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity vector128Specs slots)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs) (outputMember : output ∈ outputs)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (outputArg : args[2]? = some (.reference (.address output)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      (∀ i : Fin 11, ∃ reference,
        slots[i.val]? = some (.bytes .vector128 reference) ∧
        read after reference 16 1 = .ok (numberBytes (vector128SnapshotValue original left right i).toNat 16)) →
      (Extracted.profile.advSimd = true →
        read after output 16 1 = .ok (numberBytes (vector128SnapshotValue original left right 9).toNat 16) ∧
        read after { output with offset := output.offset + 16 } 16 1 =
          .ok (numberBytes (vector128SnapshotValue original left right 10).toNat 16)) →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        after.cells id offset = original.cells id offset) →
      entered.nextIdentity ≤ after.nextIdentity →
      (Extracted.profile.advSimd = false → MemoryBelow original.nextIdentity original after) →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index 82 args (vector128SavedFrame frame slots right) [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 0 args frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  apply vector128_snapshots_checked original entered inputs outputs left right frame slots args call setup
    layout homes leftMember rightMember leftArg rightArg post
  intro current snapshots preserved currentCall authority advanced
  obtain ⟨lowHome, lowSlot, lowRead⟩ := snapshots 9
  obtain ⟨highHome, highSlot, highRead⟩ := snapshots 10
  change slots[9]? = some (.bytes .vector128 lowHome) at lowSlot
  change slots[10]? = some (.bytes .vector128 highHome) at highSlot
  have actualLow : (vector128SavedFrame frame slots right).locals[10]? = some (.bytes .vector128 lowHome) := by
    simpa [vector128SavedFrame] using lowSlot
  have actualHigh : (vector128SavedFrame frame slots right).locals[11]? = some (.bytes .vector128 highHome) := by
    simpa [vector128SavedFrame] using highSlot
  apply vector128_output_dispatch current output (vector128SavedFrame frame slots right) args outputArg
    (currentCall.output_formed outputMember) post
  apply vector128_early_output original entered current inputs outputs output
    (vector128SavedFrame frame slots right) args call currentCall outputMember authority outputArg
    (vector128SnapshotValue original left right 9) (vector128SnapshotValue original left right 10)
    lowHome highHome actualLow actualHigh (homes.home_bound 10 .vector128 highHome highSlot) lowRead highRead post
  intro after outputRead afterCall afterAuthority outside privateReads next unchanged
  have retained : ∀ i : Fin 11, ∃ reference,
      slots[i.val]? = some (.bytes .vector128 reference) ∧
      read after reference 16 1 = .ok (numberBytes (vector128SnapshotValue original left right i).toNat 16) := by
    intro i
    obtain ⟨reference, slot, loaded⟩ := snapshots i
    exact ⟨reference, slot, privateReads reference 16 1 _
      (homes.home_bound i.val .vector128 reference slot) loaded⟩
  exact continuation after retained outputRead afterCall afterAuthority
    (fun id offset old excluded => (outside id offset excluded).trans (preserved.cells id old offset))
    (Nat.le_trans advanced next)
    (fun disabled => by rw [unchanged disabled]; exact preserved)

#print axioms vector128_output_prefix
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def propagating128 (result incoming : BitVec 128) : BitVec 128 :=
  CIL.Vector.zip128 (fun x y => CIL.Vector.mask64 (x == y)) result 0 &&& incoming

/-- Detect a carry that propagated through a corrected zero lane, using saved
    initialized vectors after any overlapping early output write. -/
theorem vector128_propagation_checked (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (upper : Bool) (result incoming : BitVec 128) (resultHome incomingHome : Reference)
    (resultSlot : frame.locals[if upper then 11 else 10]? = some (.bytes .vector128 resultHome))
    (incomingSlot : frame.locals[if upper then 9 else 8]? = some (.bytes .vector128 incomingHome))
    (resultRead : read current resultHome 16 1 = .ok (numberBytes result.toNat 16))
    (incomingRead : read current incomingHome 16 1 = .ok (numberBytes incoming.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[if upper then 13 else 12]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok (numberBytes (propagating128 result incoming).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (propagating128 result incoming).toNat 16) 1 = .ok after →
      ∃ fuel final returned,
        run Extracted.program fuel vector128Index (if upper then 94 else 88) args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index (if upper then 88 else 82) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have specified : vector128Specs[if upper then 12 else 11]? = some vector128ZeroSpec := by
    cases upper <;> rfl
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store boundary entered current inputs outputs frame root slots layout currentCall
      enteredWF homes authority _ vector128ZeroSpec specified
      (.v128 (propagating128 result incoming)) (propagating128 result incoming).toNat rfl
  have actual : frame.locals[if upper then 13 else 12]? = some (.bytes .vector128 reference) := by
    cases upper <;> exact slot
  have done := continuation reference after actual loaded retained afterCall afterAuthority written
  have loadResult := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 result) result.toNat rfl resultSlot resultRead
  have loadIncoming := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 incoming) incoming.toNat rfl incomingSlot incomingRead
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  have profile : vector128Body.profile = Extracted.profile := by rfl
  cases upper <;> simp only [Bool.false_eq_true, ite_false, ite_true] at stored loadResult loadIncoming done ⊢
  all_goals
    repeat' first
      | exact done
      | (apply run_next_exists post found (by rfl)
         first
         | exact loadResult _ _
         | exact loadIncoming _ _
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.Intrinsic.available,
               CIL.Vector.intrinsic_zero128, CIL.Vector.intrinsic_eq128, CIL.Vector.intrinsic_and128,
               propagating128, checkedValue, numericValue,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_propagation_checked
end UInt256Proof.Add.Safety
