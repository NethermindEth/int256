import UInt256.Methods.Add.Vector128Propagation

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Compose both propagation masks while retaining every earlier vector home
    and all older caller storage, including ARM's early output readbacks. -/
theorem vector128_propagation_pair (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (low high incomingLow incomingHigh : BitVec 128)
    (lowHome highHome lowIncoming highIncoming : Reference)
    (lowSlot : slots[9]? = some (.bytes .vector128 lowHome))
    (highSlot : slots[10]? = some (.bytes .vector128 highHome))
    (lowIncomingSlot : slots[7]? = some (.bytes .vector128 lowIncoming))
    (highIncomingSlot : slots[8]? = some (.bytes .vector128 highIncoming))
    (lowRead : read current lowHome 16 1 = .ok (numberBytes low.toNat 16))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (lowIncomingRead : read current lowIncoming 16 1 = .ok (numberBytes incomingLow.toNat 16))
    (highIncomingRead : read current highIncoming 16 1 = .ok (numberBytes incomingHigh.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ lowMask highMask after,
      slots[11]? = some (.bytes .vector128 lowMask) →
      slots[12]? = some (.bytes .vector128 highMask) →
      read after lowMask 16 1 = .ok (numberBytes (propagating128 low incomingLow).toNat 16) →
      read after highMask 16 1 = .ok (numberBytes (propagating128 high incomingHigh).toNat 16) →
      (∀ i, i < 11 → ∀ reference bytes,
        slots[i]? = some (.bytes .vector128 reference) →
        read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index 94 args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 82 args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  have actualLow : frame.locals[10]? = some (.bytes .vector128 lowHome) := by simpa [layout] using lowSlot
  have actualHigh : frame.locals[11]? = some (.bytes .vector128 highHome) := by simpa [layout] using highSlot
  have actualLowIncoming : frame.locals[8]? = some (.bytes .vector128 lowIncoming) := by simpa [layout] using lowIncomingSlot
  have actualHighIncoming : frame.locals[9]? = some (.bytes .vector128 highIncoming) := by simpa [layout] using highIncomingSlot
  apply vector128_propagation_checked boundary entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority false low incomingLow lowHome lowIncoming actualLow actualLowIncoming lowRead lowIncomingRead post
  intro lowMask middle lowLocal lowLoaded preserved middleCall middleAuthority firstWrite
  have lowTail : slots[11]? = some (.bytes .vector128 lowMask) := by simpa [layout] using lowLocal
  have savedHigh := vector128_prior_read entered current middle boundary slots homes 10 11 (by decide)
    highHome lowMask highSlot lowTail _ _ firstWrite highRead
  have savedIncoming := vector128_prior_read entered current middle boundary slots homes 8 11 (by decide)
    highIncoming lowMask highIncomingSlot lowTail _ _ firstWrite highIncomingRead
  apply vector128_propagation_checked boundary entered middle inputs outputs frame root slots layout args
    middleCall enteredWF homes middleAuthority true high incomingHigh highHome highIncoming actualHigh actualHighIncoming savedHigh savedIncoming post
  intro highMask after highLocal highLoaded kept afterCall afterAuthority secondWrite
  have highTail : slots[12]? = some (.bytes .vector128 highMask) := by simpa [layout] using highLocal
  have lower := vector128_prior_read entered middle after boundary slots homes 11 12 (by decide)
    lowMask highMask lowTail highTail _ _ secondWrite lowLoaded
  have earlier : ∀ i, i < 11 → ∀ reference bytes,
      slots[i]? = some (.bytes .vector128 reference) →
      read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes := by
    intro i bound reference bytes slot loaded
    exact vector128_prior_read entered middle after boundary slots homes i 12 (by omega)
      reference highMask slot highTail _ _ secondWrite
      (vector128_prior_read entered current middle boundary slots homes i 11 bound
        reference lowMask slot lowTail _ _ firstWrite loaded)
  exact continuation lowMask highMask after lowTail highTail lower highLoaded earlier
    (preserved.trans kept) afterCall afterAuthority
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ firstWrite).next
      (write_extends_allocations _ _ _ _ _ secondWrite).next)

#print axioms vector128_propagation_pair
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def vector128BranchValue (memory : Memory) (left right : Reference) (i : Fin 13) : BitVec 128 :=
  if within : i.val < 11 then vector128SnapshotValue memory left right ⟨i.val, within⟩
  else if i.val = 11 then
    propagating128 (vector128SnapshotValue memory left right 9) (vector128SnapshotValue memory left right 7)
  else propagating128 (vector128SnapshotValue memory left right 10) (vector128SnapshotValue memory left right 8)

/-- Entry through the propagation decision, with all thirteen saved values
    tied to the initial inputs and early ARM output readbacks still valid. -/
theorem vector128_ready_checked (original entered : Memory)
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
      (∀ i : Fin 13, ∃ reference,
        slots[i.val]? = some (.bytes .vector128 reference) ∧
        read after reference 16 1 = .ok (numberBytes (vector128BranchValue original left right i).toNat 16)) →
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
        run Extracted.program fuel vector128Index 94 args (vector128SavedFrame frame slots right) [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 0 args frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  apply vector128_output_prefix original entered inputs outputs left right output frame slots args call setup
    layout homes leftMember rightMember outputMember leftArg rightArg outputArg post
  intro current snapshots outputRead currentCall authority footprint advanced callerPreserved
  obtain ⟨lowHome, lowSlot, lowRead⟩ := snapshots 9
  obtain ⟨highHome, highSlot, highRead⟩ := snapshots 10
  obtain ⟨lowIncoming, lowIncomingSlot, lowIncomingRead⟩ := snapshots 7
  obtain ⟨highIncoming, highIncomingSlot, highIncomingRead⟩ := snapshots 8
  apply vector128_propagation_pair original.nextIdentity entered current inputs outputs
    (vector128SavedFrame frame slots right) (.root (some (.address right))) slots rfl args currentCall
    (enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup) homes authority
    (vector128SnapshotValue original left right 9) (vector128SnapshotValue original left right 10)
    (vector128SnapshotValue original left right 7) (vector128SnapshotValue original left right 8)
    lowHome highHome lowIncoming highIncoming lowSlot highSlot lowIncomingSlot highIncomingSlot
    lowRead highRead lowIncomingRead highIncomingRead post
  intro lowMask highMask after lowMaskSlot highMaskSlot lowMaskRead highMaskRead kept preserved afterCall afterAuthority next
  have ready : ∀ i : Fin 13, ∃ reference,
      slots[i.val]? = some (.bytes .vector128 reference) ∧
      read after reference 16 1 = .ok (numberBytes (vector128BranchValue original left right i).toNat 16) := by
    intro i
    by_cases within : i.val < 11
    · obtain ⟨reference, slot, loaded⟩ := snapshots ⟨i.val, within⟩
      refine ⟨reference, slot, ?_⟩
      simp only [vector128BranchValue, dif_pos within]
      exact kept i.val within reference _ slot loaded
    · have cases : i = 11 ∨ i = 12 := by omega
      rcases cases with rfl | rfl
      · exact ⟨lowMask, lowMaskSlot, lowMaskRead⟩
      · exact ⟨highMask, highMaskSlot, highMaskRead⟩
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed outputMember)
  have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  have retainedOutput : Extracted.profile.advSimd = true →
      read after output 16 1 = .ok (numberBytes (vector128SnapshotValue original left right 9).toNat 16) ∧
      read after { output with offset := output.offset + 16 } 16 1 =
        .ok (numberBytes (vector128SnapshotValue original left right 10).toNat 16) := by
    intro enabled
    exact ⟨(preserved.read output old 16 1).trans (outputRead enabled).1,
      (preserved.read { output with offset := output.offset + 16 } old 16 1).trans (outputRead enabled).2⟩
  exact continuation after ready retainedOutput afterCall afterAuthority
    (fun id offset bound outside => (preserved.cells id bound offset).trans (footprint id offset bound outside))
    (Nat.le_trans advanced next)
    (fun disabled => (callerPreserved disabled).trans preserved)

#print axioms vector128_ready_checked
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def selectedPropagation128 (flag : BitVec 32) (low high : BitVec 128) : BitVec 128 :=
  if Extracted.profile.advSimd = true ∧ flag = BitVec.ofNat 32 0 then incoming128High low high else low ||| high

/-- Follow the actual ISA/reporting choice and store the propagation condition.
    This covers both values of the reporting choice without a caller restriction. -/
theorem vector128_decision_checked (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (flag : BitVec 32) (argument : args[3]? = some (.scalar (.i32 flag)))
    (low high : BitVec 128) (lowHome highHome : Reference)
    (lowSlot : frame.locals[12]? = some (.bytes .vector128 lowHome))
    (highSlot : frame.locals[13]? = some (.bytes .vector128 highHome))
    (lowRead : read current lowHome 16 1 = .ok (numberBytes low.toNat 16))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[14]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok (numberBytes (selectedPropagation128 flag low high).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (selectedPropagation128 flag low high).toNat 16) 1 = .ok after →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index 107 args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 94 args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store boundary entered current inputs outputs frame root slots layout currentCall
      enteredWF homes authority 13 vector128ZeroSpec (by rfl)
      (.v128 (selectedPropagation128 flag low high)) (selectedPropagation128 flag low high).toNat rfl
  have done := continuation reference after slot loaded retained afterCall afterAuthority written
  have loadLow := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 low) low.toNat rfl lowSlot lowRead
  have loadHigh := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 high) high.toNat rfl highSlot highRead
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  have profile : vector128Body.profile = Extracted.profile := by rfl
  by_cases zero : flag = BitVec.ofNat 32 0
  all_goals
    simp only [selectedPropagation128, Extracted.profile, zero, and_true, and_false, ite_true, ite_false,
      Bool.false_eq_true, false_and, true_and] at stored
    repeat' first
      | exact done
      | (simp (config := { failIfUnchanged := false })
           [show (0 : BitVec 32) = BitVec.ofNat 32 0 from rfl, zero]
         apply run_next_exists post found (by rfl)
         first
         | exact loadLow _ _
         | exact loadHigh _ _
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, profile, cil_code, argument, pureArity, scalars, CIL.step, CIL.FeatureProfile.evaluate,
               CIL.Intrinsic.available, CIL.Vector.intrinsic_or128, CIL.Vector.intrinsic_adv_extract,
               incoming128_arm_high, show (0 : BitVec 32) = BitVec.ofNat 32 0 from rfl, zero,
               checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

/-- Test only the initialized saved condition and expose both actual targets. -/
theorem vector128_decision_branch (memory : Memory) (frame : Frame) (args : List Value)
    (home : Reference) (condition : BitVec 128)
    (slot : frame.locals[14]? = some (.bytes .vector128 home))
    (loaded : read memory home 16 1 = .ok (numberBytes condition.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel vector128Index (if condition = BitVec.ofNat 128 0 then 204 else 111)
        args frame [] memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 107 args frame [] memory = .ok (result, returned) ∧ post result returned := by
  have load := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 condition) condition.toNat rfl slot loaded
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  have profile : vector128Body.profile = Extracted.profile := by rfl
  by_cases zero : condition = BitVec.ofNat 128 0
  all_goals
    simp only [zero, ite_true, ite_false] at continuation
    repeat' first
      | exact continuation
      | (apply run_next_exists post found (by rfl)
         first
         | exact load _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.Intrinsic.available,
               CIL.Vector.intrinsic_zero128, CIL.Vector.intrinsic_equal_all128,
               show (0 : BitVec 128) = BitVec.ofNat 128 0 from rfl, zero,
               checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_decision_checked
#print axioms vector128_decision_branch
end UInt256Proof.Add.Safety
