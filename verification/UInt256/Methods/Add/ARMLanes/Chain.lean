import UInt256.Methods.Add.ARMLanes.Start
import UInt256.Methods.Add.ARMFlag

namespace UInt256Proof.Add.ARMLanes

section
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector UInt256Proof.Add.Safety
/-- Initial operands and the exact saved vectors at the output-stage boundary. -/
def lanesSnapshotValue (memory : Memory) (left right : Reference) (i : Fin 11) : BitVec 128 :=
  let a := inputHalf memory left 0
  let b := inputHalf memory left 1
  let c := inputHalf memory right 0
  let d := inputHalf memory right 1
  let low := halfSum a c
  let high := halfSum b d
  let lowMask := halfCarry low a
  let highMask := halfCarry high b
  match i.val with
  | 0 => d | 1 => a | 2 => c | 3 => b
  | 4 => high | 5 => lowMask | 6 => highMask
  | 7 => incoming128Low lowMask | 8 => incoming128High lowMask highMask
  | 9 => corrected128 low (incoming128Low lowMask)
  | _ => corrected128 high (incoming128High lowMask highMask)

#print axioms lanesSnapshotValue
end

section
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector UInt256Proof.Add.Safety
/-- Complete checked execution from entry to the first output-stage instruction. -/
theorem lanes_snapshots_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body)
    (startTail incomingTail leading correctionTail : List CIL.Op)
    (startCode : body.code = UInt256Proof.Add.SSEShapes.lanesPrefix ++ startTail)
    (incomingCode : body.code = lanesIncomingPrefix ++ incomingTail) (enabled : body.profile.advSimd = true)
    (leadingLength : leading.length = 62)
    (correctionCodeFound : body.code = leading ++ correctionCode ++ correctionTail)
    (firstEleven : ∀ i : Fin 11, specs[i.val]? = some vector128ZeroSpec)
    (sse : body.profile.advSimd = false → body.profile.sse2 = true)
    (ssse : body.profile.advSimd = false → body.profile.ssse3 = true) (original entered : Memory)
    (inputs outputs : List Reference) (left right : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions program original inputs outputs)
    (setup : enterFrame body args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity specs slots)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      (∀ i : Fin 11, ∃ reference,
        slots[i.val]? = some (.bytes .vector128 reference) ∧
        read after reference 16 1 = .ok (numberBytes (lanesSnapshotValue original left right i).toNat 16)) →
      MemoryBelow original.nextIdentity original after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      entered.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run program fuel method 69 args (vector128SavedFrame frame slots right) [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 0 args frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  apply lanes_start_checked program body method specs found startTail startCode (fun i => firstEleven ⟨i.val, by omega⟩) original entered inputs outputs left right frame slots args call setup
    layout homes leftMember rightMember leftArg rightArg post
  intro locations sum lowMask highMask prepared located sumSlot lowSlot highSlot sumRead lowRead highRead
    inputReads p0 c0 a0 n0
  apply lanes_incoming_pair program body method specs found incomingTail incomingCode enabled sse ssse ⟨firstEleven 7, firstEleven 8⟩ original.nextIdentity entered prepared inputs outputs
    (vector128SavedFrame frame slots right) (.root (some (.address right))) slots rfl args c0 enteredWF homes a0
    (lanesSnapshotValue original left right 5) (lanesSnapshotValue original left right 6)
    [.scalar (.v128 (halfSum (inputHalf original left 0) (inputHalf original right 0)))]
    lowMask highMask lowSlot highSlot lowRead highRead post
  intro lowIncoming highIncoming incoming lowIncomingSlot highIncomingSlot lowIncomingRead highIncomingRead
    keptIncoming p1 c1 a1 n1
  apply vector128_correction_pair program body method specs found leading correctionTail leadingLength correctionCodeFound ⟨firstEleven 9, firstEleven 10⟩ original.nextIdentity entered incoming inputs outputs
    (vector128SavedFrame frame slots right) (.root (some (.address right))) slots rfl args c1 enteredWF homes a1
    (halfSum (inputHalf original left 0) (inputHalf original right 0))
    (lanesSnapshotValue original left right 4)
    (lanesSnapshotValue original left right 7) (lanesSnapshotValue original left right 8)
    sum lowIncoming highIncoming sumSlot lowIncomingSlot highIncomingSlot
    (keptIncoming 4 (by decide) sum _ sumSlot sumRead) lowIncomingRead highIncomingRead post
  intro lowResult highResult after lowResultSlot highResultSlot lowResultRead highResultRead keptResult p2 c2 a2 n2
  have earlier : ∀ i, i < 7 → ∀ reference bytes,
      slots[i]? = some (.bytes .vector128 reference) →
      read prepared reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes := by
    intro i bound reference bytes slot loaded
    exact keptResult i (by omega) reference bytes slot (keptIncoming i bound reference bytes slot loaded)
  have snapshots : ∀ i : Fin 11, ∃ reference,
      slots[i.val]? = some (.bytes .vector128 reference) ∧
      read after reference 16 1 = .ok (numberBytes (lanesSnapshotValue original left right i).toNat 16) := by
    intro i
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
        i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨locations 0, located 0, earlier 0 (by decide) _ _ (located 0) (inputReads 0)⟩
    · exact ⟨locations 1, located 1, earlier 1 (by decide) _ _ (located 1) (inputReads 1)⟩
    · exact ⟨locations 2, located 2, earlier 2 (by decide) _ _ (located 2) (inputReads 2)⟩
    · exact ⟨locations 3, located 3, earlier 3 (by decide) _ _ (located 3) (inputReads 3)⟩
    · exact ⟨sum, sumSlot, earlier 4 (by decide) _ _ sumSlot sumRead⟩
    · exact ⟨lowMask, lowSlot, earlier 5 (by decide) _ _ lowSlot lowRead⟩
    · exact ⟨highMask, highSlot, earlier 6 (by decide) _ _ highSlot highRead⟩
    · exact ⟨lowIncoming, lowIncomingSlot, keptResult 7 (by decide) _ _ lowIncomingSlot lowIncomingRead⟩
    · exact ⟨highIncoming, highIncomingSlot, keptResult 8 (by decide) _ _ highIncomingSlot highIncomingRead⟩
    · exact ⟨lowResult, lowResultSlot, lowResultRead⟩
    · exact ⟨highResult, highResultSlot, highResultRead⟩
  exact continuation after snapshots (p0.trans (p1.trans p2)) c2 a2 (Nat.le_trans n0 (Nat.le_trans n1 n2))

#print axioms lanes_snapshots_checked
end

section
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety
/-- Execution from helper entry through the ISA-dependent early output stage. -/
theorem lanes_output_prefix (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body)
    (startTail incomingTail leading correctionTail : List CIL.Op)
    (startCode : body.code = UInt256Proof.Add.SSEShapes.lanesPrefix ++ startTail)
    (incomingCode : body.code = lanesIncomingPrefix ++ incomingTail) (enabled : body.profile.advSimd = true)
    (leadingLength : leading.length = 62)
    (correctionCodeFound : body.code = leading ++ correctionCode ++ correctionTail)
    (firstEleven : ∀ i : Fin 11, specs[i.val]? = some vector128ZeroSpec)
    (sse : body.profile.advSimd = false → body.profile.sse2 = true)
    (ssse : body.profile.advSimd = false → body.profile.ssse3 = true)     (earlyLeading earlyTail : List CIL.Op) (earlyLength : earlyLeading.length = 69)
    (earlyCode : body.code = earlyLeading ++ earlyOutputCode body.profile.advSimd ++ earlyTail) (original entered : Memory)
    (inputs outputs : List Reference) (left right output : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions program original inputs outputs)
    (setup : enterFrame body args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity specs slots)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs) (outputMember : output ∈ outputs)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (outputArg : args[2]? = some (.reference (.address output)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      (∀ i : Fin 11, ∃ reference,
        slots[i.val]? = some (.bytes .vector128 reference) ∧
        read after reference 16 1 = .ok (numberBytes (lanesSnapshotValue original left right i).toNat 16)) →
      (body.profile.advSimd = true →
        read after output 16 1 = .ok (numberBytes (lanesSnapshotValue original left right 9).toNat 16) ∧
        read after { output with offset := output.offset + 16 } 16 1 =
          .ok (numberBytes (lanesSnapshotValue original left right 10).toNat 16)) →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        after.cells id offset = original.cells id offset) →
      entered.nextIdentity ≤ after.nextIdentity →
      (body.profile.advSimd = false → MemoryBelow original.nextIdentity original after) →
      ∃ fuel result returned,
        run program fuel method 82 args (vector128SavedFrame frame slots right) [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 0 args frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  apply lanes_snapshots_checked program body method specs found startTail incomingTail leading correctionTail startCode incomingCode enabled leadingLength correctionCodeFound firstEleven sse ssse original entered inputs outputs left right frame slots args call setup
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
  apply vector128_output_dispatch program body method found earlyLeading earlyTail earlyLength earlyCode current output (vector128SavedFrame frame slots right) args outputArg
    (currentCall.output_formed outputMember) post
  apply vector128_early_output program body method found earlyLeading earlyTail earlyLength earlyCode original entered current inputs outputs output
    (vector128SavedFrame frame slots right) args call currentCall outputMember authority outputArg
    (lanesSnapshotValue original left right 9) (lanesSnapshotValue original left right 10)
    lowHome highHome actualLow actualHigh (homes.home_bound 10 .vector128 highHome highSlot) lowRead highRead post
  intro after outputRead afterCall afterAuthority outside privateReads next unchanged
  have retained : ∀ i : Fin 11, ∃ reference,
      slots[i.val]? = some (.bytes .vector128 reference) ∧
      read after reference 16 1 = .ok (numberBytes (lanesSnapshotValue original left right i).toNat 16) := by
    intro i
    obtain ⟨reference, slot, loaded⟩ := snapshots i
    exact ⟨reference, slot, privateReads reference 16 1 _
      (homes.home_bound i.val .vector128 reference slot) loaded⟩
  exact continuation after retained outputRead afterCall afterAuthority
    (fun id offset old excluded => (outside id offset excluded).trans (preserved.cells id old offset))
    (Nat.le_trans advanced next)
    (fun disabled => by rw [unchanged disabled]; exact preserved)

#print axioms lanes_output_prefix
end

section
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety
def lanesBranchValue (memory : Memory) (left right : Reference) (i : Fin 13) : BitVec 128 :=
  if within : i.val < 11 then lanesSnapshotValue memory left right ⟨i.val, within⟩
  else if i.val = 11 then
    propagating128 (lanesSnapshotValue memory left right 9) (lanesSnapshotValue memory left right 7)
  else propagating128 (lanesSnapshotValue memory left right 10) (lanesSnapshotValue memory left right 8)

#print axioms lanesBranchValue
end

section
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety
/-- Entry through the propagation decision, with all thirteen saved values tied to the initial inputs and early ARM output readbacks still valid. -/
theorem lanes_ready_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body)
    (startTail incomingTail leading correctionTail : List CIL.Op)
    (startCode : body.code = UInt256Proof.Add.SSEShapes.lanesPrefix ++ startTail)
    (incomingCode : body.code = lanesIncomingPrefix ++ incomingTail) (enabled : body.profile.advSimd = true)
    (leadingLength : leading.length = 62)
    (correctionCodeFound : body.code = leading ++ correctionCode ++ correctionTail)
    (firstThirteen : ∀ i : Fin 13, specs[i.val]? = some vector128ZeroSpec)
    (sse : body.profile.advSimd = false → body.profile.sse2 = true)
    (ssse : body.profile.advSimd = false → body.profile.ssse3 = true)     (earlyLeading earlyTail : List CIL.Op) (earlyLength : earlyLeading.length = 69)
    (earlyCode : body.code = earlyLeading ++ earlyOutputCode body.profile.advSimd ++ earlyTail)     (propLeading propTail : List CIL.Op) (propLength : propLeading.length = 82)
    (propCode : body.code = propLeading ++ propagationCode ++ propTail) (original entered : Memory)
    (inputs outputs : List Reference) (left right output : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions program original inputs outputs)
    (setup : enterFrame body args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity specs slots)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs) (outputMember : output ∈ outputs)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (outputArg : args[2]? = some (.reference (.address output)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      (∀ i : Fin 13, ∃ reference,
        slots[i.val]? = some (.bytes .vector128 reference) ∧
        read after reference 16 1 = .ok (numberBytes (lanesBranchValue original left right i).toNat 16)) →
      (body.profile.advSimd = true →
        read after output 16 1 = .ok (numberBytes (lanesSnapshotValue original left right 9).toNat 16) ∧
        read after { output with offset := output.offset + 16 } 16 1 =
          .ok (numberBytes (lanesSnapshotValue original left right 10).toNat 16)) →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        after.cells id offset = original.cells id offset) →
      entered.nextIdentity ≤ after.nextIdentity →
      (body.profile.advSimd = false → MemoryBelow original.nextIdentity original after) →
      ∃ fuel result returned,
        run program fuel method 94 args (vector128SavedFrame frame slots right) [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 0 args frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  apply lanes_output_prefix program body method specs found startTail incomingTail leading correctionTail startCode incomingCode enabled leadingLength correctionCodeFound (fun i => firstThirteen ⟨i.val, by omega⟩) sse ssse earlyLeading earlyTail earlyLength earlyCode original entered inputs outputs left right output frame slots args call setup
    layout homes leftMember rightMember outputMember leftArg rightArg outputArg post
  intro current snapshots outputRead currentCall authority footprint advanced callerPreserved
  obtain ⟨lowHome, lowSlot, lowRead⟩ := snapshots 9
  obtain ⟨highHome, highSlot, highRead⟩ := snapshots 10
  obtain ⟨lowIncoming, lowIncomingSlot, lowIncomingRead⟩ := snapshots 7
  obtain ⟨highIncoming, highIncomingSlot, highIncomingRead⟩ := snapshots 8
  apply vector128_propagation_pair program body method specs found propLeading propTail propLength propCode ⟨firstThirteen 11, firstThirteen 12⟩ original.nextIdentity entered current inputs outputs
    (vector128SavedFrame frame slots right) (.root (some (.address right))) slots rfl args currentCall
    (enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup) homes authority
    (lanesSnapshotValue original left right 9) (lanesSnapshotValue original left right 10)
    (lanesSnapshotValue original left right 7) (lanesSnapshotValue original left right 8)
    lowHome highHome lowIncoming highIncoming lowSlot highSlot lowIncomingSlot highIncomingSlot
    lowRead highRead lowIncomingRead highIncomingRead post
  intro lowMask highMask after lowMaskSlot highMaskSlot lowMaskRead highMaskRead kept preserved afterCall afterAuthority next
  have ready : ∀ i : Fin 13, ∃ reference,
      slots[i.val]? = some (.bytes .vector128 reference) ∧
      read after reference 16 1 = .ok (numberBytes (lanesBranchValue original left right i).toNat 16) := by
    intro i
    by_cases within : i.val < 11
    · obtain ⟨reference, slot, loaded⟩ := snapshots ⟨i.val, within⟩
      refine ⟨reference, slot, ?_⟩
      simp only [lanesBranchValue, dif_pos within]
      exact kept i.val within reference _ slot loaded
    · have cases : i = 11 ∨ i = 12 := by omega
      rcases cases with rfl | rfl
      · exact ⟨lowMask, lowMaskSlot, lowMaskRead⟩
      · exact ⟨highMask, highMaskSlot, highMaskRead⟩
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed outputMember)
  have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  have retainedOutput : body.profile.advSimd = true →
      read after output 16 1 = .ok (numberBytes (lanesSnapshotValue original left right 9).toNat 16) ∧
      read after { output with offset := output.offset + 16 } 16 1 =
        .ok (numberBytes (lanesSnapshotValue original left right 10).toNat 16) := by
    intro enabled
    exact ⟨(preserved.read output old 16 1).trans (outputRead enabled).1,
      (preserved.read { output with offset := output.offset + 16 } old 16 1).trans (outputRead enabled).2⟩
  exact continuation after ready retainedOutput afterCall afterAuthority
    (fun id offset bound outside => (preserved.cells id bound offset).trans (footprint id offset bound outside))
    (Nat.le_trans advanced next)
    (fun disabled => (callerPreserved disabled).trans preserved)

#print axioms lanes_ready_checked
end

section
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety
/-- Complete checked helper prefix through the actual fast/repair branch, preserving all saved values and any early ARM output writes. -/
theorem lanes_dispatch_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body)
    (startTail incomingTail leading correctionTail : List CIL.Op)
    (startCode : body.code = UInt256Proof.Add.SSEShapes.lanesPrefix ++ startTail)
    (incomingCode : body.code = lanesIncomingPrefix ++ incomingTail) (enabled : body.profile.advSimd = true)
    (leadingLength : leading.length = 62)
    (correctionCodeFound : body.code = leading ++ correctionCode ++ correctionTail)
    (firstFourteen : ∀ i : Fin 14, specs[i.val]? = some vector128ZeroSpec)
    (sse : body.profile.advSimd = false → body.profile.sse2 = true)
    (ssse : body.profile.advSimd = false → body.profile.ssse3 = true)     (earlyLeading earlyTail : List CIL.Op) (earlyLength : earlyLeading.length = 69)
    (earlyCode : body.code = earlyLeading ++ earlyOutputCode body.profile.advSimd ++ earlyTail)     (propLeading propTail : List CIL.Op) (propLength : propLeading.length = 82)
    (propCode : body.code = propLeading ++ propagationCode ++ propTail)     (decisionLeading decisionTail : List CIL.Op) (decisionLength : decisionLeading.length = 94)
    (decisionCodeFound : body.code = decisionLeading ++ decisionCode body.profile.advSimd ++ decisionTail) (original entered : Memory)
    (inputs outputs : List Reference) (left right output : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions program original inputs outputs)
    (setup : enterFrame body args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity specs slots)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs) (outputMember : output ∈ outputs)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (outputArg : args[2]? = some (.reference (.address output)))
    (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag) (flagArg : args[3]? = some (.scalar (.i32 flag)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after conditionHome,
      slots[13]? = some (.bytes .vector128 conditionHome) →
      read after conditionHome 16 1 = .ok (numberBytes
        (selectedPropagation128 body.profile.advSimd flag (lanesBranchValue original left right 11)
          (lanesBranchValue original left right 12)).toNat 16) →
      (∀ i : Fin 13, ∃ reference,
        slots[i.val]? = some (.bytes .vector128 reference) ∧
        read after reference 16 1 = .ok (numberBytes (lanesBranchValue original left right i).toNat 16)) →
      (body.profile.advSimd = true →
        read after output 16 1 = .ok (numberBytes (lanesSnapshotValue original left right 9).toNat 16) ∧
        read after { output with offset := output.offset + 16 } 16 1 =
          .ok (numberBytes (lanesSnapshotValue original left right 10).toNat 16)) →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        after.cells id offset = original.cells id offset) →
      entered.nextIdentity ≤ after.nextIdentity →
      (body.profile.advSimd = false → MemoryBelow original.nextIdentity original after) →
      ∃ fuel result returned,
        run program fuel method
          (if selectedPropagation128 body.profile.advSimd flag (lanesBranchValue original left right 11)
            (lanesBranchValue original left right 12) = BitVec.ofNat 128 0 then 204 else 111) args (vector128SavedFrame frame slots right) [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 0 args frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  apply lanes_ready_checked program body method specs found startTail incomingTail leading correctionTail startCode incomingCode enabled leadingLength correctionCodeFound (fun i => firstFourteen ⟨i.val, by omega⟩) sse ssse earlyLeading earlyTail earlyLength earlyCode propLeading propTail propLength propCode original entered inputs outputs left right output frame slots args
    call setup layout homes leftMember rightMember outputMember leftArg rightArg outputArg post
  intro current snapshots outputRead currentCall authority footprint advanced callerPreserved
  obtain ⟨lowHome, lowSlot, lowRead⟩ := snapshots 11
  obtain ⟨highHome, highSlot, highRead⟩ := snapshots 12
  have actualLow : (vector128SavedFrame frame slots right).locals[12]? = some (.bytes .vector128 lowHome) := by
    change slots[11]? = some (.bytes .vector128 lowHome)
    exact lowSlot
  have actualHigh : (vector128SavedFrame frame slots right).locals[13]? = some (.bytes .vector128 highHome) := by
    change slots[12]? = some (.bytes .vector128 highHome)
    exact highSlot
  apply vector128_decision_checked program body method found decisionLeading decisionTail decisionLength decisionCodeFound specs (firstFourteen 13) original.nextIdentity entered current inputs outputs
    (vector128SavedFrame frame slots right) (.root (some (.address right))) slots rfl args currentCall
    (enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup) homes authority flag flagFit flagArg
    (lanesBranchValue original left right 11) (lanesBranchValue original left right 12)
    lowHome highHome actualLow actualHigh lowRead highRead post
  intro conditionHome after conditionSlot conditionRead preserved afterCall afterAuthority written
  have conditionTail : slots[13]? = some (.bytes .vector128 conditionHome) := by
    exact conditionSlot
  have retained : ∀ i : Fin 13, ∃ reference,
      slots[i.val]? = some (.bytes .vector128 reference) ∧
      read after reference 16 1 = .ok (numberBytes (lanesBranchValue original left right i).toNat 16) := by
    intro i
    obtain ⟨reference, slot, loaded⟩ := snapshots i
    exact ⟨reference, slot, vector128_prior_read specs entered current after original.nextIdentity slots homes
      i.val 13 i.isLt reference conditionHome slot conditionTail _ _ written loaded⟩
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed outputMember)
  have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  have retainedOutput : body.profile.advSimd = true →
      read after output 16 1 = .ok (numberBytes (lanesSnapshotValue original left right 9).toNat 16) ∧
      read after { output with offset := output.offset + 16 } 16 1 =
        .ok (numberBytes (lanesSnapshotValue original left right 10).toNat 16) := by
    intro enabled
    exact ⟨(preserved.read output old 16 1).trans (outputRead enabled).1,
      (preserved.read { output with offset := output.offset + 16 } old 16 1).trans (outputRead enabled).2⟩
  apply vector128_decision_branch program body method found decisionLeading decisionTail decisionLength decisionCodeFound after (vector128SavedFrame frame slots right) args conditionHome
    _ conditionSlot conditionRead post
  exact continuation after conditionHome conditionTail conditionRead retained retainedOutput afterCall afterAuthority
    (fun id offset bound outside => (preserved.cells id bound offset).trans (footprint id offset bound outside))
    (Nat.le_trans advanced (write_extends_allocations _ _ _ _ _ written).next)
    (fun disabled => (callerPreserved disabled).trans preserved)

#print axioms lanes_dispatch_checked
end

section
open CIL.Safety CIL.Vector UInt256Model UInt256Model.Safety UInt256Proof.SIMD UInt256Proof.Add.Safety
theorem lanes_snapshot_low (memory : Memory) (left right : Reference) :
    lanesSnapshotValue memory left right 9 =
      correctedLo (inputLimb memory left) (inputLimb memory right) := by
  simp only [lanesSnapshotValue, show (9 : Fin 11).val = 9 from rfl]
  simpa only [input_half_low, input_half_high] using
    vector128_low_corrected (inputLimb memory left) (inputLimb memory right)

#print axioms lanes_snapshot_low
end

section
open CIL.Safety CIL.Vector UInt256Model UInt256Model.Safety UInt256Proof.SIMD UInt256Proof.Add.Safety
theorem lanes_snapshot_high (memory : Memory) (left right : Reference) :
    lanesSnapshotValue memory left right 10 =
      correctedHi (inputLimb memory left) (inputLimb memory right) := by
  simp only [lanesSnapshotValue, show (10 : Fin 11).val = 10 from rfl]
  simpa only [input_half_low, input_half_high] using
    vector128_high_corrected (inputLimb memory left) (inputLimb memory right)

#print axioms lanes_snapshot_high
end

section
open CIL.Safety CIL.Vector UInt256Model UInt256Model.Safety UInt256Proof.SIMD UInt256Proof.Add.Safety
theorem lanes_snapshot_incoming_low (memory : Memory) (left right : Reference) :
    lanesSnapshotValue memory left right 7 = pack128 (BitVec.ofNat 64 0)
      (carryMask (inputLimb memory left 0) (inputLimb memory right 0)) := by
  simp only [lanesSnapshotValue, show (7 : Fin 11).val = 7 from rfl]
  simp only [input_half_low, input_half_high, incoming128Low,
    halfCarry, halfSum, zip128, lane128_0, lane128_1, carryMask]
  rfl

#print axioms lanes_snapshot_incoming_low
end

section
open CIL.Safety CIL.Vector UInt256Model UInt256Model.Safety UInt256Proof.SIMD UInt256Proof.Add.Safety
theorem lanes_snapshot_incoming_high (memory : Memory) (left right : Reference) :
    lanesSnapshotValue memory left right 8 = pack128
      (carryMask (inputLimb memory left 1) (inputLimb memory right 1))
      (carryMask (inputLimb memory left 2) (inputLimb memory right 2)) := by
  simp only [lanesSnapshotValue, show (8 : Fin 11).val = 8 from rfl]
  simp only [input_half_low, input_half_high, incoming128High,
    halfCarry, halfSum, zip128, lane128_0, lane128_1, carryMask]

#print axioms lanes_snapshot_incoming_high
end

section
open CIL.Safety CIL.Vector UInt256Model UInt256Model.Safety UInt256Proof.SIMD UInt256Proof.Add.Safety
theorem lanes_branch_low (memory : Memory) (left right : Reference) :
    lanesBranchValue memory left right 11 =
      propagationLo (inputLimb memory left) (inputLimb memory right) := by
  change propagating128 (lanesSnapshotValue memory left right 9)
    (lanesSnapshotValue memory left right 7) = _
  rw [lanes_snapshot_low, lanes_snapshot_incoming_low]
  exact vector128_low_propagation _ _

#print axioms lanes_branch_low
end

section
open CIL.Safety CIL.Vector UInt256Model UInt256Model.Safety UInt256Proof.SIMD UInt256Proof.Add.Safety
theorem lanes_branch_high (memory : Memory) (left right : Reference) :
    lanesBranchValue memory left right 12 =
      propagationHi (inputLimb memory left) (inputLimb memory right) := by
  change propagating128 (lanesSnapshotValue memory left right 10)
    (lanesSnapshotValue memory left right 8) = _
  rw [lanes_snapshot_high, lanes_snapshot_incoming_high]
  exact vector128_high_propagation _ _

#print axioms lanes_branch_high
end

section
open CIL.Safety CIL.Vector UInt256Model UInt256Model.Safety UInt256Proof.SIMD UInt256Proof.Add.Safety
/-- The actual saved fast condition implies the saved output halves encode the sum of the initial caller operands, including overlapping views. -/
theorem lanes_snapshot_fast_words (memory : Memory) (left right : Reference) (advSimd : Bool) (flag : BitVec 32)
    (fast : selectedPropagation128 advSimd flag (lanesBranchValue memory left right 11)
      (lanesBranchValue memory left right 12) = BitVec.ofNat 128 0) :
    let words := sumWords (inputLimb memory left) (inputLimb memory right)
    lanesSnapshotValue memory left right 9 = pack128 (words 0) (words 1) ∧
    lanesSnapshotValue memory left right 10 = pack128 (words 2) (words 3) := by
  rw [lanes_branch_low, lanes_branch_high] at fast
  simpa only [lanes_snapshot_low, lanes_snapshot_high] using
    vector128_fast_words advSimd (inputLimb memory left) (inputLimb memory right) flag fast

#print axioms lanes_snapshot_fast_words
end

section
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety
/-- Complete fast suffix with initial-input arithmetic and surviving caller memory guarantees. -/
theorem lanes_fast_result (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (leadingLength : leading.length = 204)
    (code : body.code = leading ++ fastOutputCode body.profile.advSimd ++ tail)
    (returns : body.returnsValue = true) (original entered current : Memory)
    (inputs outputs : List Reference) (output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions program original inputs outputs)
    (currentCall : CallingConditions program current inputs outputs)
    (member : output ∈ outputs) (authority : AccessBelow entered.nextIdentity entered current)
    (argument : args[2]? = some (.reference (.address output)))
    (low high : BitVec 128) (lowHome highHome : Reference)
    (lowSlot : frame.locals[10]? = some (.bytes .vector128 lowHome))
    (highSlot : frame.locals[11]? = some (.bytes .vector128 highHome))
    (highBound : original.nextIdentity ≤ highHome.allocation)
    (lowRead : read current lowHome 16 1 = .ok (numberBytes low.toNat 16))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (earlyRead : body.profile.advSimd = true →
      read current output 16 1 = .ok (numberBytes low.toNat 16) ∧
      read current { output with offset := output.offset + 16 } 16 1 = .ok (numberBytes high.toNat 16))
    (carryHome : Reference) (carry : BitVec 128)
    (carrySlot : frame.locals[7]? = some (.bytes .vector128 carryHome))
    (carryBound : original.nextIdentity ≤ carryHome.allocation)
    (carryRead : read current carryHome 16 1 = .ok (numberBytes carry.toNat 16))
    (left right : Reference) (flag : BitVec 32)
    (lowValue : low = lanesSnapshotValue original left right 9)
    (highValue : high = lanesSnapshotValue original left right 10)
    (fast : selectedPropagation128 body.profile.advSimd flag (lanesBranchValue original left right 11)
      (lanesBranchValue original left right 12) = BitVec.ofNat 128 0)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id) :
    ∃ fuel final returned,
      run program fuel method 204 args frame [] current = .ok (final, returned) ∧
      returned = [.scalar (.i32 (if CIL.Vector.lane64 carry 1 > BitVec.ofNat 64 0 then 1 else 0))] ∧
      inputValue final output = inputValue original left + inputValue original right ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = current.cells id offset) := by
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [.scalar (.i32 (if CIL.Vector.lane64 carry 1 > BitVec.ofNat 64 0 then 1 else 0))] ∧
    inputValue final output = inputValue original left + inputValue original right ∧
    access final output 32 1 true = .ok () ∧
    (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
      final.cells id offset = current.cells id offset)
  apply vector128_fast_suffix program body method found leading tail leadingLength code returns original entered current inputs outputs output frame args
    call currentCall member authority argument low high lowHome highHome lowSlot highSlot
    highBound lowRead highRead earlyRead carryHome carry carrySlot carryBound carryRead post
  intro after outputRead afterCall afterAuthority outside advanced
  have teardown := leaveFrame_preserves_memory_below frame after original.nextIdentity owned
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed member)
  have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  have lo := (teardown.read output old 16 1).trans outputRead.1
  have hi := (teardown.read { output with offset := output.offset + 16 } old 16 1).trans outputRead.2
  obtain ⟨lowWords, highWords⟩ := lanes_snapshot_fast_words original left right body.profile.advSimd flag fast
  rw [lowValue, lowWords] at lo
  rw [highValue, highWords] at hi
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [output_value_of_packed_halves _ _ _ lo hi, UInt256Proof.sumWords_sum,
      input_limbs_value, input_limbs_value]
  · exact (teardown.access output old 32 1 true).trans
      (afterCall.1.2.2 (wordView output) (List.mem_map.mpr ⟨output, member, rfl⟩))
  · intro id offset earlier untouched
    exact (teardown.cells id earlier offset).trans (outside id offset untouched)

#print axioms lanes_fast_result
end

section
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety
/-- Checked execution from helper entry for the mathematical fast case. -/
theorem lanes_fast_entry (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body)
    (startTail incomingTail leading correctionTail : List CIL.Op)
    (startCode : body.code = UInt256Proof.Add.SSEShapes.lanesPrefix ++ startTail)
    (incomingCode : body.code = lanesIncomingPrefix ++ incomingTail) (enabled : body.profile.advSimd = true)
    (leadingLength : leading.length = 62)
    (correctionCodeFound : body.code = leading ++ correctionCode ++ correctionTail)
    (firstFourteen : ∀ i : Fin 14, specs[i.val]? = some vector128ZeroSpec)
    (sse : body.profile.advSimd = false → body.profile.sse2 = true)
    (ssse : body.profile.advSimd = false → body.profile.ssse3 = true)     (earlyLeading earlyTail : List CIL.Op) (earlyLength : earlyLeading.length = 69)
    (earlyCode : body.code = earlyLeading ++ earlyOutputCode body.profile.advSimd ++ earlyTail)     (propLeading propTail : List CIL.Op) (propLength : propLeading.length = 82)
    (propCode : body.code = propLeading ++ propagationCode ++ propTail)     (decisionLeading decisionTail : List CIL.Op) (decisionLength : decisionLeading.length = 94)
    (decisionCodeFound : body.code = decisionLeading ++ decisionCode body.profile.advSimd ++ decisionTail)     (fastLeading fastTail : List CIL.Op) (fastLength : fastLeading.length = 204)
    (fastCode : body.code = fastLeading ++ fastOutputCode body.profile.advSimd ++ fastTail)
    (returns : body.returnsValue = true) (original entered : Memory)
    (inputs outputs : List Reference) (left right output : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions program original inputs outputs)
    (setup : enterFrame body args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity specs slots)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs) (outputMember : output ∈ outputs)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (outputArg : args[2]? = some (.reference (.address output)))
    (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag) (flagArg : args[3]? = some (.scalar (.i32 flag)))
    (fast : selectedPropagation128 body.profile.advSimd flag (lanesBranchValue original left right 11)
      (lanesBranchValue original left right 12) = BitVec.ofNat 128 0) :
    ∃ fuel final returned,
      run program fuel method 0 args frame [] entered = .ok (final, returned) ∧
      returned = [.scalar (.i32 (if CIL.Vector.lane64 (lanesSnapshotValue original left right 6) 1 > BitVec.ofNat 64 0 then 1 else 0))] ∧
      inputValue final output = inputValue original left + inputValue original right ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = original.cells id offset) := by
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [.scalar (.i32 (if CIL.Vector.lane64 (lanesSnapshotValue original left right 6) 1 > BitVec.ofNat 64 0 then 1 else 0))] ∧
    inputValue final output = inputValue original left + inputValue original right ∧
    access final output 32 1 true = .ok () ∧
    (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
      final.cells id offset = original.cells id offset)
  apply lanes_dispatch_checked program body method specs found startTail incomingTail leading correctionTail startCode incomingCode enabled leadingLength correctionCodeFound firstFourteen sse ssse earlyLeading earlyTail earlyLength earlyCode propLeading propTail propLength propCode decisionLeading decisionTail decisionLength decisionCodeFound original entered inputs outputs left right output frame slots args
    call setup layout homes leftMember rightMember outputMember leftArg rightArg outputArg flag flagFit flagArg post
  intro current conditionHome conditionSlot conditionRead snapshots earlyRead currentCall authority footprint advanced _callerPreserved
  simp only [fast, ite_true]
  obtain ⟨lowHome, lowSlot, lowRead⟩ := snapshots 9
  obtain ⟨highHome, highSlot, highRead⟩ := snapshots 10
  obtain ⟨carryHome, carrySlot, carryRead⟩ := snapshots 6
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  obtain ⟨fuel, final, returned, executed, scalar, result, writable, outside⟩ :=
    lanes_fast_result program body method found fastLeading fastTail fastLength fastCode returns original entered current inputs outputs output
      (vector128SavedFrame frame slots right) args call currentCall outputMember authority outputArg
      (lanesSnapshotValue original left right 9) (lanesSnapshotValue original left right 10)
      lowHome highHome lowSlot highSlot (homes.home_bound 10 .vector128 highHome highSlot)
      lowRead highRead earlyRead carryHome (lanesBranchValue original left right 6) carrySlot
      (homes.home_bound 6 .vector128 carryHome carrySlot) carryRead left right flag rfl rfl fast
      (fun id member => (fresh.2 id member).1)
  exact ⟨fuel, final, returned, executed, scalar, result, writable,
    fun id offset old untouched => (outside id offset old untouched).trans (footprint id offset old untouched)⟩

#print axioms lanes_fast_entry
end

section
open CIL.Safety CIL.Vector UInt256Model UInt256Model.Safety UInt256Proof.SIMD UInt256Proof.Add.Safety
theorem lanes_snapshot_high_carry (memory : Memory) (left right : Reference) :
    lanesSnapshotValue memory left right 6 =
      pack128 (carryMask (inputLimb memory left 2) (inputLimb memory right 2))
        (carryMask (inputLimb memory left 3) (inputLimb memory right 3)) := by
  simp only [lanesSnapshotValue, show (6 : Fin 11).val = 6 from rfl,
    input_half_high, halfCarry, halfSum, zip128, lane128_0, lane128_1, carryMask]

#print axioms lanes_snapshot_high_carry
end

section
open CIL.Safety UInt256Model.Safety UInt256Proof.SIMD UInt256Proof.Add.Safety
def lanesDecisionValues (advSimd : Bool) (memory : Memory) (left right : Reference) (flag : BitVec 32)
    (i : Fin 14) : BitVec 128 :=
  if within : i.val < 13 then lanesBranchValue memory left right ⟨i.val, within⟩
  else selectedPropagation128 advSimd flag (lanesBranchValue memory left right 11) (lanesBranchValue memory left right 12)

#print axioms lanesDecisionValues
end

section
open CIL.Safety UInt256Model.Safety UInt256Proof.SIMD UInt256Proof.Add.Safety
theorem lanes_decision_values_old (advSimd : Bool) (memory : Memory) (left right : Reference) (flag : BitVec 32) (i : Fin 13) :
    lanesDecisionValues advSimd memory left right flag ⟨i.val, by omega⟩ = lanesBranchValue memory left right i := by
  simp only [lanesDecisionValues, dite_eq_left i.isLt]

#print axioms lanes_decision_values_old
end

section
open CIL.Safety UInt256Model.Safety UInt256Proof.SIMD UInt256Proof.Add.Safety
theorem lanes_decision_repair_mask (advSimd : Bool) (memory : Memory) (left right : Reference) (flag : BitVec 32) :
    repair128Mask (lanesDecisionValues advSimd memory left right flag 10)
      (lanesDecisionValues advSimd memory left right flag 11) (lanesDecisionValues advSimd memory left right flag 12) =
      extraHi (inputLimb memory left) (inputLimb memory right) := by
  change repair128Mask (lanesSnapshotValue memory left right 10)
    (lanesBranchValue memory left right 11) (lanesBranchValue memory left right 12) = _
  rw [lanes_snapshot_high, lanes_branch_low, lanes_branch_high]
  exact vector128_arm_extra_value _ _

#print axioms lanes_decision_repair_mask
end

section
open CIL.Safety UInt256Model.Safety UInt256Proof.SIMD UInt256Proof.Add.Safety
theorem lanes_repaired_snapshot_high (advSimd : Bool) (memory : Memory) (left right : Reference) (flag : BitVec 32) :
    armRepairSnapshot (lanesDecisionValues advSimd memory left right flag) 10 =
      repairedHi (inputLimb memory left) (inputLimb memory right) := by
  change corrected128 (lanesSnapshotValue memory left right 10)
    (repair128Mask (lanesDecisionValues advSimd memory left right flag 10)
      (lanesDecisionValues advSimd memory left right flag 11) (lanesDecisionValues advSimd memory left right flag 12)) = _
  rw [lanes_snapshot_high, lanes_decision_repair_mask]
  exact vector128_arm_repaired_high _ _

#print axioms lanes_repaired_snapshot_high
end

section
open CIL.Safety UInt256Model.Safety UInt256Proof.SIMD UInt256Proof.Add.Safety
theorem lanes_repaired_snapshot_carry (advSimd : Bool) (memory : Memory) (left right : Reference) (flag : BitVec 32) :
    armRepairSnapshot (lanesDecisionValues advSimd memory left right flag) 6 =
      UInt256Proof.Reporting.repairedCarryHi (inputLimb memory left) (inputLimb memory right) := by
  change repaired128Carry (lanesSnapshotValue memory left right 6)
    (lanesBranchValue memory left right 12) (full128 (lanesSnapshotValue memory left right 10))
    (repair128Mask (lanesDecisionValues advSimd memory left right flag 10)
      (lanesDecisionValues advSimd memory left right flag 11) (lanesDecisionValues advSimd memory left right flag 12)) = _
  rw [lanes_snapshot_high_carry, lanes_branch_high, lanes_snapshot_high, lanes_decision_repair_mask]
  exact vector128_arm_repaired_carry _ _

#print axioms lanes_repaired_snapshot_carry
end

section
open CIL.Safety CIL.Vector UInt256Model.Safety UInt256Proof.SIMD UInt256Proof.Reporting UInt256Proof.Add.Safety
/-- The actual fast-return mask encodes overflow when reporting was requested. -/
theorem lanes_snapshot_fast_flag (advSimd : Bool) (memory : Memory) (left right : Reference) (flag : BitVec 32)
    (reporting : flag ≠ BitVec.ofNat 32 0)
    (fast : selectedPropagation128 advSimd flag (lanesBranchValue memory left right 11)
      (lanesBranchValue memory left right 12) = BitVec.ofNat 128 0) :
    (if lane64 (lanesSnapshotValue memory left right 6) 1 > BitVec.ofNat 64 0
      then (1 : BitVec 32) else 0) =
      if 2^256 ≤ (inputValue memory left).toNat + (inputValue memory right).toNat then 1 else 0 := by
  rw [lanes_branch_low, lanes_branch_high] at fast
  have carry := vector128_reporting_fast_carry advSimd (inputLimb memory left) (inputLimb memory right)
    flag reporting fast
  rw [lanes_snapshot_high_carry, lane128_1, carry_mask_negative, ← carry]
  simp only [word_positive, ne_eq, BitVec.neg_eq_zero_iff]
  have overflow := finalCarry_overflow (inputLimb memory left) (inputLimb memory right)
  rw [input_limbs_value, input_limbs_value] at overflow
  change (finalCarry (inputLimb memory left) (inputLimb memory right) ≠ BitVec.ofNat 64 0) ↔ _ at overflow
  simp only [overflow]

#print axioms lanes_snapshot_fast_flag
end

section
open CIL.Safety CIL.Vector UInt256Model.Safety UInt256Proof.SIMD UInt256Proof.Reporting UInt256Proof.Add.Safety
/-- The repaired high mask gives overflow of the original caller operands. -/
theorem lanes_snapshot_repaired_flag (advSimd : Bool) (memory : Memory) (left right : Reference) (flag : BitVec 32) :
    (if lane64 (armRepairSnapshot (lanesDecisionValues advSimd memory left right flag) 6) 1 > BitVec.ofNat 64 0
      then (1 : BitVec 32) else 0) =
      if 2^256 ≤ (inputValue memory left).toNat + (inputValue memory right).toNat then 1 else 0 := by
  rw [lanes_repaired_snapshot_carry, repaired_high_flag]
  simp only [word_positive, ne_eq, BitVec.neg_eq_zero_iff]
  have overflow := finalCarry_overflow (inputLimb memory left) (inputLimb memory right)
  rw [input_limbs_value, input_limbs_value] at overflow
  change (finalCarry (inputLimb memory left) (inputLimb memory right) ≠ BitVec.ofNat 64 0) ↔ _ at overflow
  simp only [overflow]

#print axioms lanes_snapshot_repaired_flag
end

section
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety
/-- Complete ARM repair branch from saved initial-input snapshots to normal return, retaining the independent sum and caller memory guarantees. -/
theorem lanes_arm_repair_run (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (leadingLength : leading.length = 113)
    (code : body.code = leading ++ armRepairCode ++ tail)
    (repairSpecs : ∀ i : Fin 4, specs[19 + i.val]? = some vector128ZeroSpec)  (baseSpecs : ∀ i : Fin 14, specs[i.val]? = some vector128ZeroSpec)     (returns : body.returnsValue = true)  (enabled : body.profile.advSimd = true)
    (original entered current : Memory) (inputs outputs : List Reference)
    (left right output : Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (call : CallingConditions program original inputs outputs)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered original.nextIdentity specs slots)
    (authority : AccessBelow entered.nextIdentity entered current) (member : output ∈ outputs)
    (outputArg : args[2]? = some (.reference (.address output)))
    (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag) (flagArg : args[3]? = some (.scalar (.i32 flag)))
    (snapshots : ∀ i : Fin 14, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
      read current reference 16 1 = .ok (numberBytes (lanesDecisionValues body.profile.advSimd original left right flag i).toNat 16))
    (lowRead : read current output 16 1 = .ok (numberBytes (lanesSnapshotValue original left right 9).toNat 16))
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id) :
    ∃ fuel final returned,
      run program fuel method 113 args frame [] current = .ok (final, returned) ∧
      returned = [.scalar (.i32 (if 2^256 ≤ (inputValue original left).toNat + (inputValue original right).toNat then 1 else 0))] ∧
      inputValue final output = inputValue original left + inputValue original right ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = current.cells id offset) := by
  let post : Memory → List Value → Prop := fun final returned =>
    returned = [.scalar (.i32 (if 2^256 ≤ (inputValue original left).toNat + (inputValue original right).toNat then 1 else 0))] ∧
    inputValue final output = inputValue original left + inputValue original right ∧
    access final output 32 1 true = .ok () ∧
    (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
      final.cells id offset = current.cells id offset)
  apply vector128_arm_repair_checked program body method specs found leading tail leadingLength code repairSpecs baseSpecs enabled original.nextIdentity entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority flag flagFit flagArg (lanesDecisionValues body.profile.advSimd original left right flag) rfl snapshots post
  intro after repaired preserved afterCall afterAuthority advanced
  obtain ⟨carryHome, carrySlot, carryRead⟩ := repaired 6
  obtain ⟨highHome, highSlot, highRead⟩ := repaired 10
  change slots[6]? = _ at carrySlot
  change slots[10]? = _ at highSlot
  have actualCarry : frame.locals[7]? = some (.bytes .vector128 carryHome) := by simpa [layout] using carrySlot
  have actualHigh : frame.locals[11]? = some (.bytes .vector128 highHome) := by simpa [layout] using highSlot
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed member)
  have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  have savedLow := (preserved.read output old 16 1).trans lowRead
  obtain ⟨fuel, final, returned, executed, scalar, result, writable, outside⟩ :=
    vector128_arm_repair_result program body method found leading tail leadingLength code returns enabled original entered after inputs outputs output frame args
      call afterCall member afterAuthority outputArg (lanesSnapshotValue original left right 9)
      (armRepairSnapshot (lanesDecisionValues body.profile.advSimd original left right flag) 10)
      highHome actualHigh highRead savedLow carryHome
      (armRepairSnapshot (lanesDecisionValues body.profile.advSimd original left right flag) 6) actualCarry
      (homes.home_bound 6 .vector128 carryHome carrySlot) carryRead left right
      (lanes_snapshot_low original left right) (lanes_repaired_snapshot_high body.profile.advSimd original left right flag) owned
  rw [lanes_snapshot_repaired_flag] at scalar
  exact ⟨fuel, final, returned, executed, scalar, result, writable,
    fun id offset bound untouched => (outside id offset bound untouched).trans (preserved.cells id bound offset)⟩

#print axioms lanes_arm_repair_run
end

section
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety
theorem lanes_arm_entry_with_flag (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body)
    (startTail incomingTail leading correctionTail : List CIL.Op)
    (startCode : body.code = UInt256Proof.Add.SSEShapes.lanesPrefix ++ startTail)
    (incomingCode : body.code = lanesIncomingPrefix ++ incomingTail)
    (leadingLength : leading.length = 62)
    (correctionCodeFound : body.code = leading ++ correctionCode ++ correctionTail)
    (firstFourteen : ∀ i : Fin 14, specs[i.val]? = some vector128ZeroSpec)
    (sse : body.profile.advSimd = false → body.profile.sse2 = true)
    (ssse : body.profile.advSimd = false → body.profile.ssse3 = true)     (earlyLeading earlyTail : List CIL.Op) (earlyLength : earlyLeading.length = 69)
    (earlyCode : body.code = earlyLeading ++ earlyOutputCode body.profile.advSimd ++ earlyTail)     (propLeading propTail : List CIL.Op) (propLength : propLeading.length = 82)
    (propCode : body.code = propLeading ++ propagationCode ++ propTail)     (decisionLeading decisionTail : List CIL.Op) (decisionLength : decisionLeading.length = 94)
    (decisionCodeFound : body.code = decisionLeading ++ decisionCode body.profile.advSimd ++ decisionTail)     (fastLeading fastTail : List CIL.Op) (fastLength : fastLeading.length = 204)
    (fastCode : body.code = fastLeading ++ fastOutputCode body.profile.advSimd ++ fastTail)
    (returns : body.returnsValue = true)     (repairDispatchLeading repairDispatchTail : List CIL.Op) (repairDispatchLength : repairDispatchLeading.length = 111)
    (repairDispatchCode : body.code = repairDispatchLeading ++ [.feature .advSimd, .brzero 162] ++ repairDispatchTail)
    (repairLeading repairTail : List CIL.Op) (repairLength : repairLeading.length = 113)
    (repairCode : body.code = repairLeading ++ armRepairCode ++ repairTail)
    (repairSpecs : ∀ i : Fin 4, specs[19 + i.val]? = some vector128ZeroSpec) (enabled : body.profile.advSimd = true) (original entered : Memory)
    (inputs outputs : List Reference) (left right output : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions program original inputs outputs)
    (setup : enterFrame body args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity specs slots)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs) (outputMember : output ∈ outputs)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (outputArg : args[2]? = some (.reference (.address output)))
    (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag) (flagArg : args[3]? = some (.scalar (.i32 flag)))
    : ∃ fuel final returned,
      run program fuel method 0 args frame [] entered = .ok (final, returned) ∧
      (∃ returnedFlag : BitVec 32, returned = [.scalar (.i32 returnedFlag)] ∧ CIL.NarrowKind.unsigned8.extend returnedFlag = returnedFlag ∧
        (flag ≠ BitVec.ofNat 32 0 → returnedFlag =
          if 2^256 ≤ (inputValue original left).toNat + (inputValue original right).toNat then 1 else 0)) ∧
      inputValue final output = inputValue original left + inputValue original right ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = original.cells id offset) := by
  by_cases fast : selectedPropagation128 body.profile.advSimd flag (lanesBranchValue original left right 11)
      (lanesBranchValue original left right 12) = BitVec.ofNat 128 0
  · obtain ⟨fuel, final, returned, executed, scalar, result, writable, outside⟩ :=
      lanes_fast_entry program body method specs found startTail incomingTail leading correctionTail startCode incomingCode enabled leadingLength correctionCodeFound firstFourteen sse ssse earlyLeading earlyTail earlyLength earlyCode propLeading propTail propLength propCode decisionLeading decisionTail decisionLength decisionCodeFound fastLeading fastTail fastLength fastCode returns original entered inputs outputs left right output frame slots args
        call setup layout homes leftMember rightMember outputMember leftArg rightArg outputArg flag flagFit flagArg fast
    exact ⟨fuel, final, returned, executed, ⟨_, scalar, (by split <;> rfl), fun reporting => lanes_snapshot_fast_flag body.profile.advSimd original left right flag reporting fast⟩,
      result, writable, outside⟩
  · let post : Memory → List Value → Prop := fun final returned =>
      (∃ returnedFlag : BitVec 32, returned = [.scalar (.i32 returnedFlag)] ∧ CIL.NarrowKind.unsigned8.extend returnedFlag = returnedFlag ∧
        (flag ≠ BitVec.ofNat 32 0 → returnedFlag =
          if 2^256 ≤ (inputValue original left).toNat + (inputValue original right).toNat then 1 else 0)) ∧
      inputValue final output = inputValue original left + inputValue original right ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < original.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = original.cells id offset)
    apply lanes_dispatch_checked program body method specs found startTail incomingTail leading correctionTail startCode incomingCode enabled leadingLength correctionCodeFound firstFourteen sse ssse earlyLeading earlyTail earlyLength earlyCode propLeading propTail propLength propCode decisionLeading decisionTail decisionLength decisionCodeFound original entered inputs outputs left right output frame slots args
      call setup layout homes leftMember rightMember outputMember leftArg rightArg outputArg flag flagFit flagArg post
    intro current conditionHome conditionSlot conditionRead snapshots earlyRead currentCall authority footprint advanced _callerPreserved
    simp only [fast, ite_false]
    apply vector128_repair_dispatch program body method found repairDispatchLeading repairDispatchTail repairDispatchLength repairDispatchCode current (vector128SavedFrame frame slots right) args post
    simp only [vector128RepairStart, enabled, ite_true]
    have extended : ∀ i : Fin 14, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
        read current reference 16 1 = .ok (numberBytes (lanesDecisionValues body.profile.advSimd original left right flag i).toNat 16) := by
      intro i
      by_cases within : i.val < 13
      · obtain ⟨reference, slot, loaded⟩ := snapshots ⟨i.val, within⟩
        refine ⟨reference, slot, ?_⟩
        simpa only [lanesDecisionValues, dite_eq_left within] using loaded
      · have same : i = 13 := by omega
        subst i
        exact ⟨conditionHome, conditionSlot, conditionRead⟩
    have fresh := enterFrame_fresh _ _ _ _ _ setup
    obtain ⟨fuel, final, returned, executed, scalar, result, writable, outside⟩ :=
      lanes_arm_repair_run program body method specs found repairLeading repairTail repairLength repairCode repairSpecs firstFourteen returns enabled original entered current inputs outputs left right output
        (vector128SavedFrame frame slots right) (.root (some (.address right))) slots rfl args
        call currentCall (enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup) homes authority
        outputMember outputArg flag flagFit flagArg extended (earlyRead enabled).1
        (fun id member => (fresh.2 id member).1)
    exact ⟨fuel, final, returned, executed, ⟨_, scalar, (by split <;> rfl), fun _ => rfl⟩, result, writable,
      fun id offset bound untouched => (outside id offset bound untouched).trans (footprint id offset bound untouched)⟩

#print axioms lanes_arm_entry_with_flag
end

section
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety
theorem checked_lanes_arm_contract_with_flag (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body)
    (startTail incomingTail leading correctionTail : List CIL.Op)
    (startCode : body.code = UInt256Proof.Add.SSEShapes.lanesPrefix ++ startTail)
    (incomingCode : body.code = lanesIncomingPrefix ++ incomingTail)
    (leadingLength : leading.length = 62)
    (correctionCodeFound : body.code = leading ++ correctionCode ++ correctionTail)
    (firstFourteen : ∀ i : Fin 14, specs[i.val]? = some vector128ZeroSpec)
    (sse : body.profile.advSimd = false → body.profile.sse2 = true)
    (ssse : body.profile.advSimd = false → body.profile.ssse3 = true)     (earlyLeading earlyTail : List CIL.Op) (earlyLength : earlyLeading.length = 69)
    (earlyCode : body.code = earlyLeading ++ earlyOutputCode body.profile.advSimd ++ earlyTail)     (propLeading propTail : List CIL.Op) (propLength : propLeading.length = 82)
    (propCode : body.code = propLeading ++ propagationCode ++ propTail)     (decisionLeading decisionTail : List CIL.Op) (decisionLength : decisionLeading.length = 94)
    (decisionCodeFound : body.code = decisionLeading ++ decisionCode body.profile.advSimd ++ decisionTail)     (fastLeading fastTail : List CIL.Op) (fastLength : fastLeading.length = 204)
    (fastCode : body.code = fastLeading ++ fastOutputCode body.profile.advSimd ++ fastTail)
    (returns : body.returnsValue = true)     (repairDispatchLeading repairDispatchTail : List CIL.Op) (repairDispatchLength : repairDispatchLeading.length = 111)
    (repairDispatchCode : body.code = repairDispatchLeading ++ [.feature .advSimd, .brzero 162] ++ repairDispatchTail)
    (repairLeading repairTail : List CIL.Op) (repairLength : repairLeading.length = 113)
    (repairCode : body.code = repairLeading ++ armRepairCode ++ repairTail)
    (repairSpecs : ∀ i : Fin 4, specs[19 + i.val]? = some vector128ZeroSpec)     (metadata : body.localKinds = .reference :: specs.map NumericLocalSpec.kind ∧ body.locals = .nullRef :: specs.map NumericLocalSpec.value)
    (vectors : body.vectorArgs = []) (parameters : body.parameterHomes = []) (enabled : body.profile.advSimd = true)
    (memory : Memory) (left right output : Reference) (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag)
    (call : CallingConditions program memory [left, right] [output]) :
    ∃ fuel final returned,
      InvocationCertificate program method (vector128Arguments left right output flag)
        memory fuel final [.scalar (.i32 returned)] ∧
      inputValue final output = inputValue memory left + inputValue memory right ∧
      CIL.NarrowKind.unsigned8.extend returned = returned ∧
      (flag ≠ BitVec.ofNat 32 0 → returned =
        if 2^256 ≤ (inputValue memory left).toNat + (inputValue memory right).toNat then 1 else 0) ∧
      access final output 32 1 true = .ok () ∧
      (∀ id offset, id < memory.nextIdentity → OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset) := by
  let args := vector128Arguments left right output flag
  obtain ⟨frame, entered, slots, setup, layout, homes, preserved, enteredWF⟩ :=
    vector128_frame_setup body specs metadata vectors parameters memory args call.1.1
  obtain ⟨fuel, final, returned, executed, scalar, result, writable, footprint⟩ :=
    lanes_arm_entry_with_flag program body method specs found startTail incomingTail leading correctionTail startCode incomingCode leadingLength correctionCodeFound firstFourteen sse ssse earlyLeading earlyTail earlyLength earlyCode propLeading propTail propLength propCode decisionLeading decisionTail decisionLength decisionCodeFound fastLeading fastTail fastLength fastCode returns repairDispatchLeading repairDispatchTail repairDispatchLength repairDispatchCode repairLeading repairTail repairLength repairCode repairSpecs enabled memory entered [left, right] [output] left right output frame slots args
      call setup layout homes (by simp) (by simp) (by simp) rfl rfl rfl flag flagFit rfl
  obtain ⟨returnedValue, rfl, returnedFit, overflow⟩ := scalar
  have checked : args.mapM (checkedValue memory) = .ok args := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [args, vector128Arguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  exact ⟨fuel, final, returnedValue,
    certify_invocation program method body args memory frame entered
      fuel final [.scalar (.i32 returnedValue)] found checked setup live executed,
    result, returnedFit, overflow, writable, footprint⟩

#print axioms checked_lanes_arm_contract_with_flag
end

end UInt256Proof.Add.ARMLanes
