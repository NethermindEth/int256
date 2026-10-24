import UInt256.Methods.Add.Vector128EarlyOutput

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety
def propagationCode : List CIL.Op := [
.local 10,
.intrinsic (.vector (.zero 128)) 0,
.intrinsic (.vector (.eq64 128)) 2,
.local 8,
.intrinsic (.vector (.band 128)) 2,
.setLocal 12,
.local 11,
.intrinsic (.vector (.zero 128)) 0,
.intrinsic (.vector (.eq64 128)) 2,
.local 9,
.intrinsic (.vector (.band 128)) 2,
.setLocal 13
]
/-- Detect a carry that propagated through a corrected zero lane, using saved initialized vectors after any overlapping early output write. -/
theorem vector128_propagation_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (leadingLength : leading.length = 82)
    (code : body.code = leading ++ propagationCode ++ tail)
    (slotsSpec : specs[11]? = some vector128ZeroSpec ∧ specs[12]? = some vector128ZeroSpec) (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs slots)
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
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (propagating128 result incoming).toNat 16) 1 = .ok after →
      ∃ fuel final returned,
        run program fuel method (if upper then 94 else 88) args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method (if upper then 88 else 82) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have specified : specs[if upper then 12 else 11]? = some vector128ZeroSpec := by
    cases upper <;> exact (by first | exact slotsSpec.1 | exact slotsSpec.2)
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store program body specs boundary entered current inputs outputs frame root slots layout currentCall
      enteredWF homes authority _ vector128ZeroSpec specified
      (.v128 (propagating128 result incoming)) (propagating128 result incoming).toNat rfl
  have actual : frame.locals[if upper then 13 else 12]? = some (.bytes .vector128 reference) := by
    cases upper <;> exact slot
  have done := continuation reference after actual loaded retained afterCall afterAuthority written
  have loadResult := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 result) result.toNat rfl resultSlot resultRead
  have loadIncoming := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 incoming) incoming.toNat rfl incomingSlot incomingRead
  cases upper <;> simp only [Bool.false_eq_true, ite_false, ite_true] at stored loadResult loadIncoming done ⊢
  all_goals
    repeat' first
      | exact done
      | (apply run_next_exists post found (by simp [code, List.getElem?_append, leadingLength, propagationCode]; rfl)
         first
         | exact loadResult _ _
         | exact loadIncoming _ _
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, cil_guard, observerCount, pureArity, scalars, CIL.step.eq_def, CIL.Intrinsic.available,
               CIL.Vector.intrinsic_zero128, CIL.Vector.intrinsic_eq128, CIL.Vector.intrinsic_and128,
               propagating128, checkedValue, numericValue,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_propagation_checked
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Compose both propagation masks while retaining every earlier vector home and all older caller storage, including ARM's early output readbacks. -/
theorem vector128_propagation_pair (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (leadingLength : leading.length = 82)
    (code : body.code = leading ++ propagationCode ++ tail)
    (slotsSpec : specs[11]? = some vector128ZeroSpec ∧ specs[12]? = some vector128ZeroSpec) (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs slots)
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
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run program fuel method 94 args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 82 args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  have actualLow : frame.locals[10]? = some (.bytes .vector128 lowHome) := by simpa [layout] using lowSlot
  have actualHigh : frame.locals[11]? = some (.bytes .vector128 highHome) := by simpa [layout] using highSlot
  have actualLowIncoming : frame.locals[8]? = some (.bytes .vector128 lowIncoming) := by simpa [layout] using lowIncomingSlot
  have actualHighIncoming : frame.locals[9]? = some (.bytes .vector128 highIncoming) := by simpa [layout] using highIncomingSlot
  apply vector128_propagation_checked program body method specs found leading tail leadingLength code slotsSpec boundary entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority false low incomingLow lowHome lowIncoming actualLow actualLowIncoming lowRead lowIncomingRead post
  intro lowMask middle lowLocal lowLoaded preserved middleCall middleAuthority firstWrite
  have lowTail : slots[11]? = some (.bytes .vector128 lowMask) := by simpa [layout] using lowLocal
  have savedHigh := vector128_prior_read specs entered current middle boundary slots homes 10 11 (by decide)
    highHome lowMask highSlot lowTail _ _ firstWrite highRead
  have savedIncoming := vector128_prior_read specs entered current middle boundary slots homes 8 11 (by decide)
    highIncoming lowMask highIncomingSlot lowTail _ _ firstWrite highIncomingRead
  apply vector128_propagation_checked program body method specs found leading tail leadingLength code slotsSpec boundary entered middle inputs outputs frame root slots layout args
    middleCall enteredWF homes middleAuthority true high incomingHigh highHome highIncoming actualHigh actualHighIncoming savedHigh savedIncoming post
  intro highMask after highLocal highLoaded kept afterCall afterAuthority secondWrite
  have highTail : slots[12]? = some (.bytes .vector128 highMask) := by simpa [layout] using highLocal
  have lower := vector128_prior_read specs entered middle after boundary slots homes 11 12 (by decide)
    lowMask highMask lowTail highTail _ _ secondWrite lowLoaded
  have earlier : ∀ i, i < 11 → ∀ reference bytes,
      slots[i]? = some (.bytes .vector128 reference) →
      read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes := by
    intro i bound reference bytes slot loaded
    exact vector128_prior_read specs entered middle after boundary slots homes i 12 (by omega)
      reference highMask slot highTail _ _ secondWrite
      (vector128_prior_read specs entered current middle boundary slots homes i 11 bound
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

/-- Entry through the propagation decision, with all thirteen saved values tied to the initial inputs and early ARM output readbacks still valid. -/
theorem vector128_ready_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body)
    (startTail incomingTail leading correctionTail : List CIL.Op)
    (startCode : body.code = vector128AddPrefix ++ startTail)
    (incomingCode : body.code = incomingPrefix body.profile.advSimd ++ incomingTail)
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
        read after reference 16 1 = .ok (numberBytes (vector128BranchValue original left right i).toNat 16)) →
      (body.profile.advSimd = true →
        read after output 16 1 = .ok (numberBytes (vector128SnapshotValue original left right 9).toNat 16) ∧
        read after { output with offset := output.offset + 16 } 16 1 =
          .ok (numberBytes (vector128SnapshotValue original left right 10).toNat 16)) →
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
  apply vector128_output_prefix program body method specs found startTail incomingTail leading correctionTail startCode incomingCode leadingLength correctionCodeFound (fun i => firstThirteen ⟨i.val, by omega⟩) sse ssse earlyLeading earlyTail earlyLength earlyCode original entered inputs outputs left right output frame slots args call setup
    layout homes leftMember rightMember outputMember leftArg rightArg outputArg post
  intro current snapshots outputRead currentCall authority footprint advanced callerPreserved
  obtain ⟨lowHome, lowSlot, lowRead⟩ := snapshots 9
  obtain ⟨highHome, highSlot, highRead⟩ := snapshots 10
  obtain ⟨lowIncoming, lowIncomingSlot, lowIncomingRead⟩ := snapshots 7
  obtain ⟨highIncoming, highIncomingSlot, highIncomingRead⟩ := snapshots 8
  apply vector128_propagation_pair program body method specs found propLeading propTail propLength propCode ⟨firstThirteen 11, firstThirteen 12⟩ original.nextIdentity entered current inputs outputs
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
  have retainedOutput : body.profile.advSimd = true →
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
