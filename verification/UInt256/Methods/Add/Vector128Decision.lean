import CIL.Safety.SymbolicExecution
import UInt256.Methods.Add.Vector128Propagation

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector
def decisionCode (adv : Bool) : List CIL.Op := if adv then [
.feature .advSimd,
.brzero 98,
.arg 3 (some .unsigned8),
.brzero 102,
.local 12,
.local 13,
.intrinsic (.vector (.bor 128)) 2,
.branch 106,
.local 12,
.local 13,
.const32 1,
.intrinsic (.advSimd .extract64) 3,
.setLocal 14,
.local 14,
.intrinsic (.vector (.zero 128)) 0,
.intrinsic (.vector (.equalsAll 128)) 2,
.brnonzero 204
] else [
.feature .advSimd,
.brzero 98,
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.local 12,
.local 13,
.intrinsic (.vector (.bor 128)) 2,
.branch 106,
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.setLocal 14,
.local 14,
.intrinsic (.vector (.zero 128)) 0,
.intrinsic (.vector (.equalsAll 128)) 2,
.brnonzero 204
]
/-- Follow the actual ISA/reporting choice and store the propagation condition. -/
theorem vector128_decision_checked (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (code : CodeAt body 94 (decisionCode body.profile.advSimd)) (specs : List NumericLocalSpec) (slotSpec : specs[13]? = some vector128ZeroSpec) (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag) (argument : args[3]? = some (.scalar (.i32 flag)))
    (low high : BitVec 128) (lowHome highHome : Reference)
    (lowSlot : frame.locals[12]? = some (.bytes .vector128 lowHome))
    (highSlot : frame.locals[13]? = some (.bytes .vector128 highHome))
    (lowRead : read current lowHome 16 1 = .ok (numberBytes low.toNat 16))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[14]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok (numberBytes (selectedPropagation128 body.profile.advSimd flag low high).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (selectedPropagation128 body.profile.advSimd flag low high).toNat 16) 1 = .ok after →
      ∃ fuel result returned,
        run program fuel method 107 args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 94 args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store program body specs boundary entered current inputs outputs frame root slots layout currentCall
      enteredWF homes authority 13 vector128ZeroSpec slotSpec
      (.v128 (selectedPropagation128 body.profile.advSimd flag low high)) (selectedPropagation128 body.profile.advSimd flag low high).toNat rfl
  have done := continuation reference after slot loaded retained afterCall afterAuthority written
  have loadLow := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 low) low.toNat rfl lowSlot lowRead
  have loadHigh := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 high) high.toNat rfl highSlot highRead
  cases selected : body.profile.advSimd <;> simp only [selected] at code <;> by_cases zero : flag = BitVec.ofNat 32 0
  all_goals
    simp only [selectedPropagation128, selected, zero, and_true, and_false, ite_true, ite_false,
      Bool.false_eq_true, false_and, true_and] at stored
    repeat'
      simp (config := { failIfUnchanged := false, implicitDefEqProofs := false }) only
        [localResult, Nat.reduceAdd, show CIL.NarrowKind.unsigned8.extend (0 : BitVec 32) = 0 from rfl,
         show (BitVec.setWidth 8 (1 : BitVec 32)).toNat = 1 from rfl,
         incoming128_arm_high, show (0 : BitVec 32) = BitVec.ofNat 32 0 from rfl,
         show (0 : BitVec 128) = BitVec.ofNat 128 0 from rfl, zero, ite_true, ite_false]
      first
      | exact done
      | (simp (config := { failIfUnchanged := false })
           [flagFit, show (0 : BitVec 32) = BitVec.ofNat 32 0 from rfl, zero]
         apply run_next_exists post found (by (conv => lhs; arg 2; whnf); cil_lookup [code])
         first
         | exact loadLow _ _
         | exact loadHigh _ _
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [localResult, checkedIntrinsic, step, cil_guard, observerCount, selected, flagFit, argument, pureArity, scalars, CIL.step.eq_def, CIL.FeatureProfile.evaluate,
               CIL.Intrinsic.available, CIL.Vector.intrinsic_or128, CIL.Vector.intrinsic_adv_extract,
               incoming128_arm_high, show (0 : BitVec 32) = BitVec.ofNat 32 0 from rfl, zero,
               checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
            try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)))

/-- Test only the initialized saved condition and expose both actual targets. -/
theorem vector128_decision_branch (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (code : CodeAt body 94 (decisionCode body.profile.advSimd)) (memory : Memory) (frame : Frame) (args : List Value)
    (home : Reference) (condition : BitVec 128)
    (slot : frame.locals[14]? = some (.bytes .vector128 home))
    (loaded : read memory home 16 1 = .ok (numberBytes condition.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method (if condition = BitVec.ofNat 128 0 then 204 else 111)
        args frame [] memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 107 args frame [] memory = .ok (result, returned) ∧ post result returned := by
  have load := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 condition) condition.toNat rfl slot loaded
  cases selected : body.profile.advSimd <;> simp only [selected] at code <;> by_cases zero : condition = BitVec.ofNat 128 0
  all_goals
    simp only [zero, ite_true, ite_false] at continuation
    iterate 4
      apply run_next_exists post found (by (conv => lhs; arg 2; whnf); cil_lookup [code])
      first
      | exact load _ _
      | (simp (config := { implicitDefEqProofs := false })
           [CIL.truth, Option.bind, List.mapM, localResult, checkedIntrinsic, step, cil_guard, observerCount, selected, pureArity, scalars, CIL.step.eq_def, CIL.Intrinsic.available,
             CIL.Vector.intrinsic_zero128, CIL.Vector.intrinsic_equal_all128,
             show (0 : BitVec 128) = BitVec.ofNat 128 0 from rfl, zero,
             checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
         try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))
    simpa only [List.reverse_nil, show (0 : BitVec 128) = BitVec.ofNat 128 0 from rfl, zero, ite_true, ite_false] using continuation
#print axioms vector128_decision_checked
#print axioms vector128_decision_branch
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Complete checked helper prefix through the actual fast/repair branch, preserving all saved values and any early ARM output writes. -/
theorem vector128_dispatch_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body)
    (startCode : CodeAt body 0 vector128AddPrefix)
    (incomingCode : CodeAt body 0 (incomingPrefix body.profile.advSimd))
    (correctionCodeFound : CodeAt body 62 correctionCode)
    (firstFourteen : ∀ i : Fin 14, specs[i.val]? = some vector128ZeroSpec)
    (sse : body.profile.advSimd = false → body.profile.sse2 = true)
    (ssse : body.profile.advSimd = false → body.profile.ssse3 = true)
    (earlyCode : CodeAt body 69 (earlyOutputCode body.profile.advSimd))
    (propCode : CodeAt body 82 (propagationCode))
    (decisionCodeFound : CodeAt body 94 (decisionCode body.profile.advSimd)) (original entered : Memory)
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
        (selectedPropagation128 body.profile.advSimd flag (vector128BranchValue original left right 11)
          (vector128BranchValue original left right 12)).toNat 16) →
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
        run program fuel method
          (if selectedPropagation128 body.profile.advSimd flag (vector128BranchValue original left right 11)
            (vector128BranchValue original left right 12) = BitVec.ofNat 128 0 then 204 else 111) args (vector128SavedFrame frame slots right) [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 0 args frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  apply vector128_ready_checked program body method specs found startCode incomingCode correctionCodeFound (fun i => firstFourteen ⟨i.val, by omega⟩) sse ssse earlyCode propCode original entered inputs outputs left right output frame slots args
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
  apply vector128_decision_checked program body method found decisionCodeFound specs (firstFourteen 13) original.nextIdentity entered current inputs outputs
    (vector128SavedFrame frame slots right) (.root (some (.address right))) slots rfl args currentCall
    (enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup) homes authority flag flagFit flagArg
    (vector128BranchValue original left right 11) (vector128BranchValue original left right 12)
    lowHome highHome actualLow actualHigh lowRead highRead post
  intro conditionHome after conditionSlot conditionRead preserved afterCall afterAuthority written
  have conditionTail : slots[13]? = some (.bytes .vector128 conditionHome) := by
    exact conditionSlot
  have retained : ∀ i : Fin 13, ∃ reference,
      slots[i.val]? = some (.bytes .vector128 reference) ∧
      read after reference 16 1 = .ok (numberBytes (vector128BranchValue original left right i).toNat 16) := by
    intro i
    obtain ⟨reference, slot, loaded⟩ := snapshots i
    exact ⟨reference, slot, vector128_prior_read specs entered current after original.nextIdentity slots homes
      i.val 13 i.isLt reference conditionHome slot conditionTail _ _ written loaded⟩
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed outputMember)
  have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  have retainedOutput : body.profile.advSimd = true →
      read after output 16 1 = .ok (numberBytes (vector128SnapshotValue original left right 9).toNat 16) ∧
      read after { output with offset := output.offset + 16 } 16 1 =
        .ok (numberBytes (vector128SnapshotValue original left right 10).toNat 16) := by
    intro enabled
    exact ⟨(preserved.read output old 16 1).trans (outputRead enabled).1,
      (preserved.read { output with offset := output.offset + 16 } old 16 1).trans (outputRead enabled).2⟩
  apply vector128_decision_branch program body method found decisionCodeFound after (vector128SavedFrame frame slots right) args conditionHome
    _ conditionSlot conditionRead post
  exact continuation after conditionHome conditionTail conditionRead retained retainedOutput afterCall afterAuthority
    (fun id offset bound outside => (preserved.cells id bound offset).trans (footprint id offset bound outside))
    (Nat.le_trans advanced (write_extends_allocations _ _ _ _ _ written).next)
    (fun disabled => (callerPreserved disabled).trans preserved)

#print axioms vector128_dispatch_checked
end UInt256Proof.Add.Safety
