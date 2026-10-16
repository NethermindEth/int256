import UInt256.Methods.Add.Vector128Snapshots
import UInt256.Safety.OutputHalves

namespace UInt256Proof.Add.Safety
def earlyOutputCode (adv : Bool) : List CIL.Op := if adv then [
.arg 2,
.skipInit,
.feature .advSimd,
.brzero 82,
.arg 2,
.memory .asRef,
.dup,
.local 10,
.memory .store128,
.const32 1,
.memory (.add 16 true),
.local 11,
.memory .store128
] else [
.arg 2,
.skipInit,
.feature .advSimd,
.brzero 82,
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile"
]
end UInt256Proof.Add.Safety
namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def vector128EarlyOutputStart (body : CIL.Method) : Nat := if body.profile.advSimd then 73 else 82

/-- SkipInit checks the output reference but neither initializes nor reads its bytes. -/
theorem vector128_output_dispatch (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (leadingLength : leading.length = 69)
    (code : body.code = leading ++ earlyOutputCode body.profile.advSimd ++ tail) (memory : Memory) (output : Reference)
    (frame : Frame) (args : List Value)
    (argument : args[2]? = some (.reference (.address output)))
    (formed : form memory output = .ok output)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method (vector128EarlyOutputStart body) args frame [] memory =
        .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 69 args frame [] memory =
        .ok (result, returned) ∧ post result returned := by
  cases selected : body.profile.advSimd <;> simp only [vector128EarlyOutputStart, selected, Bool.false_eq_true, ite_false, ite_true] at continuation ⊢
  all_goals repeat' first
    | exact continuation
    | (apply run_next_exists post found (by simp [code, List.getElem?_append, leadingLength, earlyOutputCode, selected]; rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, selected, argument, checkedValue, formValue, formed, instruction,
           pureArity, scalars, CIL.step.eq_def, CIL.FeatureProfile.evaluate,
           numericValue, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

#print axioms vector128_output_dispatch
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- ARM performs its two early output writes from saved private values; SSE reaches the common continuation without a write. -/
theorem vector128_early_output (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (leadingLength : leading.length = 69)
    (code : body.code = leading ++ earlyOutputCode body.profile.advSimd ++ tail) (original entered current : Memory)
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
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      (body.profile.advSimd = true → read after output 16 1 = .ok (numberBytes low.toNat 16) ∧
        read after { output with offset := output.offset + 16 } 16 1 = .ok (numberBytes high.toNat 16)) →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = current.cells id offset) →
      (∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
        read current reference width alignment = .ok bytes → read after reference width alignment = .ok bytes) →
      current.nextIdentity ≤ after.nextIdentity →
      (body.profile.advSimd = false → after = current) →
      ∃ fuel result returned,
        run program fuel method 82 args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (vector128EarlyOutputStart body) args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  cases selected : body.profile.advSimd
  case false =>
    have disabled : body.profile.advSimd = false := selected
    simp only [vector128EarlyOutputStart, selected, Bool.false_eq_true, ite_false]
    exact continuation current (by intro enabled; rw [disabled] at enabled; contradiction)
      currentCall authority (by intros; rfl) (by intros; assumption) (Nat.le_refl _) (fun _ => rfl)
  case true =>
    obtain ⟨middle, after, firstWrite, secondWrite, firstRead, secondRead, middleCall, afterCall,
        afterAuthority, outside, privateReads, advanced⟩ :=
      output_halves_update program original entered current inputs outputs output low high
        call currentCall member authority
    have done := continuation after (fun _ => ⟨firstRead, secondRead⟩) afterCall afterAuthority outside
      (fun reference width alignment bytes bound loaded => (privateReads reference width alignment bytes bound loaded).2) advanced
      (by intro disabled; rw [selected] at disabled; contradiction)
    have loadLow := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 low) low.toNat rfl lowSlot lowRead
    have loadHigh := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 high) high.toNat rfl highSlot
      (privateReads highHome 16 1 _ highBound highRead).1
    have formed := currentCall.output_formed member
    have address := middleCall.output_half_address member 1
    simp only [Fin.val_one, Nat.mul_one] at address
    simp only [vector128EarlyOutputStart, selected, ite_true]
    all_goals repeat' first
      | exact done
      | (apply run_next_exists post found (by simp [code, List.getElem?_append, leadingLength, earlyOutputCode, selected]; rfl)
         first
         | exact loadLow _ _
         | exact loadHigh _ _
         | (simp (config := { implicitDefEqProofs := false })
             [localResult, step, argument, checkedValue, formValue, formed, staticInstruction, memoryInstruction,
               storeValue, referenceAt, firstWrite, secondWrite, address, CIL.offsetValue,
               checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_early_output
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety
/-- Execution from helper entry through the ISA-dependent early output stage. -/
theorem vector128_output_prefix (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body)
    (startTail incomingTail leading correctionTail : List CIL.Op)
    (startCode : body.code = vector128AddPrefix ++ startTail)
    (incomingCode : body.code = incomingPrefix body.profile.advSimd ++ incomingTail)
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
        read after reference 16 1 = .ok (numberBytes (vector128SnapshotValue original left right i).toNat 16)) →
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
        run program fuel method 82 args (vector128SavedFrame frame slots right) [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 0 args frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  apply vector128_snapshots_checked program body method specs found startTail incomingTail leading correctionTail startCode incomingCode leadingLength correctionCodeFound firstEleven sse ssse original entered inputs outputs left right frame slots args call setup
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
