import UInt256.Methods.Add.SSEShapes.Decision
import UInt256.Methods.Add.Vector128FastEntry

namespace UInt256Proof.Add.SSEShapes
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety CIL.Vector

/-- SSE fast suffix placed at `base`: store both corrected halves and return the high-lane carry bit. -/
def sseFastCode (base : Nat) : List CIL.Op := [
  .feature .advSimd,
  .brnonzero (base + 11),
  .arg 2,
  .memory .asRef,
  .dup,
  .local 10,
  .memory .store128,
  .const32 1,
  .memory (.add 16 true),
  .local 11,
  .memory .store128,
  .local 7,
  .const32 1,
  .intrinsic (.vector (.extract64 128)) 2,
  .const32 0,
  .convI8,
  .gtu,
  .ret (some .unsigned8)]

/-- The fast suffix returns the saved high-lane carry bit and retires its frame. -/
theorem fast_return (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat)
    (leadingLength : leading.length = base)
    (code : body.code = leading ++ sseFastCode base ++ tail) (returns : body.returnsValue = true) (memory : Memory) (frame : Frame) (args : List Value)
    (home : Reference) (mask : BitVec 128)
    (slot : frame.locals[7]? = some (.bytes .vector128 home))
    (loaded : read memory home 16 1 = .ok (numberBytes mask.toNat 16)) :
    run program 7 method (base + 11) args frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if CIL.Vector.lane64 mask 1 > BitVec.ofNat 64 0 then 1 else 0))]) := by
  have load := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 mask) mask.toNat rfl slot loaded
  iterate 6
    normalize_pc
    apply Eq.trans
    · apply run_next found (by fetch_segment)
      first
      | exact load _ _
      | (simp (config := { implicitDefEqProofs := false })
          [localResult, checkedIntrinsic, step, pureArity, scalars, CIL.step.eq_def, CIL.binary,
            CIL.Intrinsic.available, CIL.Vector.intrinsic_extract128,
            checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
         first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)
  normalize_pc
  have fetched : body.code[base + 17]? = some (.ret (some .unsigned8)) := by fetch_segment
  by_cases carry : CIL.Vector.lane64 mask 1 > BitVec.ofNat 64 0
  all_goals simp [run, found, fetched, returns, step, checkedValue, numericValue, CIL.NarrowKind.extend, carry,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- SSE skips the ARM fast branch and writes the saved result halves. -/
theorem fast_output (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat)
    (leadingLength : leading.length = base)
    (code : body.code = leading ++ sseFastCode base ++ tail) (disabled : body.profile.advSimd = false)
    (original entered current : Memory)
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
      (read after output 16 1 = .ok (numberBytes low.toNat 16) ∧
        read after { output with offset := output.offset + 16 } 16 1 = .ok (numberBytes high.toNat 16)) →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = current.cells id offset) →
      (∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
        read current reference width alignment = .ok bytes → read after reference width alignment = .ok bytes) →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run program fuel method (base + 11) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method base args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨middle, after, firstWrite, secondWrite, firstRead, secondRead, middleCall, afterCall,
      afterAuthority, outside, privateReads, advanced⟩ :=
    output_halves_update program original entered current inputs outputs output low high
      call currentCall member authority
  have done := continuation after ⟨firstRead, secondRead⟩ afterCall afterAuthority outside
    (fun reference width alignment bytes bound loaded => (privateReads reference width alignment bytes bound loaded).2) advanced
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
  repeat' first
    | exact done
    | (normalize_pc
       apply run_next_exists post found (by fetch_segment)
       first
       | exact loadLow _ _
       | exact loadHigh _ _
       | (simp (config := { implicitDefEqProofs := false })
           [localResult, checkedIntrinsic, step, disabled, pureArity, scalars, CIL.step.eq_def, CIL.FeatureProfile.evaluate,
             argument, checkedValue, formValue, formed, staticInstruction, memoryInstruction,
             storeValue, referenceAt, firstWrite, secondWrite, address, CIL.offsetValue, numericValue,
             checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

/-- Complete fast suffix with initial-input arithmetic and surviving caller memory guarantees. -/
theorem fast_result (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat)
    (leadingLength : leading.length = base)
    (code : body.code = leading ++ sseFastCode base ++ tail) (disabled : body.profile.advSimd = false)
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
    (carryHome : Reference) (carry : BitVec 128)
    (carrySlot : frame.locals[7]? = some (.bytes .vector128 carryHome))
    (carryBound : original.nextIdentity ≤ carryHome.allocation)
    (carryRead : read current carryHome 16 1 = .ok (numberBytes carry.toNat 16))
    (left right : Reference) (flag : BitVec 32)
    (lowValue : low = vector128SnapshotValue original left right 9)
    (highValue : high = vector128SnapshotValue original left right 10)
    (fast : selectedPropagation128 false flag (vector128BranchValue original left right 11)
      (vector128BranchValue original left right 12) = BitVec.ofNat 128 0)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id) :
    ∃ fuel final returned,
      run program fuel method base args frame [] current = .ok (final, returned) ∧
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
  apply fast_output program body method found leading tail base leadingLength code disabled original entered current
    inputs outputs output frame args call currentCall member authority argument low high lowHome highHome lowSlot highSlot
    highBound lowRead highRead post
  intro after outputRead afterCall afterAuthority outside privateReads advanced
  refine ⟨7, _, _, fast_return program body method found leading tail base leadingLength code returns after frame args
    carryHome carry carrySlot (privateReads carryHome 16 1 _ carryBound carryRead), ?_⟩
  have teardown := leaveFrame_preserves_memory_below frame after original.nextIdentity owned
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed member)
  have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  have lo := (teardown.read output old 16 1).trans outputRead.1
  have hi := (teardown.read { output with offset := output.offset + 16 } old 16 1).trans outputRead.2
  obtain ⟨lowWords, highWords⟩ := vector128_snapshot_fast_words original left right false flag fast
  rw [lowValue, lowWords] at lo
  rw [highValue, highWords] at hi
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [output_value_of_packed_halves _ _ _ lo hi, UInt256Proof.sumWords_sum,
      input_limbs_value, input_limbs_value]
  · exact (teardown.access output old 32 1 true).trans
      (afterCall.1.2.2 (wordView output) (List.mem_map.mpr ⟨output, member, rfl⟩))
  · intro id offset earlier untouched
    exact (teardown.cells id earlier offset).trans (outside id offset untouched)

#print axioms fast_return
#print axioms fast_output
#print axioms fast_result
end UInt256Proof.Add.SSEShapes
