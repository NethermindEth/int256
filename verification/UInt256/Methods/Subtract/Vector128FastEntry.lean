import UInt256.Methods.Subtract.Vector128Decision
import UInt256.Safety.OutputHalves
import UInt256.Methods.Subtract.Vector128Dispatch
import UInt256.Arithmetic.SIMDBorrow
import UInt256.Safety.HalfRepresentation
import UInt256.Methods.Subtract.BorrowArithmetic
import UInt256.Safety.HalfOutputValue
import CIL.Safety.ReturnMemory

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- The fast suffix returns the saved high-lane borrow mask and retires its frame.
    The arithmetic meaning of this flag is established separately from stepping. -/
theorem vector128_fast_return (memory : Memory) (frame : Frame) (args : List Value)
    (home : Reference) (mask : BitVec 128)
    (slot : frame.locals[8]? = some (.bytes .vector128 home))
    (loaded : read memory home 16 1 = .ok (numberBytes mask.toNat 16)) :
    run Extracted.program 7 vector128Index 134 args frame [] memory =
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
  have fetched : vector128Body.code[140]? = some .ret := by rfl
  simp [run, found, fetched, returns, step, checkedValue, numericValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms vector128_fast_return
end UInt256Proof.Subtract.Safety

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

namespace UInt256Proof.Subtract.Safety
open CIL.Safety CIL.Vector UInt256Model UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- The checked branch expression is exactly the independent arithmetic
    propagation test over the original input limbs. -/
theorem vector128_initial_propagation (memory : Memory) (left right : Reference) :
    vector128InitialPropagation memory left right =
      UInt256Proof.propagation128 (inputLimb memory left) (inputLimb memory right) := by
  simp [vector128InitialPropagation, vector128Propagation, vector128IncomingValue,
    vector128PreparedValue, vector128InputValues, vector128BinaryValue,
    input_half_low, input_half_high, incoming128Low, incoming128High,
    zip128, lane128_0, lane128_1, pack128_zero, pack128_and, pack128_or,
    UInt256Proof.propagation128, UInt256Proof.zeroDifferenceMask, UInt256Proof.borrowMask,
    CIL.fin_val_three,
    show (4 : Fin 10).val = 4 from rfl,
    show (5 : Fin 10).val = 5 from rfl,
    show (8 : Fin 10).val = 8 from rfl,
    show (9 : Fin 10).val = 9 from rfl,
    show (4 : Fin 8).val = 4 from rfl,
    show (5 : Fin 8).val = 5 from rfl,
    show (6 : Fin 8).val = 6 from rfl,
    show (7 : Fin 8).val = 7 from rfl]

  rfl

theorem vector128_no_borrow_propagation (memory : Memory) (left right : Reference)
    (fast : vector128InitialPropagation memory left right = BitVec.ofNat 128 0) :
    UInt256Proof.NoBorrowPropagation (inputLimb memory left) (inputLimb memory right) := by
  rw [vector128_initial_propagation] at fast
  exact UInt256Proof.propagation128_zero _ _ fast

def vector128Corrected (memory : Memory) (left right : Reference) (upper : Bool) : BitVec 128 :=
  let values := vector128IncomingValue (vector128InputValues memory left right)
  zip128 (· + ·) (values (if upper then 5 else 4)) (values (if upper then 9 else 8))

theorem vector128_corrected_words (memory : Memory) (left right : Reference) (upper : Bool) :
    vector128Corrected memory left right upper =
      let words := UInt256Proof.speculativeDifference (inputLimb memory left) (inputLimb memory right)
      pack128 (words (if upper then 2 else 0)) (words (if upper then 3 else 1)) := by
  have correction (x y result : BitVec 64) : result + mask64 (x.ult y) =
      result - UInt256Proof.independentBorrow x y := UInt256Proof.borrow_mask_subtract_raw x y result
  cases upper <;>
    simp [vector128Corrected, vector128IncomingValue, vector128PreparedValue, vector128InputValues,
      vector128BinaryValue, input_half_low, input_half_high, incoming128Low, incoming128High,
      zip128, lane128_0, lane128_1, correction, UInt256Proof.speculativeDifference, CIL.fin_val_three,
      show (4 : Fin 10).val = 4 from rfl, show (5 : Fin 10).val = 5 from rfl,
      show (8 : Fin 10).val = 8 from rfl, show (9 : Fin 10).val = 9 from rfl,
      show (6 : Fin 8).val = 6 from rfl, show (7 : Fin 8).val = 7 from rfl]


theorem vector128_corrected_difference (memory : Memory) (left right : Reference) (upper : Bool)
    (fast : vector128InitialPropagation memory left right = BitVec.ofNat 128 0) :
    vector128Corrected memory left right upper =
      pack128 (scalarDifferenceWord memory left right (if upper then 2 else 0))
        (scalarDifferenceWord memory left right (if upper then 3 else 1)) := by
  rw [vector128_corrected_words,
    UInt256Proof.speculative_difference_words _ _ (vector128_no_borrow_propagation memory left right fast),
    ← scalar_difference_words]

def vector128FastFlag (memory : Memory) (left right : Reference) : BitVec 32 :=
  let highMask := vector128IncomingValue (vector128InputValues memory left right) 7
  if BitVec.ofNat 64 0 < lane64 highMask 1 then BitVec.ofNat 32 1 else BitVec.ofNat 32 0

theorem vector128_fast_flag (memory : Memory) (left right : Reference)
    (fast : vector128InitialPropagation memory left right = BitVec.ofNat 128 0) :
    vector128FastFlag memory left right = subtractUnderflow memory left right := by
  have mask : lane64 (vector128IncomingValue (vector128InputValues memory left right) 7) 1 =
      UInt256Proof.borrowMask (inputLimb memory left 3) (inputLimb memory right 3) := by
    simp [vector128IncomingValue, vector128PreparedValue, vector128InputValues, vector128BinaryValue,
      input_half_low, input_half_high, zip128, lane128_0, lane128_1,
      show (7 : Fin 10).val = 7 from rfl, UInt256Proof.borrowMask]
    rfl
  have chain := (UInt256Proof.independent_borrow_chain _ _
    (vector128_no_borrow_propagation memory left right fast)).2.2
  change scalarBorrowValue memory left right 4 =
    UInt256Proof.independentBorrow (inputLimb memory left 3) (inputLimb memory right 3) at chain
  dsimp only [vector128FastFlag]
  rw [mask, UInt256Proof.borrow_mask_flag, ← chain]
  change _ = if (inputValue memory left).toNat < (inputValue memory right).toNat then 1 else 0
  rw [← scalar_flag_underflow]
  simp [scalarUnderflowFlag, BitVec.pos_iff_ne_zero]

#print axioms vector128_fast_flag
#print axioms vector128_corrected_words
#print axioms vector128_corrected_difference
#print axioms vector128_initial_propagation
#print axioms vector128_no_borrow_propagation
end UInt256Proof.Subtract.Safety

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

theorem vector128_fast_entry (original entered : Memory)
    (left right output : Reference) (frame : Frame) (slots : List LocalSlot)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame vector128Body (binaryArguments left right output) original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity vector128Specs slots)
    (fast : vector128InitialPropagation original left right = BitVec.ofNat 128 0) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 0 (binaryArguments left right output) frame [] entered =
        .ok (final, returned) ∧ SubtractResult original final returned left right output := by
  let args := binaryArguments left right output
  let post := fun final returned => SubtractResult original final returned left right output
  let values := vector128IncomingValue (vector128InputValues original left right)
  apply vector128_dispatch original entered [left, right] [output] left right frame slots args
    call setup layout homes (by simp) (by simp) (by rfl) (by rfl) post
  intro current snapshots preserved currentCall authority advanced
  simp only [fast, ite_true]
  obtain ⟨lowHome, lowSlot, lowRead⟩ := snapshots 4
  obtain ⟨highHome, highSlot, highRead⟩ := snapshots 5
  obtain ⟨incomingLowHome, incomingLowSlot, incomingLowRead⟩ := snapshots 8
  obtain ⟨incomingHighHome, incomingHighSlot, incomingHighRead⟩ := snapshots 9
  obtain ⟨maskHome, maskSlot, maskRead⟩ := snapshots 7
  apply vector128_fast_output original entered current [left, right] [output] output
    (vector128SavedFrame frame slots right) args call currentCall (by simp) authority (by rfl)
    (values 4) (values 5) (values 8) (values 9) lowHome highHome incomingLowHome incomingHighHome
    lowSlot highSlot (homes.home_bound 5 .vector128 highHome highSlot) lowRead highRead
    incomingLowSlot incomingHighSlot (homes.home_bound 9 .vector128 incomingHighHome incomingHighSlot)
    incomingLowRead incomingHighRead post
  intro after outputRead afterCall afterAuthority outside privateReads next
  have saved := privateReads maskHome 16 1 _ (homes.home_bound 7 .vector128 maskHome maskSlot) maskRead
  have teardown := leaveFrame_preserves_memory_below (vector128SavedFrame frame slots right) after original.nextIdentity
    (fun id member => ((enterFrame_fresh _ _ _ _ _ setup).2 id member).1)
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed (by simp : output ∈ [output]))
  have old : output.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
  have lo := (teardown.read output old 16 1).trans outputRead.1
  have hi := (teardown.read { output with offset := output.offset + 16 } old 16 1).trans outputRead.2
  change read _ output 16 1 = .ok (numberBytes (vector128Corrected original left right false).toNat 16) at lo
  change read _ { output with offset := output.offset + 16 } 16 1 =
    .ok (numberBytes (vector128Corrected original left right true).toNat 16) at hi
  rw [vector128_corrected_difference original left right false fast] at lo
  rw [vector128_corrected_difference original left right true fast] at hi
  refine ⟨7, leaveFrame (vector128SavedFrame frame slots right) after,
    [.scalar (.i32 (vector128FastFlag original left right))], ?_, ?_⟩
  · exact vector128_fast_return after (vector128SavedFrame frame slots right) args maskHome (values 7) maskSlot saved
  · refine ⟨leaveFrame_preserves_wellFormed _ _ afterCall.1.1, ?_, ?_, ?_, ?_⟩
    · have computed := output_value_of_packed_halves _ output (scalarDifferenceWord original left right) lo hi
      exact computed.trans (scalar_difference_value original left right)
    · rw [vector128_fast_flag original left right fast]
    · exact (teardown.access output old 32 1 true).trans
        (afterCall.1.2.2 (wordView output) (by simp))
    · intro id earlier offset untouched
      exact (teardown.cells id earlier offset).trans
        ((outside id offset untouched).trans (preserved.cells id earlier offset))

#print axioms vector128_fast_entry
end UInt256Proof.Subtract.Safety
