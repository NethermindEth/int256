import Extracted
import CIL.Safety.NumericHomes
import UInt256.Safety.ReadOnlyExecution
import UInt256.Methods.Compare.MaskSafety
import UInt256.Methods.Compare.VectorMasks
import CIL.Safety.CallComposition
import CIL.Safety.StepComposition
import UInt256.Safety.ReadOnlyForwarder

namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety

def portableIndex : Nat := Extracted.program.findIdx fun body => body.code.any fun op =>
  match op with | .intrinsic (.vector (.extractMSB64 256)) _ => true | _ => false

def portableBody : CIL.Method := Extracted.program[portableIndex]?.getD
  { code := [], locals := [], returnsValue := false }

def portableSpecs : List NumericLocalSpec :=
  [⟨.vector256, .v256 0, 0, by rfl⟩, ⟨.word32, .i32 0, 0, by rfl⟩,
   ⟨.word32, .i32 0, 0, by rfl⟩]

/-- Prepare the three extracted local homes with distinct identities, without
replacing caller inputs by disjoint synthetic values. -/
theorem portable_setup (memory : Memory) (left right : Reference)
    (call : CallingConditions Extracted.program memory [left, right] []) :
    ∃ frame entered,
      enterFrame portableBody (readOnlyArguments [left, right]) memory = .ok (frame, entered) ∧
      NumericHomes entered memory.nextIdentity portableSpecs frame.locals ∧
      CallingConditions Extracted.program entered [left, right] [] ∧
      MemoryBelow memory.nextIdentity memory entered := by
  obtain ⟨slots, owned, entered, made, homes⟩ :=
    make_numeric_locals memory memory.nextIdentity portableSpecs call.1.1
  let frame : Frame := ⟨memory.nextIdentity, slots, owned, []⟩
  have kinds : portableBody.localKinds = numericKinds portableSpecs := by rfl
  have values : portableBody.locals = numericInitializers portableSpecs := by rfl
  have aggregates : portableBody.aggregateArgs = [] := by rfl
  have setup : enterFrame portableBody (readOnlyArguments [left, right]) memory = .ok (frame, entered) := by
    simp [enterFrame, kinds, values, aggregates, made, makeArgumentHomes, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact ⟨frame, entered, setup, homes, call.after_frame_setup setup,
    enterFrame_preserves_caller_memory _ _ _ _ _ setup⟩

#print axioms portable_setup
end UInt256Proof.Compare.Safety

namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety

/-- Three private writes retain caller bytes and the earlier local snapshots. -/
theorem portable_local_writes (memory : Memory) (frame : Frame) (lower : Nat)
    (homes : NumericHomes memory lower portableSpecs frame.locals)
    (vector : BitVec 256) (equal less : BitVec 32) :
    ∃ vectorRef equalRef lessRef first second final,
      frame.locals = [.bytes .vector256 vectorRef, .bytes .word32 equalRef, .bytes .word32 lessRef] ∧
      storeLocal memory (.bytes .vector256 vectorRef) (.scalar (.v256 vector)) =
        .ok (.bytes .vector256 vectorRef, first) ∧
      storeLocal first (.bytes .word32 equalRef) (.scalar (.i32 equal)) =
        .ok (.bytes .word32 equalRef, second) ∧
      storeLocal second (.bytes .word32 lessRef) (.scalar (.i32 less)) =
        .ok (.bytes .word32 lessRef, final) ∧
      loadLocal first (.bytes .vector256 vectorRef) = .ok (.scalar (.v256 vector)) ∧
      loadLocal second (.bytes .vector256 vectorRef) = .ok (.scalar (.v256 vector)) ∧
      loadLocal final (.bytes .word32 equalRef) = .ok (.scalar (.i32 equal)) ∧
      loadLocal final (.bytes .word32 lessRef) = .ok (.scalar (.i32 less)) ∧
      MemoryBelow lower memory first ∧ MemoryBelow lower memory second ∧
      MemoryBelow lower memory final := by
  rcases frame with ⟨activation, slots, owned, arguments⟩
  cases homes with
  | cons vectorRef vectorSpec vectorFresh vectorRead vectorAccess tail =>
    cases tail with
    | cons equalRef equalSpec equalFresh equalRead equalAccess tail =>
      cases tail with
      | cons lessRef lessSpec lessFresh lessRead lessAccess tail =>
        cases tail
        obtain ⟨first, w0, s0, r0⟩ := store_numeric_local .vector256 (.v256 vector) vector.toNat rfl vectorAccess
        obtain ⟨equalAllocation, equalReady⟩ := access_requirements equalAccess
        obtain ⟨lessAllocation, lessReady⟩ := access_requirements lessAccess
        obtain ⟨second, w1, s1, r1⟩ := store_numeric_local .word32 (.i32 equal) equal.toNat rfl
          (equalReady.after_write w0).access
        obtain ⟨final, w2, s2, r2⟩ := store_numeric_local .word32 (.i32 less) less.toNat rfl
          ((lessReady.after_write w0).after_write w1).access
        have ve : vectorRef.allocation < equalRef.allocation := equalFresh
        have el : equalRef.allocation < lessRef.allocation := lessFresh
        have r0after := write_preserves_disjoint_read w1 r0 (Or.inl (Nat.ne_of_lt ve))
        have r1after := write_preserves_disjoint_read w2 r1 (Or.inl (Nat.ne_of_lt el))
        have below0 := write_preserves_memory_below _ _ _ _ _ lower vectorFresh w0
        have below1 := write_preserves_memory_below _ _ _ _ _ lower
          (Nat.le_trans vectorFresh (Nat.le_of_lt ve)) w1
        have below2 := write_preserves_memory_below _ _ _ _ _ lower
          (Nat.le_trans vectorFresh (Nat.le_trans (Nat.le_of_lt ve) (Nat.le_of_lt el))) w2
        exact ⟨vectorRef, equalRef, lessRef, first, second, final, rfl, s0, s1, s2,
          load_numeric_local .vector256 (.v256 vector) vector.toNat rfl r0,
          load_numeric_local .vector256 (.v256 vector) vector.toNat rfl r0after,
          load_numeric_local .word32 (.i32 equal) equal.toNat rfl r1after,
          load_numeric_local .word32 (.i32 less) less.toNat rfl r2,
          below0, below0.trans below1, (below0.trans below1).trans below2⟩

#print axioms portable_local_writes
end UInt256Proof.Compare.Safety

namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety

def portableEqual (left right : BitVec 256) : BitVec 32 :=
  CIL.Vector.moveMask64 (CIL.Vector.zip256 (fun x y => CIL.Vector.mask64 (x == y)) left right)
def portableLess (left right : BitVec 256) : BitVec 32 :=
  CIL.Vector.moveMask64 (CIL.Vector.zip256 (fun x y => CIL.Vector.mask64 (x.ult y)) left right)

theorem portable_run (memory : Memory) (left right : Reference) (frame : Frame) (lower : Nat)
    (homes : NumericHomes memory lower portableSpecs frame.locals)
    (call : CallingConditions Extracted.program memory [left, right] []) :
    ∃ fuel final,
      run Extracted.program fuel portableIndex 0 (readOnlyArguments [left, right]) frame [] memory =
        .ok (leaveFrame frame final, [.scalar (.i32 (maskResult
          (portableEqual (inputValue memory left) (inputValue memory right))
          (portableLess (inputValue memory left) (inputValue memory right))))]) ∧
      MemoryBelow lower memory final := by
  let x := inputValue memory left
  let y := inputValue memory right
  let eqWord := portableEqual x y
  let ltWord := portableLess x y
  obtain ⟨vr, er, lr, m0, m1, m2, slots, s0, s1, s2, r0, r0after, r1, r2, _, _, preserved⟩ :=
    portable_local_writes memory frame lower homes y eqWord ltWord
  have slot0 : frame.locals[0]? = some (.bytes .vector256 vr) := by simp [slots]
  have slot1 : frame.locals[1]? = some (.bytes .word32 er) := by simp [slots]
  have slot2 : frame.locals[2]? = some (.bytes .word32 lr) := by simp [slots]
  have duplicate (m : Memory) (bits : BitVec 256) (rest : List Value) :
      instruction .dup (.scalar (.v256 bits) :: rest) m =
        .ok (m, .scalar (.v256 bits) :: .scalar (.v256 bits) :: rest) := by
    simp [instruction, checkedValue, numericValue, Pure.pure, Except.pure]
  have keep0 : frame.locals.set 0 (.bytes .vector256 vr) = frame.locals := by simp [slots]
  have keep1 : frame.locals.set 1 (.bytes .word32 er) = frame.locals := by simp [slots]
  have keep2 : frame.locals.set 2 (.bytes .word32 lr) = frame.locals := by simp [slots]
  have found : Extracted.program[portableIndex]? = some portableBody := by rfl
  have fetched : portableBody.code[18]? = some (.call maskIndex 2) := by rfl
  have returned : portableBody.code[19]? = some .ret := by rfl
  have returns : portableBody.returnsValue = true := by rfl
  have stepped : step portableBody (.call maskIndex 2) 18 (readOnlyArguments [left, right]) frame
      [.scalar (.i32 ltWord), .scalar (.i32 eqWord)] m2 =
      .ok (.call maskIndex [.scalar (.i32 eqWord), .scalar (.i32 ltWord)] [] m2) := by
    simp [step, checkedValue, numericValue, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have tail : run Extracted.program 1 portableIndex 19 (readOnlyArguments [left, right]) frame
      [.scalar (.i32 (maskResult eqWord ltWord))] m2 =
      .ok (leaveFrame frame m2, [.scalar (.i32 (maskResult eqWord ltWord))]) := by
    simp [run, found, returned, returns, step, checkedValue, numericValue,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, tail⟩ := run_call_exists found fetched stepped ⟨8, mask_invoke m2 eqWord ltWord⟩ ⟨1, tail⟩
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  have hl := call.input_load (reference := left) (by simp)
  have hr := call.input_load (reference := right) (by simp)
  simp only [eqWord, ltWord, portableEqual, portableLess, x, y] at s1 s2 r1 r2 tail
  refine ⟨tailFuel + 18, m2, ?_, preserved⟩
  conv in portableIndex => cbv
  iterate 18
    apply Eq.trans
    · apply run_next
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [step, readOnlyArguments, checkedValue, numericValue, formValue, fl, fr, hl, hr,
            slot0, slot1, slot2, duplicate, s0, s1, s2, r0, r0after, r1, r2, keep0, keep1, keep2, x, y,
            pureArity, scalars, staticInstruction, memoryInstruction,
            CIL.step, CIL.Intrinsic.available, intrinsic_portable_eq, intrinsic_portable_lt,
            intrinsic_portable_mask, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try (exact ⟨rfl, rfl, rfl, rfl⟩)
        done
  exact tail

#print axioms portable_run
end UInt256Proof.Compare.Safety

namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety

theorem portable_result_math (memory : Memory) (left right : Reference) :
    maskResult (portableEqual (inputValue memory left) (inputValue memory right))
      (portableLess (inputValue memory left) (inputValue memory right)) =
      if (inputValue memory left).toNat < (inputValue memory right).toNat then 1 else 0 := by
  have leftValue : UInt256Model.value (inputLimb memory left) = inputValue memory left :=
    UInt256Proof.input_value (fun offset => (memory.cells left.allocation offset).bits) left.offset
  have rightValue : UInt256Model.value (inputLimb memory right) = inputValue memory right :=
    UInt256Proof.input_value (fun offset => (memory.cells right.allocation offset).bits) right.offset
  rw [← leftValue, ← rightValue]
  simp only [portableEqual, portableLess, portableEqualityMask, portableLessMask, mask_result_math]

theorem portable_checked : BinaryReadOnlyInvocation
    (fun left right => .i32 (if left.toNat < right.toNat then 1 else 0))
    Extracted.program portableIndex := by
  intro memory left right call
  obtain ⟨frame, entered, setup, homes, enteredCall, before⟩ := portable_setup memory left right call
  obtain ⟨fuel, final, finished, preserved⟩ := portable_run entered left right frame memory.nextIdentity homes enteredCall
  rw [portable_result_math, call.input_value_after_setup setup (by simp : left ∈ [left, right]),
    call.input_value_after_setup setup (by simp : right ∈ [left, right])] at finished
  have found : Extracted.program[portableIndex]? = some portableBody := by rfl
  have checked : (readOnlyArguments [left, right]).mapM (checkedValue memory) =
      .ok (readOnlyArguments [left, right]) := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    simp [readOnlyArguments, checkedValue, formValue, fl, fr, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  refine ⟨fuel, _, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live finished, ?_⟩
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have after := leaveFrame_preserves_memory_below frame final memory.nextIdentity
    (fun id member => (fresh.2 id member).1)
  intro id bound offset
  exact (after.cells id bound offset).trans
    ((preserved.cells id bound offset).trans (before.cells id bound offset))

#print axioms portable_result_math
#print axioms portable_checked
end UInt256Proof.Compare.Safety
