import UInt256.Methods.Add.ScalarCarryPrefix
import UInt256.Methods.Add.StorageCall
import UInt256.Methods.Add.CarryArithmetic
import UInt256.Methods.Add.ScalarCarryMemory
import UInt256.Methods.Add.ScalarSmallFacts

namespace UInt256Proof.Safety

open CIL.Safety

def scalarStoreCall : Nat :=
  Extracted.addScalarBody.code.findIdx fun op => match op with
    | .call callee _ => callee == Extracted.storeLimbsIndex
    | _ => false

theorem scalar_store_prefix (left right output : Reference) (extra : List Value)
    (frame : Frame) (memory : Memory) (results : Fin 4 → Reference) (words : Fin 4 → BitVec 64)
    (outputFormed : form memory output = .ok output)
    (slots : ∀ i, frame.locals[i.val + 3]? = some (.bytes .word64 (results i)))
    (reads : ∀ i, read memory (results i) 8 1 = .ok (numberBytes (words i).toNat 8))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex scalarStoreCall
        ([.reference (.address left), .reference (.address right), .reference (.address output)] ++ extra)
        frame (storageArguments output (words 0) (words 1) (words 2) (words 3)).reverse memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall 3 + 1)
        ([.reference (.address left), .reference (.address right), .reference (.address output)] ++ extra)
        frame [] memory = .ok (result, returned) ∧ post result returned := by
  unfold storageArguments at continuation
  conv at continuation in storageWordOrder => cbv
  simp [List.range_succ, List.findIdx] at continuation
  conv in (scalarCarryCall _) => cbv
  simp only [Nat.reduceAdd]
  have s0 := slots 0
  have s1 := slots 1
  have s2 := slots 2
  have s3 := slots 3
  dsimp at s0 s1 s2 s3
  simp only [CIL.fin_val_three, Nat.reduceAdd] at s3
  have r0 := load_local_word64_of_read (reads 0)
  have r1 := load_local_word64_of_read (reads 1)
  have r2 := load_local_word64_of_read (reads 2)
  have r3 := load_local_word64_of_read (reads 3)
  repeat'
    first
    | exact continuation
    | apply run_next_exists post
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [cil_code, step, checkedValue, formValue, outputFormed, s0, s1, s2, s3, r0, r1, r2, r3,
            checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩

theorem scalar_return (args : List Value) (frame : Frame) (memory : Memory)
    (carryHome : Reference) (carry : BitVec 64)
    (slot : frame.locals[2]? = some (.bytes .word64 carryHome))
    (loaded : read memory carryHome 8 1 = .ok (numberBytes carry.toNat 8)) :
    run Extracted.program (Extracted.addScalarBody.code.length + 1) Extracted.addScalarIndex
      (scalarStoreCall + 1) args frame [] memory =
        .ok (leaveFrame frame memory, [.scalar (.i32 (scalarOverflowFlag carry))]) := by
  conv in scalarStoreCall => cbv
  have reading := load_local_word64_of_read loaded
  simp only [cil_code]
  simp only [Nat.reduceAdd]
  repeat'
    first
    | apply Eq.trans
      · apply run_next
        · simp only [cil_code]; rfl
        · simp only [cil_code]; rfl
        · simp (config := { implicitDefEqProofs := false })
            [cil_code, step, slot, reading, checkedValue, numericValue,
              pureArity, scalars, CIL.step, CIL.binary, instruction,
              Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    | solve
      | rw [run]
        simp (config := { implicitDefEqProofs := false })
          [cil_code, step, checkedValue, numericValue, scalarOverflowFlag,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms scalar_store_prefix
#print axioms scalar_return

end UInt256Proof.Safety

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

structure ScalarResult (original final : CIL.Safety.Memory) (values : List Value)
    (left right output : Reference) : Prop where
  wellFormed : final.WellFormed
  value : inputValue final output = scalarSumValue original left right
  flag : values = [.scalar (.i32 (scalarOverflowFlag (scalarCarryValue original left right 4)))]
  writable : access final output 32 1 true = .ok ()
  footprint : ∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset →
    final.cells id offset = original.cells id offset

/-- Finish the extracted general scalar path, preserving the private carry
    across output writes and the original caller footprint across teardown. -/
theorem scalar_finish (original entered current : CIL.Safety.Memory) (frame : Frame)
    (left right output carryHome : Reference) (results : Fin 4 → Reference)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame Extracted.addScalarBody (scalarArguments left right output) original = .ok (frame, entered))
    (state : ScalarCarryState original current frame left right output carryHome results 4) :
    ∃ fuel final values,
      run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall 3 + 1)
        (scalarArguments left right output) frame [] current = .ok (final, values) ∧
      ScalarResult original final values left right output := by
  let words := scalarSumWord original left right
  let post := fun final values => ScalarResult original final values left right output
  have formed := state.call.output_formed (by simp : output ∈ [output])
  apply scalar_store_prefix left right output [.scalar (.i32 0)] frame current results words
    formed state.resultSlots (fun i => state.completed i i.isLt) post
  apply run_store_limbs [left, right] output (words 0) (words 1) (words 2) (words 3) post
    (body := Extracted.addScalarBody) (op := .call Extracted.storeLimbsIndex 5)
  · simp only [cil_code]
  · conv in scalarStoreCall => cbv
    simp only [cil_code]
  · unfold storageArguments
    repeat' (conv in storageWordOrder => cbv)
    simp [List.range_succ, List.findIdx, step, checkedValue, numericValue, formValue, formed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl⟩
  · exact state.call
  · intro stored valid outside authority value
    obtain ⟨outputAllocation, outputPresent, _, _⟩ := formed_reference_live _ _ _
      (call.output_formed (by simp : output ∈ [output]))
    have outputOld := (call.1.1.1 _ _ outputPresent).1
    obtain ⟨carryAllocation, carryPresent, _, _⟩ := access_within_allocation _ _ _ _ _ state.carryWrite
    have carryOld := (state.call.1.1.1 _ _ carryPresent).1
    have distinct : carryHome.allocation ≠ output.allocation :=
      Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le outputOld state.carryFresh))
    have carryRead := authority.read_eq state.carryRead carryOld
      (fun i _ => outside _ _ (Or.inl distinct))
    have fresh := enterFrame_fresh _ _ _ _ _ setup
    have retained := leaveFrame_preserves_memory_below frame stored original.nextIdentity
      (fun id member => (fresh.2 id member).1)
    refine ⟨Extracted.addScalarBody.code.length + 1, leaveFrame frame stored,
      [.scalar (.i32 (scalarOverflowFlag (scalarCarryValue original left right 4)))],
      scalar_return _ _ _ _ _ state.carrySlot carryRead, ?_⟩
    have bytes : (fun offset => ((leaveFrame frame stored).cells output.allocation offset).bits) =
        (fun offset => (stored.cells output.allocation offset).bits) := by
      funext offset
      rw [retained.cells output.allocation outputOld offset]
    refine ⟨leaveFrame_preserves_wellFormed _ _ valid.1.1, ?_, rfl, ?_, ?_⟩
    · simpa only [inputValue, bytes, scalarSumValue] using value
    · exact (retained.access output outputOld 32 1 true).trans
        (valid.1.2.2 (wordView output) (by simp))
    · intro id old offset untouched
      exact (retained.cells id old offset).trans ((outside id offset untouched).trans (state.callerCells id old offset))

#print axioms scalar_finish

theorem ScalarResult.modular_sum {original final : CIL.Safety.Memory} {values : List Value}
    {left right output : Reference} (result : ScalarResult original final values left right output) :
    inputValue final output = inputValue original left + inputValue original right :=
  result.value.trans (scalar_sum_value original left right)

/-- Complete finite checked execution on the both-large branch, including
    initial-input modular arithmetic, exact carry flag and caller footprint. -/
theorem scalar_general_checked (memory : CIL.Safety.Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (largeRight : inputLimb memory right 1 ||| inputLimb memory right 2 |||
      inputLimb memory right 3 ≠ BitVec.ofNat 64 0)
    (largeLeft : inputLimb memory left 1 ||| inputLimb memory left 2 |||
      inputLimb memory left 3 ≠ BitVec.ofNat 64 0) :
    ∃ fuel final values,
      invoke Extracted.program fuel Extracted.addScalarIndex (scalarArguments left right output) memory =
        .ok (final, values) ∧ ScalarResult memory final values left right output := by
  apply scalar_general_carries memory left right output call largeRight largeLeft
    (fun final values => ScalarResult memory final values left right output)
  intro frame entered carryHome results after setup state
  exact scalar_finish memory entered after frame left right output carryHome results call setup state

#print axioms ScalarResult.modular_sum
#print axioms scalar_general_checked

end UInt256Proof.Safety

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

theorem scalar_right_small_checked (memory : CIL.Safety.Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (small : inputLimb memory right 1 ||| inputLimb memory right 2 ||| inputLimb memory right 3 = 0) :
    ∃ fuel final values,
      invoke Extracted.program fuel Extracted.addScalarIndex (scalarArguments left right output) memory =
        .ok (final, values) ∧ AddResult memory final values left right output := by
  let post := fun final values => AddResult memory final values left right output
  obtain ⟨frame, entered, setup, homes, _, enteredWF⟩ :=
    scalar_frame_setup memory (scalarArguments left right output) call.1.1
  have executed := scalar_right_prefix_checked memory entered left right output [.scalar (.i32 0)]
    frame call setup homes post (by
      intro home current slot loaded preserved currentCall authority
      rw [small]
      apply scalar_small_prefix false left right output home (inputLimb memory right 0) frame current
        (currentCall.input_formed (by simp [scalarSmallSource])) (currentCall.output_formed (by simp)) slot loaded post
      have next := scalar_private_next memory entered current frame homes enteredWF currentCall.1.1 authority
      have math := scalar_small_values false memory current left right output call preserved small
      exact scalar_small_finish false memory entered current frame left right output (inputLimb memory right 0)
        call setup currentCall preserved next math.1 math.2)
  obtain ⟨fuel, final, values, finished, result⟩ := executed
  have checked : (scalarArguments left right output).mapM (checkedValue memory) =
      .ok (scalarArguments left right output) := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [scalarArguments, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨fuel, final, values, ?_, result⟩
  change run Extracted.program fuel Extracted.addScalarIndex 0
    (scalarArguments left right output) frame [] entered = .ok (final, values) at finished
  simp only [cil_code] at setup
  simpa only [invoke, cil_code, checked, setup, Except.mapError, Bind.bind, Except.bind] using finished

theorem scalar_left_small_checked (memory : CIL.Safety.Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (largeRight : inputLimb memory right 1 ||| inputLimb memory right 2 |||
      inputLimb memory right 3 ≠ BitVec.ofNat 64 0)
    (small : inputLimb memory left 1 ||| inputLimb memory left 2 ||| inputLimb memory left 3 = 0) :
    ∃ fuel final values,
      invoke Extracted.program fuel Extracted.addScalarIndex (scalarArguments left right output) memory =
        .ok (final, values) ∧ AddResult memory final values left right output := by
  let post := fun final values => AddResult memory final values left right output
  apply scalar_large_right_prefix memory left right output call largeRight post
  intro frame entered rightHome leftHome current setup homes ready
  rw [small]
  apply scalar_small_prefix true left right output leftHome (inputLimb memory left 0) frame current
    (ready.call.input_formed (by simp [scalarSmallSource])) (ready.call.output_formed (by simp)) ready.leftSlot ready.leftRead post
  have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  have next := scalar_private_next memory entered current frame homes enteredWF ready.call.1.1 ready.authority
  have math := scalar_small_values true memory current left right output call ready.preserved small
  exact scalar_small_finish true memory entered current frame left right output (inputLimb memory left 0)
    call setup ready.call ready.preserved next math.1 math.2

#print axioms scalar_right_small_checked
#print axioms scalar_left_small_checked

end UInt256Proof.Safety

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

theorem ScalarResult.as_add {original final : CIL.Safety.Memory} {values : List Value}
    {left right output : Reference} (result : ScalarResult original final values left right output) :
    AddResult original final values left right output :=
  ⟨result.wellFormed, result.modular_sum, by simpa only [scalar_flag_overflow] using result.flag,
    result.writable, result.footprint⟩

/-- All scalar helper branches: actual finite execution, initial-operand sum,
    mathematical overflow and caller storage preservation under valid overlap. -/
theorem scalar_checked (memory : CIL.Safety.Memory) (left right output : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output]) :
    ∃ fuel final values,
      invoke Extracted.program fuel Extracted.addScalarIndex (scalarArguments left right output) memory =
        .ok (final, values) ∧ AddResult memory final values left right output := by
  by_cases rightSmall : inputLimb memory right 1 ||| inputLimb memory right 2 |||
      inputLimb memory right 3 = BitVec.ofNat 64 0
  · exact scalar_right_small_checked memory left right output call rightSmall
  · by_cases leftSmall : inputLimb memory left 1 ||| inputLimb memory left 2 |||
        inputLimb memory left 3 = BitVec.ofNat 64 0
    · exact scalar_left_small_checked memory left right output call rightSmall leftSmall
    · obtain ⟨fuel, final, values, invoked, result⟩ :=
        scalar_general_checked memory left right output call rightSmall leftSmall
      exact ⟨fuel, final, values, invoked, result.as_add⟩

#print axioms ScalarResult.as_add
#print axioms scalar_checked

end UInt256Proof.Safety
