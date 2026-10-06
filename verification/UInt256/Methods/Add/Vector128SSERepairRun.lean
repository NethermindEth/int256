import UInt256.Methods.Add.Vector128SSECarryState
import UInt256.Methods.Add.StorageCall
import UInt256.Methods.Add.CarryArithmetic
import CIL.Safety.ReturnMemory
import UInt256.Methods.Add.Vector128RepairDispatch

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety UInt256Proof.AddSubtract.Safety

/-- The five actual word homes are fresh and retain write authority through
    the checked vector prefix. Their contents need not all be initialized yet. -/
theorem vector128_sse_word_home (original entered current : Memory)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots)
    (homes : NumericHomes entered original.nextIdentity vector128Specs slots)
    (enteredWF : entered.WellFormed)
    (authority : AccessBelow entered.nextIdentity entered current) (index : Fin 5) :
    ∃ reference,
      slots[14 + index.val]? = some (.bytes .word64 reference) ∧
      frame.locals[15 + index.val]? = some (.bytes .word64 reference) ∧
      original.nextIdentity ≤ reference.allocation ∧
      access current reference 8 1 true = .ok () := by
  have spec : vector128Specs[14 + index.val]? = some ⟨.word64, .i64 0, 0, rfl⟩ := by
    obtain ⟨index, bound⟩ := index
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨reference, slot, fresh, _, writable⟩ := homes.home_at _ _ spec
  have actual : frame.locals[15 + index.val]? = some (.bytes .word64 reference) := by
    simpa [layout, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using slot
  obtain ⟨allocation, ready⟩ := access_requirements writable
  exact ⟨reference, slot, actual, fresh, authority.access writable (enteredWF.1 _ _ ready.present).1⟩

/-- Build the full zero-carry invariant from actual homes and preserved caller
    memory. All separation obligations concern fresh private allocations. -/
theorem vector128_sse_carry_ready (original entered current : Memory)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (left right output carryHome : Reference)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (currentCall : CallingConditions Extracted.program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (homes : NumericHomes entered original.nextIdentity vector128Specs slots)
    (enteredWF : entered.WellFormed)
    (authority : AccessBelow entered.nextIdentity entered current)
    (carrySlot : frame.locals[15]? = some (.bytes .word64 carryHome))
    (carryRead : read current carryHome 8 1 = .ok (numberBytes 0 8)) :
    ∃ results : Fin 4 → Reference,
      ScalarCarryState original current frame left right output carryHome results 0 15 16 := by
  classical
  have allHomes := vector128_sse_word_home original entered current frame root slots layout homes enteredWF authority
  obtain ⟨carry, carryLocal, actualCarry, carryFresh, carryWrite⟩ := allHomes 0
  have same : carry = carryHome := by simpa only [show 15 + (0 : Fin 5).val = 15 from rfl, carrySlot,
    Option.some.injEq, LocalSlot.bytes.injEq, true_and] using actualCarry.symm
  subst carry
  let results : Fin 4 → Reference := fun i => Classical.choose (allHomes ⟨i.val + 1, by omega⟩)
  have resultFacts (i : Fin 4) := Classical.choose_spec (allHomes ⟨i.val + 1, by omega⟩)
  have resultSlots (i : Fin 4) : slots[15 + i.val]? = some (.bytes .word64 (results i)) := by
    have found := (resultFacts i).1
    change slots[14 + (i.val + 1)]? = some (.bytes .word64 (results i)) at found
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd] using found
  have ordered (i : Fin 4) : carryHome.allocation < (results i).allocation :=
    homes.ordered 14 (15 + i.val) .word64 .word64 carryHome (results i) (by omega) carryLocal (resultSlots i)
  refine ⟨results, currentCall, ?_, carrySlot, ?_, carryWrite, ?_, carryRead, by simp [scalarCarryValue],
    ?_, (fun i => Ne.symm (Nat.ne_of_lt (ordered i))), ?_, carryFresh, ?_, preserved.cells, ?_⟩
  · intro reference member
    exact call.input_bytes_of_memory_below preserved member
  · intro i
    have found := (resultFacts i).2.1
    change frame.locals[15 + (i.val + 1)]? = some (.bytes .word64 (results i)) at found
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd] using found
  · intro i
    exact (resultFacts i).2.2.2
  · intro reference member
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed member)
    have old : reference.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
    exact ⟨Nat.ne_of_lt (Nat.lt_of_lt_of_le old carryFresh),
      fun i => Nat.ne_of_lt (Nat.lt_of_lt_of_le old (resultFacts i).2.2.1)⟩
  · intro i j different
    have distinct : i.val ≠ j.val := fun equal => different (Fin.ext equal)
    by_cases before : i.val < j.val
    · exact Nat.ne_of_lt (homes.ordered _ _ .word64 .word64 _ _ (by omega) (resultSlots i) (resultSlots j))
    · exact Ne.symm (Nat.ne_of_lt (homes.ordered _ _ .word64 .word64 _ _ (by omega) (resultSlots j) (resultSlots i)))
  · intro i
    exact (resultFacts i).2.2.1
  · intro i impossible
    omega

/-- Start with the actual repair branch, initialize carry, and execute all four
    helper calls. The continuation receives complete initial-input result words. -/
theorem vector128_sse_repair_carry (original entered current : Memory)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (left right output : Reference)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (currentCall : CallingConditions Extracted.program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (homes : NumericHomes entered original.nextIdentity vector128Specs slots)
    (enteredWF : entered.WellFormed)
    (authority : AccessBelow entered.nextIdentity entered current)
    (extra : List Value) (post : Memory → List Value → Prop)
    (continuation : ∀ carryHome results after,
      ScalarCarryState original after frame left right output carryHome results 4 15 16 →
      ∃ fuel final returned,
        run Extracted.program fuel vector128Index 193 (binaryArguments left right output ++ extra)
          frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 162 (binaryArguments left right output ++ extra)
        frame [] current = .ok (final, returned) ∧ post final returned := by
  apply vector128_sse_repair_start (by rfl) original.nextIdentity entered current [left, right] [output]
    frame root slots layout (binaryArguments left right output ++ extra) currentCall enteredWF homes authority post
  intro carryHome after carrySlot carryRead retained afterCall afterAuthority _written
  obtain ⟨results, ready⟩ := vector128_sse_carry_ready original entered after frame root slots layout
    left right output carryHome call afterCall (preserved.trans retained) homes enteredWF afterAuthority carrySlot carryRead
  exact vector128_sse_carry_all ready extra post (continuation carryHome results)

#print axioms vector128_sse_repair_carry
#print axioms vector128_sse_word_home
#print axioms vector128_sse_carry_ready
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety UInt256Proof.AddSubtract.Safety

theorem vector128_sse_store_prefix (left right output : Reference) (extra : List Value)
    (frame : Frame) (memory : Memory) (results : Fin 4 → Reference) (words : Fin 4 → BitVec 64)
    (outputFormed : form memory output = .ok output)
    (slots : ∀ i, frame.locals[i.val + 16]? = some (.bytes .word64 (results i)))
    (reads : ∀ i, read memory (results i) 8 1 = .ok (numberBytes (words i).toNat 8))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel vector128Index 198
        ([.reference (.address left), .reference (.address right), .reference (.address output)] ++ extra)
        frame [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
          .scalar (.i64 (words 0)), .reference (.address output)] memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 193
        ([.reference (.address left), .reference (.address right), .reference (.address output)] ++ extra)
        frame [] memory = .ok (result, returned) ∧ post result returned := by
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
    | apply run_next_exists post (by rfl : Extracted.program[vector128Index]? = some vector128Body) (by rfl)
      simp (config := { implicitDefEqProofs := false })
          [cil_code, step, checkedValue, formValue, outputFormed, s0, s1, s2, s3, r0, r1, r2, r3,
            checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩

theorem vector128_sse_return (args : List Value) (frame : Frame) (memory : Memory)
    (carryHome : Reference) (carry : BitVec 64)
    (slot : frame.locals[15]? = some (.bytes .word64 carryHome))
    (loaded : read memory carryHome 8 1 = .ok (numberBytes carry.toNat 8)) :
    run Extracted.program 5 vector128Index 199 args frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if BitVec.ofNat 64 0 < carry then 1 else 0))]) := by
  have reading := load_local_word64_of_read loaded
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  repeat'
    first
    | apply Eq.trans
      · apply run_next found (by rfl)
        simp (config := { implicitDefEqProofs := false })
          [step, slot, reading, checkedValue, numericValue, pureArity, scalars,
            CIL.step, CIL.binary, instruction, Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    | solve
      | rw [run]
        simp (config := { implicitDefEqProofs := false })
          [found, show vector128Body.code[203]? = some .ret from rfl,
            show vector128Body.returnsValue = true from rfl, step, checkedValue, numericValue,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms vector128_sse_store_prefix
#print axioms vector128_sse_return
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety UInt256Proof.AddSubtract.Safety

theorem vector128_sse_finish (original current : CIL.Safety.Memory) (frame : Frame)
    (left right output carryHome : Reference) (results : Fin 4 → Reference) (extra : List Value)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : ScalarCarryState original current frame left right output carryHome results 4 15 16) :
    ∃ fuel final values,
      run Extracted.program fuel vector128Index 193
        (binaryArguments left right output ++ extra) frame [] current = .ok (final, values) ∧
      AddResult original final values left right output := by
  let words := scalarSumWord original left right
  let post := fun final values => AddResult original final values left right output
  have formed := state.call.output_formed (by simp : output ∈ [output])
  apply vector128_sse_store_prefix left right output extra frame current results words
    formed state.resultSlots (fun i => state.completed i i.isLt) post
  apply run_store_limbs [left, right] output (words 0) (words 1) (words 2) (words 3) post
    (body := vector128Body) (op := .call Extracted.storeLimbsIndex 5)
  · rfl
  · rfl
  · unfold storageArguments
    repeat' (conv in storageWordOrder => cbv)
    simp [List.range_succ, List.findIdx, List.findIdx.go, step, checkedValue, numericValue, formValue, formed,
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
    have retained := leaveFrame_preserves_memory_below frame stored original.nextIdentity
      owned
    refine ⟨5, leaveFrame frame stored,
      [.scalar (.i32 (scalarOverflowFlag (scalarCarryValue original left right 4)))],
      vector128_sse_return _ _ _ _ _ state.carrySlot carryRead, ?_⟩
    have bytes : (fun offset => ((leaveFrame frame stored).cells output.allocation offset).bits) =
        (fun offset => (stored.cells output.allocation offset).bits) := by
      funext offset
      rw [retained.cells output.allocation outputOld offset]
    refine ⟨leaveFrame_preserves_wellFormed _ _ valid.1.1, ?_, ?_, ?_, ?_⟩
    · have computed : inputValue (leaveFrame frame stored) output = scalarSumValue original left right := by
        simpa only [inputValue, bytes, scalarSumValue] using value
      exact computed.trans (scalar_sum_value original left right)
    · rw [scalar_flag_overflow]
    · exact (retained.access output outputOld 32 1 true).trans
        (valid.1.2.2 (wordView output) (by simp))
    · intro id old offset untouched
      exact (retained.cells id old offset).trans ((outside id offset untouched).trans (state.callerCells id old offset))

#print axioms vector128_sse_finish
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety UInt256Proof.AddSubtract.Safety

/-- The complete SSE repair route from helper entry, including initial-input
    arithmetic, exact overflow and preservation outside an arbitrarily aliased output. -/
theorem vector128_sse_repair_entry (original entered : CIL.Safety.Memory)
    (left right output : Reference) (frame : Frame) (slots : List LocalSlot)
    (flag : BitVec 32)
    (call : CallingConditions Extracted.program original [left, right] [output])
    (setup : enterFrame vector128Body
      (binaryArguments left right output ++ [.scalar (.i32 flag)]) original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity vector128Specs slots)
    (repair : selectedPropagation128 flag (vector128BranchValue original left right 11)
      (vector128BranchValue original left right 12) ≠ BitVec.ofNat 128 0) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 0
        (binaryArguments left right output ++ [.scalar (.i32 flag)]) frame [] entered =
          .ok (final, returned) ∧ AddResult original final returned left right output := by
  let args := binaryArguments left right output ++ [.scalar (.i32 flag)]
  let post := fun final returned => AddResult original final returned left right output
  apply vector128_dispatch_checked original entered [left, right] [output] left right output
    frame slots args call setup layout homes (by simp) (by simp) (by simp)
    (by rfl) (by rfl) (by rfl) flag (by rfl) post
  intro current conditionHome conditionSlot conditionRead snapshots earlyRead currentCall authority footprint advanced preserved
  simp only [repair, ite_false]
  apply vector128_repair_dispatch current (vector128SavedFrame frame slots right) args post
  change ∃ fuel final returned,
    run Extracted.program fuel vector128Index 162 args (vector128SavedFrame frame slots right) [] current =
      .ok (final, returned) ∧ post final returned
  apply vector128_sse_repair_carry original entered current (vector128SavedFrame frame slots right)
    (.root (some (.address right))) slots rfl left right output call currentCall (preserved (by rfl))
    homes (enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup) authority [.scalar (.i32 flag)] post
  intro carryHome results after state
  exact vector128_sse_finish original after (vector128SavedFrame frame slots right)
    left right output carryHome results [.scalar (.i32 flag)] call
    (fun id member => ((enterFrame_fresh _ _ _ _ _ setup).2 id member).1) state

#print axioms vector128_sse_repair_entry
end UInt256Proof.Add.Safety
