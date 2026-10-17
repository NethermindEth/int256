import UInt256.Methods.Subtract.Vector128Repair
import UInt256.Methods.Subtract.SegmentFetch

namespace UInt256Proof.Subtract.Profile

/-- Zero the borrow word at local `bl`, then four borrow calls writing locals `bl + 1` to `bl + 4`. -/
def subtractRepairBorrowCode (bl borrow : Nat) : List CIL.Op := [
  .const32 0, .convI8, .setLocal bl,
  .arg 0, .fieldAt 0 8, .arg 1, .fieldAt 0 8, .localAddr bl, .localAddr (bl + 1), .call borrow 4,
  .arg 0, .fieldAt 8 8, .arg 1, .fieldAt 8 8, .localAddr bl, .localAddr (bl + 2), .call borrow 4,
  .arg 0, .fieldAt 16 8, .arg 1, .fieldAt 16 8, .localAddr bl, .localAddr (bl + 3), .call borrow 4,
  .arg 0, .fieldAt 24 8, .arg 1, .fieldAt 24 8, .localAddr bl, .localAddr (bl + 4), .call borrow 4]

/-- Store the four words in ascending order and return the final borrow. -/
def subtractStoreCode (bl storage : Nat) : List CIL.Op := [
  .arg 2, .local (bl + 1), .local (bl + 2), .local (bl + 3), .local (bl + 4), .call storage 5,
  .local bl, .const32 0, .convI8, .gtu, .ret (some .unsigned8)]

theorem subtract_repair_code_split (borrow storage : Nat) :
    subtractRepairCode borrow storage = subtractRepairBorrowCode 11 borrow ++ subtractStoreCode 11 storage := rfl
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Initialize the private borrow word at any offset. -/
theorem subtract_repair_start_at (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (base ws : Nat) (leading tail : List CIL.Op) (leadingLength : leading.length = base)
    (borrow : Nat) (code : body.code = leading ++ subtractRepairBorrowCode (ws + 1) borrow ++ tail)
    (borrowSpec : specs[ws]? = some subtractWordSpec)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[ws + 1]? = some (.bytes .word64 reference) →
      read after reference 8 1 = .ok (numberBytes 0 8) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes 0 8) 1 = .ok after →
      ∃ fuel final returned,
        run program fuel method (base + 3) args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method base args frame [] current = .ok (final, returned) ∧ post final returned := by
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store program body specs boundary entered current inputs outputs frame root slots layout currentCall
      enteredWF homes authority ws subtractWordSpec borrowSpec (.i64 0) 0 rfl
  have done := continuation reference after slot loaded retained afterCall afterAuthority written
  repeat' first
    | exact done
    | (apply run_next_exists post found (by seg_fetch code leadingLength)
       first
       | exact stored _ _ _
       | (simp (config := { implicitDefEqProofs := false })
           [step, pureArity, scalars, CIL.step.eq_def, CIL.unary, checkedValue, numericValue,
             Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

/-- Load both operand limbs and the two private word addresses for one borrow call. -/
theorem subtract_repair_segment_at (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (base bl : Nat) (leading tail : List CIL.Op) (leadingLength : leading.length = base)
    (borrow : Nat) (code : body.code = leading ++ subtractRepairBorrowCode bl borrow ++ tail)
    (segment : Fin 4) (left right : Reference) (args : List Value)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (frame : Frame) (memory : Memory) (a b : BitVec 64) (borrowHome resultHome : Reference)
    (leftFormed : form memory left = .ok left) (rightFormed : form memory right = .ok right)
    (leftRead : ∀ rest, instruction (.fieldAt (8 * segment.val) 8)
      (.reference (.address left) :: rest) memory = .ok (memory, .scalar (.i64 a) :: rest))
    (rightRead : ∀ rest, instruction (.fieldAt (8 * segment.val) 8)
      (.reference (.address right) :: rest) memory = .ok (memory, .scalar (.i64 b) :: rest))
    (borrowSlot : frame.locals[bl]? = some (.bytes .word64 borrowHome))
    (resultSlot : frame.locals[bl + 1 + segment.val]? = some (.bytes .word64 resultHome))
    (borrowFormed : form memory borrowHome = .ok borrowHome)
    (resultFormed : form memory resultHome = .ok resultHome)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method (base + 9 + 7 * segment.val) args frame
        [.reference (.address resultHome), .reference (.address borrowHome), .scalar (.i64 b), .scalar (.i64 a)]
        memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (base + 3 + 7 * segment.val) args frame [] memory =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨segment, bound⟩ := segment
  have cases : segment = 0 ∨ segment = 1 ∨ segment = 2 ∨ segment = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  all_goals
    simp only [Nat.reduceMul, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] at leftRead rightRead resultSlot continuation ⊢
    repeat' first
      | exact continuation
      | (apply run_next_exists post found (by seg_fetch code leadingLength)
         simp (config := { implicitDefEqProofs := false })
           [step, checkedValue, numericValue, formValue, leftArg, rightArg, leftFormed, rightFormed,
             borrowFormed, resultFormed, borrowSlot, resultSlot, localAddress, leftRead, rightRead,
             pureArity, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
         first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

/-- One fetched borrow call composes with the checked borrow-helper contract. -/
theorem subtract_repair_indexed_borrow_at (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (base bl : Nat) (leading tail : List CIL.Op) (leadingLength : leading.length = base)
    (borrow : Nat) (code : body.code = leading ++ subtractRepairBorrowCode bl borrow ++ tail)
    (borrowFound : program[borrow]? = some (borrowBody body.profile))
    (index : Fin 4) (args : List Value) (frame : Frame) (memory : Memory)
    (a b c : BitVec 64) (borrowHome resultHome : Reference)
    (wellFormed : memory.WellFormed) (incoming : c.toNat ≤ 1)
    (borrowRead : read memory borrowHome 8 1 = .ok (numberBytes c.toNat 8))
    (borrowWrite : access memory borrowHome 8 1 true = .ok ())
    (resultWrite : access memory resultHome 8 1 true = .ok ())
    (disjoint : WordsDisjoint borrowHome resultHome)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, BorrowPost (program := program) a b c borrowHome resultHome memory after →
      ∃ fuel result returned,
        run program fuel method (base + 10 + 7 * index.val) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (base + 9 + 7 * index.val) args frame
        [.reference (.address resultHome), .reference (.address borrowHome), .scalar (.i64 b), .scalar (.i64 a)]
        memory = .ok (result, returned) ∧ post result returned := by
  have borrowFormed := access_reference_valid _ _ _ _ _ borrowWrite
  have resultFormed := access_reference_valid _ _ _ _ _ resultWrite
  obtain ⟨childFuel, stored, invoked, guarantees⟩ := borrow_checked_contract borrowFound a b c borrowHome resultHome
    memory wellFormed incoming borrowRead borrowWrite resultWrite disjoint
  obtain ⟨parentFuel, result, values, resumed, satisfied⟩ := continuation stored guarantees
  have fetched : body.code[base + 9 + 7 * index.val]? = some (.call borrow 4) := by
    obtain ⟨index, bound⟩ := index
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    all_goals
      simp only [Nat.reduceMul, Nat.add_zero]
      seg_fetch code leadingLength
  have stepped : step body (.call borrow 4) (base + 9 + 7 * index.val) args frame
      [.reference (.address resultHome), .reference (.address borrowHome), .scalar (.i64 b), .scalar (.i64 a)] memory =
      .ok (.call borrow [.scalar (.i64 a), .scalar (.i64 b), .reference (.address borrowHome),
        .reference (.address resultHome)] [] memory) := by
    simp [step, checkedValue, numericValue, formValue, borrowFormed, resultFormed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    try exact ⟨rfl, rfl⟩
  have resumed' : run program parentFuel method (base + 9 + 7 * index.val + 1) args frame [] stored =
      .ok (result, values) := by
    simpa only [show base + 9 + 7 * index.val + 1 = base + 10 + 7 * index.val by omega] using resumed
  obtain ⟨fuel, finished⟩ := run_call_exists found fetched stepped ⟨childFuel, invoked⟩ ⟨parentFuel, resumed'⟩
  exact ⟨fuel, result, values, finished, satisfied⟩

/-- Advance the borrow invariant through one actual repair call at any offset. -/
theorem subtract_repair_next_at (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (base bl : Nat) (leading tail : List CIL.Op) (leadingLength : leading.length = base)
    (borrow : Nat) (code : body.code = leading ++ subtractRepairBorrowCode bl borrow ++ tail)
    (borrowFound : program[borrow]? = some (borrowBody body.profile))
    {original before : Memory} {frame : Frame}
    {left right output borrowHome : Reference} {results : Fin 4 → Reference} (index : Fin 4)
    (state : ScalarBorrowState (program := program) original before frame left right output borrowHome results index.val bl (bl + 1))
    (args : List Value)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarBorrowState (program := program) original after frame left right output borrowHome results (index.val + 1) bl (bl + 1) →
      ∃ fuel result returned,
        run program fuel method (base + 10 + 7 * index.val) args frame [] after = .ok (result, returned) ∧
          post result returned) :
    ∃ fuel result returned,
      run program fuel method (base + 3 + 7 * index.val) args frame [] before =
        .ok (result, returned) ∧ post result returned := by
  have call := state.call
  have borrowWrite := state.borrowWrite
  have resultWrite := state.resultWrites index
  have resultSlot : frame.locals[bl + 1 + index.val]? = some (.bytes .word64 (results index)) := by
    simpa only [Nat.add_comm] using state.resultSlots index
  apply subtract_repair_segment_at program body method found base bl leading tail leadingLength borrow code
    index left right args leftArg rightArg frame before _ _ borrowHome (results index)
    (call.input_formed (by simp)) (call.input_formed (by simp))
    (fun rest => call.input_field_instruction (by simp) _ rest)
    (fun rest => call.input_field_instruction (by simp) _ rest) state.borrowSlot resultSlot
    (access_reference_valid _ _ _ _ _ borrowWrite) (access_reference_valid _ _ _ _ _ resultWrite) post
  apply subtract_repair_indexed_borrow_at program body method found base bl leading tail leadingLength borrow code
    borrowFound index args frame before _ _ (scalarBorrowValue original left right index.val) borrowHome (results index)
    call.1.1 state.borrowBound state.borrowRead borrowWrite resultWrite
    (Or.inl (Ne.symm (state.borrowSeparate index))) post
  intro after math
  apply continuation after
  apply state.advance index
  simpa only [inputLimb, state.inputBytes left (by simp), state.inputBytes right (by simp)] using math

/-- All four borrow calls keep the initial operands, private homes and completed limbs. -/
theorem subtract_repair_all_at (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (base bl : Nat) (leading tail : List CIL.Op) (leadingLength : leading.length = base)
    (borrow : Nat) (code : body.code = leading ++ subtractRepairBorrowCode bl borrow ++ tail)
    (borrowFound : program[borrow]? = some (borrowBody body.profile))
    {original before : Memory} {frame : Frame}
    {left right output borrowHome : Reference} {results : Fin 4 → Reference}
    (state : ScalarBorrowState (program := program) original before frame left right output borrowHome results 0 bl (bl + 1))
    (args : List Value)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarBorrowState (program := program) original after frame left right output borrowHome results 4 bl (bl + 1) →
      ∃ fuel result returned,
        run program fuel method (base + 31) args frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (base + 3) args frame [] before = .ok (result, returned) ∧ post result returned := by
  have s0 := subtract_repair_next_at program body method found base bl leading tail leadingLength
    borrow code borrowFound 0 state args leftArg rightArg post
  simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] at s0
  apply s0
  intro _ first
  have s1 := subtract_repair_next_at program body method found base bl leading tail leadingLength
    borrow code borrowFound 1 first args leftArg rightArg post
  simp only [Fin.val_one, Nat.mul_one, Nat.add_assoc, Nat.reduceAdd] at s1 ⊢
  apply s1
  intro _ second
  have s2 := subtract_repair_next_at program body method found base bl leading tail leadingLength
    borrow code borrowFound 2 second args leftArg rightArg post
  simp only [Fin.val_two, Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd] at s2 ⊢
  apply s2
  intro _ third
  have s3 := subtract_repair_next_at program body method found base bl leading tail leadingLength
    borrow code borrowFound 3 third args leftArg rightArg post
  simp only [CIL.fin_val_three, Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd] at s3 ⊢
  exact s3 continuation

#print axioms subtract_repair_start_at
#print axioms subtract_repair_segment_at
#print axioms subtract_repair_indexed_borrow_at
#print axioms subtract_repair_next_at
#print axioms subtract_repair_all_at
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- The five repair word homes at slot `ws` onwards are fresh and keep write authority. -/
theorem subtract_repair_word_home_at (specs : List NumericLocalSpec) (ws : Nat)
    (wordSpecs : ∀ i : Fin 5, specs[ws + i.val]? = some subtractWordSpec) (original entered current : Memory)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots)
    (homes : NumericHomes entered original.nextIdentity specs slots)
    (enteredWF : entered.WellFormed)
    (authority : AccessBelow entered.nextIdentity entered current) (index : Fin 5) :
    ∃ reference,
      slots[ws + index.val]? = some (.bytes .word64 reference) ∧
      frame.locals[ws + 1 + index.val]? = some (.bytes .word64 reference) ∧
      original.nextIdentity ≤ reference.allocation ∧
      access current reference 8 1 true = .ok () := by
  obtain ⟨reference, slot, fresh, _, writable⟩ := homes.home_at _ _ (wordSpecs index)
  change slots[ws + index.val]? = some (.bytes .word64 reference) at slot
  have actual : frame.locals[ws + 1 + index.val]? = some (.bytes .word64 reference) := by
    rw [layout, show ws + 1 + index.val = (ws + index.val) + 1 by omega]
    simpa using slot
  obtain ⟨allocation, ready⟩ := access_requirements writable
  exact ⟨reference, slot, actual, fresh, authority.access writable (enteredWF.1 _ _ ready.present).1⟩

/-- Build the zero-borrow invariant from fresh private homes and unchanged caller memory. -/
theorem subtract_repair_ready_at (program : CIL.Program) (specs : List NumericLocalSpec) (ws : Nat)
    (wordSpecs : ∀ i : Fin 5, specs[ws + i.val]? = some subtractWordSpec) (original entered current : Memory)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (left right output borrowHome : Reference)
    (call : CallingConditions program original [left, right] [output])
    (currentCall : CallingConditions program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (homes : NumericHomes entered original.nextIdentity specs slots)
    (enteredWF : entered.WellFormed)
    (authority : AccessBelow entered.nextIdentity entered current)
    (borrowSlot : frame.locals[ws + 1]? = some (.bytes .word64 borrowHome))
    (borrowRead : read current borrowHome 8 1 = .ok (numberBytes 0 8)) :
    ∃ results : Fin 4 → Reference,
      ScalarBorrowState (program := program) original current frame left right output borrowHome results 0
        (ws + 1) (ws + 1 + 1) := by
  classical
  have allHomes := subtract_repair_word_home_at specs ws wordSpecs original entered current frame root slots layout
    homes enteredWF authority
  obtain ⟨borrowRef, borrowLocal, actualBorrow, borrowFresh, borrowWrite⟩ := allHomes 0
  have same : borrowRef = borrowHome := by
    have local0 : frame.locals[ws + 1]? = some (.bytes .word64 borrowRef) := by simpa using actualBorrow
    rw [borrowSlot] at local0
    simpa using local0.symm
  subst borrowRef
  let results : Fin 4 → Reference := fun i => Classical.choose (allHomes ⟨i.val + 1, by omega⟩)
  have resultFacts (i : Fin 4) := Classical.choose_spec (allHomes ⟨i.val + 1, by omega⟩)
  have resultSlots (i : Fin 4) : slots[ws + (i.val + 1)]? = some (.bytes .word64 (results i)) := (resultFacts i).1
  have borrowSlotTail : slots[ws]? = some (.bytes .word64 borrowHome) := by simpa using borrowLocal
  have ordered (i : Fin 4) : borrowHome.allocation < (results i).allocation :=
    homes.ordered ws (ws + (i.val + 1)) .word64 .word64 borrowHome (results i) (by omega) borrowSlotTail (resultSlots i)
  refine ⟨results, currentCall, ?_, borrowSlot, ?_, borrowWrite, ?_, borrowRead, by simp [scalarBorrowValue],
    ?_, (fun i => Ne.symm (Nat.ne_of_lt (ordered i))), ?_, borrowFresh, ?_, preserved.cells, ?_⟩
  · intro reference member
    exact call.input_bytes_of_memory_below preserved member
  · intro i
    have found := (resultFacts i).2.1
    rw [show i.val + (ws + 1 + 1) = ws + 1 + (i.val + 1) by omega]
    exact found
  · intro i
    exact (resultFacts i).2.2.2
  · intro reference member
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed member)
    have old : reference.allocation < original.nextIdentity := (call.1.1.1 _ _ present).1
    exact ⟨Nat.ne_of_lt (Nat.lt_of_lt_of_le old borrowFresh),
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

/-- From the repair start, zero the borrow and run all four checked borrow calls on the initial limbs. -/
theorem subtract_repair_borrow_at (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (base ws : Nat) (leading tail : List CIL.Op) (leadingLength : leading.length = base)
    (borrow : Nat) (code : body.code = leading ++ subtractRepairBorrowCode (ws + 1) borrow ++ tail)
    (borrowFound : program[borrow]? = some (borrowBody body.profile))
    (wordSpecs : ∀ i : Fin 5, specs[ws + i.val]? = some subtractWordSpec)
    (original entered current : Memory)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (left right output : Reference)
    (call : CallingConditions program original [left, right] [output])
    (currentCall : CallingConditions program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (homes : NumericHomes entered original.nextIdentity specs slots)
    (enteredWF : entered.WellFormed)
    (authority : AccessBelow entered.nextIdentity entered current)
    (args : List Value)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ borrowHome results after,
      ScalarBorrowState (program := program) original after frame left right output borrowHome results 4
        (ws + 1) (ws + 1 + 1) →
      ∃ fuel final returned,
        run program fuel method (base + 31) args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method base args frame [] current = .ok (final, returned) ∧ post final returned := by
  apply subtract_repair_start_at program body method specs found base ws leading tail leadingLength borrow code
    (by simpa using wordSpecs 0) original.nextIdentity entered current [left, right] [output]
    frame root slots layout args currentCall enteredWF homes authority post
  intro borrowHome after borrowSlot borrowRead retained afterCall afterAuthority _written
  obtain ⟨results, ready⟩ := subtract_repair_ready_at program specs ws wordSpecs original entered after frame root slots
    layout left right output borrowHome call afterCall (preserved.trans retained) homes enteredWF afterAuthority
    borrowSlot borrowRead
  exact subtract_repair_all_at program body method found base (ws + 1) leading tail leadingLength borrow code borrowFound
    ready args leftArg rightArg post (continuation borrowHome results)

#print axioms subtract_repair_word_home_at
#print axioms subtract_repair_ready_at
#print axioms subtract_repair_borrow_at
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Subtract.Safety

/-- Push the output reference and the four completed words for the storage call. -/
theorem subtract_store_prefix_at (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (base bl : Nat) (leading tail : List CIL.Op) (leadingLength : leading.length = base)
    (storage : Nat) (code : body.code = leading ++ subtractStoreCode bl storage ++ tail)
    (output : Reference) (args : List Value)
    (outputArg : args[2]? = some (.reference (.address output)))
    (frame : Frame) (memory : Memory) (results : Fin 4 → Reference) (words : Fin 4 → BitVec 64)
    (outputFormed : form memory output = .ok output)
    (slots : ∀ i, frame.locals[i.val + (bl + 1)]? = some (.bytes .word64 (results i)))
    (reads : ∀ i, read memory (results i) 8 1 = .ok (numberBytes (words i).toNat 8))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method (base + 5) args frame
        [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
          .scalar (.i64 (words 0)), .reference (.address output)] memory = .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run program fuel method base args frame [] memory = .ok (result, returned) ∧ post result returned := by
  have s0 : frame.locals[bl + 1]? = some (.bytes .word64 (results 0)) := by simpa using slots 0
  have s1 : frame.locals[bl + 2]? = some (.bytes .word64 (results 1)) := by
    simpa [show 1 + (bl + 1) = bl + 2 by omega] using slots 1
  have s2 : frame.locals[bl + 3]? = some (.bytes .word64 (results 2)) := by
    simpa [show 2 + (bl + 1) = bl + 3 by omega] using slots 2
  have s3 : frame.locals[bl + 4]? = some (.bytes .word64 (results 3)) := by
    simpa [CIL.fin_val_three, show 3 + (bl + 1) = bl + 4 by omega] using slots 3
  have r0 := load_local_word64_of_read (reads 0)
  have r1 := load_local_word64_of_read (reads 1)
  have r2 := load_local_word64_of_read (reads 2)
  have r3 := load_local_word64_of_read (reads 3)
  repeat' first
    | exact continuation
    | (apply run_next_exists post found (by seg_fetch code leadingLength)
       simp (config := { implicitDefEqProofs := false })
         [step, checkedValue, formValue, outputArg, outputFormed, s0, s1, s2, s3, r0, r1, r2, r3,
           checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

/-- Return the final borrow word as the unsigned underflow flag and retire the frame. -/
theorem subtract_store_return_at (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (base bl : Nat) (leading tail : List CIL.Op) (leadingLength : leading.length = base)
    (storage : Nat) (code : body.code = leading ++ subtractStoreCode bl storage ++ tail)
    (returns : body.returnsValue = true)
    (args : List Value) (frame : Frame) (memory : Memory)
    (borrowHome : Reference) (borrowWord : BitVec 64)
    (slot : frame.locals[bl]? = some (.bytes .word64 borrowHome))
    (loaded : read memory borrowHome 8 1 = .ok (numberBytes borrowWord.toNat 8)) :
    run program 5 method (base + 6) args frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (scalarUnderflowFlag borrowWord))]) := by
  have reading := load_local_word64_of_read loaded
  iterate 4
    apply Eq.trans
    · apply run_next found (by seg_fetch code leadingLength)
      simp (config := { implicitDefEqProofs := false })
        [step, slot, reading, checkedValue, numericValue, pureArity, scalars,
          CIL.step.eq_def, CIL.binary, CIL.unary, instruction, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  have fetched : body.code[base + 6 + 1 + 1 + 1 + 1]? = some (.ret (some .unsigned8)) := by
    seg_fetch code leadingLength
  by_cases positive : BitVec.ofNat 64 0 < borrowWord
  all_goals simp [run, found, fetched, returns, step, checkedValue, numericValue, CIL.NarrowKind.extend,
    scalarUnderflowFlag, positive, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Store the four ripple words through the checked limb helper and return the exact borrow. -/
theorem subtract_store_finish_at (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (base bl : Nat) (leading tail : List CIL.Op) (leadingLength : leading.length = base)
    (storage : Nat) (code : body.code = leading ++ subtractStoreCode bl storage ++ tail)
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body body.profile))
    (returns : body.returnsValue = true)
    (original current : CIL.Safety.Memory) (frame : Frame)
    (left right output borrowHome : Reference) (results : Fin 4 → Reference) (args : List Value)
    (outputArg : args[2]? = some (.reference (.address output)))
    (call : CallingConditions program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : ScalarBorrowState (program := program) original current frame left right output borrowHome results 4
      bl (bl + 1)) :
    ∃ fuel final values,
      run program fuel method base args frame [] current = .ok (final, values) ∧
      SubtractResult original final values left right output := by
  let words := scalarDifferenceWord original left right
  let post := fun final values => SubtractResult original final values left right output
  have formed := state.call.output_formed (by simp : output ∈ [output])
  apply subtract_store_prefix_at program body method found base bl leading tail leadingLength storage code
    output args outputArg frame current results words formed state.resultSlots (fun i => state.completed i i.isLt) post
  obtain ⟨childFuel, stored, invoked, valid, outside, authority, value, _⟩ :=
    UInt256Proof.Multiply.LimbStorage.store_limbs_readable_contract body.profile program storage storageFound
      current [left, right] output (words 0) (words 1) (words 2) (words 3) state.call
  have stepped : step body (.call storage 5) (base + 5) args frame
      [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
        .scalar (.i64 (words 0)), .reference (.address output)] current =
      .ok (.call storage (UInt256Proof.Multiply.LimbStorage.arguments output (words 0) (words 1) (words 2) (words 3)) [] current) := by
    simp [step, UInt256Proof.Multiply.LimbStorage.arguments, checkedValue, numericValue,
      formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    try exact ⟨rfl, rfl⟩
  obtain ⟨outputAllocation, outputPresent, _, _⟩ := formed_reference_live _ _ _
    (call.output_formed (by simp : output ∈ [output]))
  have outputOld := (call.1.1.1 _ _ outputPresent).1
  obtain ⟨borrowAllocation, borrowPresent, _, _⟩ := access_within_allocation _ _ _ _ _ state.borrowWrite
  have borrowOld := (state.call.1.1.1 _ _ borrowPresent).1
  have distinct : borrowHome.allocation ≠ output.allocation :=
    Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le outputOld state.borrowFresh))
  have borrowRead := authority.read_eq state.borrowRead borrowOld
    (fun i _ => outside _ _ (Or.inl distinct))
  have returned := subtract_store_return_at program body method found base bl leading tail leadingLength storage code
    returns args frame stored borrowHome _ state.borrowSlot borrowRead
  obtain ⟨fuel, executed⟩ := run_call_exists found
    (by seg_fetch code leadingLength) stepped ⟨childFuel, invoked⟩ ⟨5, returned⟩
  refine ⟨fuel, leaveFrame frame stored, _, executed, ?_⟩
  have retained := leaveFrame_preserves_memory_below frame stored original.nextIdentity owned
  have bytes : (fun offset => ((leaveFrame frame stored).cells output.allocation offset).bits) =
      (fun offset => (stored.cells output.allocation offset).bits) := by
    funext offset
    rw [retained.cells output.allocation outputOld offset]
  refine ⟨leaveFrame_preserves_wellFormed _ _ valid.1.1, ?_, ?_, ?_, ?_⟩
  · have computed : inputValue (leaveFrame frame stored) output = scalarDifferenceValue original left right := by
      simpa only [inputValue, bytes, scalarDifferenceValue] using value
    exact computed.trans (scalar_difference_value original left right)
  · rw [scalar_flag_underflow]
    rfl
  · exact (retained.access output outputOld 32 1 true).trans
      (valid.1.2.2 (wordView output) (by simp))
  · intro id old offset untouched
    exact (retained.cells id old offset).trans ((outside id offset untouched).trans (state.callerCells id old offset))

#print axioms subtract_store_prefix_at
#print axioms subtract_store_return_at
#print axioms subtract_store_finish_at
end UInt256Proof.Subtract.Profile
