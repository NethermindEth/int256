import UInt256.Methods.Add.SSEShapes.Fast
import UInt256.Methods.Add.SSERepair
import UInt256.Methods.Add.SSEShapes.ReversedStorage

namespace UInt256Proof.Add.SSEShapes
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety UInt256Proof.Add.CarrySafety UInt256Proof.Safety

/-- The carry-call repair; `reversed` pushes the sum words from the top limb down. -/
def repairCodeOf (reversed : Bool) (carry storage : Nat) : List CIL.Op := [
  .const32 0, .convI8, .setLocal 15,
  .arg 0, .fieldAt 0 8, .arg 1, .fieldAt 0 8, .localAddr 15, .localAddr 16, .call carry 4,
  .arg 0, .fieldAt 8 8, .arg 1, .fieldAt 8 8, .localAddr 15, .localAddr 17, .call carry 4,
  .arg 0, .fieldAt 16 8, .arg 1, .fieldAt 16 8, .localAddr 15, .localAddr 18, .call carry 4,
  .arg 0, .fieldAt 24 8, .arg 1, .fieldAt 24 8, .localAddr 15, .localAddr 19, .call carry 4,
  .arg 2, .local (bif reversed then 19 else 16), .local (bif reversed then 18 else 17),
  .local (bif reversed then 17 else 18), .local (bif reversed then 16 else 19),
  .call storage 5, .local 15, .const32 0, .convI8, .gtu, .ret (some .unsigned8)]

theorem repairCodeOf_false (carry storage : Nat) : repairCodeOf false carry storage = sseRepairCode carry storage := rfl

/-- Operand stack at the storage call. -/
def repairStack (reversed : Bool) (output : Reference) (words : Fin 4 → BitVec 64) : List Value :=
  bif reversed then
    [.scalar (.i64 (words 0)), .scalar (.i64 (words 1)), .scalar (.i64 (words 2)),
      .scalar (.i64 (words 3)), .reference (.address output)]
  else
    [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
      .scalar (.i64 (words 0)), .reference (.address output)]

/-- Arguments passed to the storage callee. -/
def repairArgs (reversed : Bool) (output : Reference) (words : Fin 4 → BitVec 64) : List Value :=
  bif reversed then UInt256Proof.Multiply.LimbStorage.arguments output (words 3) (words 2) (words 1) (words 0)
  else UInt256Proof.Multiply.LimbStorage.arguments output (words 0) (words 1) (words 2) (words 3)

/-- Storage callee matching the push order. -/
def repairStorage (reversed : Bool) (profile : CIL.FeatureProfile) : CIL.Method :=
  bif reversed then ReversedStorage.body profile else UInt256Proof.Multiply.LimbStorage.body profile

/-- Initialize the private carry word before the SSE scalar repair cascade. -/
theorem sse_repair_start (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (carry storage : Nat) (reversed : Bool) (code : body.code = leading ++ repairCodeOf reversed carry storage ++ tail)
    (carrySpec : specs[14]? = some armWordSpec)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[15]? = some (.bytes .word64 reference) →
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
      enteredWF homes authority 14 armWordSpec carrySpec (.i64 0) 0 rfl
  have done := continuation reference after slot loaded retained afterCall afterAuthority written
  repeat' first
    | exact done
    | (normalize_pc
       apply run_next_exists post found (by fetch_segment)
       first
       | exact stored _ _ _
       | (simp (config := { implicitDefEqProofs := false })
           [step, pureArity, scalars, CIL.step.eq_def, CIL.unary, checkedValue, numericValue,
             Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))


/-- Load both operand limbs and the two private word addresses for one carry call. -/
theorem sse_carry_segment (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (carry storage : Nat) (reversed : Bool) (code : body.code = leading ++ repairCodeOf reversed carry storage ++ tail)
    (segment : Fin 4) (left right : Reference) (args : List Value)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (frame : Frame) (memory : Memory) (a b : BitVec 64) (carryHome resultHome : Reference)
    (leftFormed : form memory left = .ok left) (rightFormed : form memory right = .ok right)
    (leftRead : ∀ rest, instruction (.fieldAt (8 * segment.val) 8)
      (.reference (.address left) :: rest) memory = .ok (memory, .scalar (.i64 a) :: rest))
    (rightRead : ∀ rest, instruction (.fieldAt (8 * segment.val) 8)
      (.reference (.address right) :: rest) memory = .ok (memory, .scalar (.i64 b) :: rest))
    (carrySlot : frame.locals[15]? = some (.bytes .word64 carryHome))
    (resultSlot : frame.locals[segment.val + 16]? = some (.bytes .word64 resultHome))
    (carryFormed : form memory carryHome = .ok carryHome)
    (resultFormed : form memory resultHome = .ok resultHome)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method (base + (9 + 7 * segment.val)) args frame
        [.reference (.address resultHome), .reference (.address carryHome), .scalar (.i64 b), .scalar (.i64 a)]
        memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (base + (3 + 7 * segment.val)) args frame [] memory =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨segment, bound⟩ := segment
  have cases : segment = 0 ∨ segment = 1 ∨ segment = 2 ∨ segment = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  all_goals
    simp only [Nat.reduceMul, Nat.reduceAdd] at leftRead rightRead resultSlot continuation ⊢
    repeat' first
      | exact continuation
      | (normalize_pc
         apply run_next_exists post found (by fetch_segment)
         simp (config := { implicitDefEqProofs := false })
           [step, checkedValue, numericValue, formValue, leftArg, rightArg, leftFormed, rightFormed,
             carryFormed, resultFormed, carrySlot, resultSlot, localAddress, leftRead, rightRead,
             pureArity, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
         first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)


/-- One fetched carry call composes with the checked carry-helper contract. -/
theorem sse_indexed_carry (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (carry storage : Nat) (reversed : Bool) (code : body.code = leading ++ repairCodeOf reversed carry storage ++ tail)
    (carryFound : program[carry]? = some (carryBody body.profile))
    (index : Fin 4) (args : List Value) (frame : Frame) (memory : Memory)
    (a b c : BitVec 64) (carryHome resultHome : Reference)
    (wellFormed : memory.WellFormed) (incoming : c.toNat ≤ 1)
    (carryRead : read memory carryHome 8 1 = .ok (numberBytes c.toNat 8))
    (carryWrite : access memory carryHome 8 1 true = .ok ())
    (resultWrite : access memory resultHome 8 1 true = .ok ())
    (disjoint : WordsDisjoint carryHome resultHome)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, CarryPost (program := program) a b c carryHome resultHome memory after →
      ∃ fuel result returned,
        run program fuel method (base + (10 + 7 * index.val)) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (base + (9 + 7 * index.val)) args frame
        [.reference (.address resultHome), .reference (.address carryHome), .scalar (.i64 b), .scalar (.i64 a)]
        memory = .ok (result, returned) ∧ post result returned := by
  have carryFormed := access_reference_valid _ _ _ _ _ carryWrite
  have resultFormed := access_reference_valid _ _ _ _ _ resultWrite
  obtain ⟨childFuel, stored, invoked, guarantees⟩ := carry_checked_contract carryFound a b c carryHome resultHome
    memory wellFormed incoming carryRead carryWrite resultWrite disjoint
  obtain ⟨parentFuel, result, values, resumed, satisfied⟩ := continuation stored guarantees
  have fetched : body.code[base + (9 + 7 * index.val)]? = some (.call carry 4) := by
    obtain ⟨index, bound⟩ := index
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    all_goals exact code_at code leadingLength rfl
  have stepped : step body (.call carry 4) (base + (9 + 7 * index.val)) args frame
      [.reference (.address resultHome), .reference (.address carryHome), .scalar (.i64 b), .scalar (.i64 a)] memory =
      .ok (.call carry [.scalar (.i64 a), .scalar (.i64 b), .reference (.address carryHome),
        .reference (.address resultHome)] [] memory) := by
    simp [step, checkedValue, numericValue, formValue, carryFormed, resultFormed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    try exact ⟨rfl, rfl⟩
  have resumed' : run program parentFuel method (base + (9 + 7 * index.val) + 1) args frame [] stored =
      .ok (result, values) := by
    simpa only [show base + (9 + 7 * index.val) + 1 = base + (10 + 7 * index.val) by omega] using resumed
  obtain ⟨fuel, finished⟩ := run_call_exists found fetched stepped ⟨childFuel, invoked⟩ ⟨parentFuel, resumed'⟩
  exact ⟨fuel, result, values, finished, satisfied⟩


/-- Caller views discharge both limb loads; checked homes discharge the carry call. -/
theorem sse_carry_segment_checked (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (carry storage : Nat) (reversed : Bool) (code : body.code = leading ++ repairCodeOf reversed carry storage ++ tail)
    (carryFound : program[carry]? = some (carryBody body.profile))
    (segment : Fin 4) (left right output : Reference) (args : List Value)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (frame : Frame) (memory : CIL.Safety.Memory) (c : BitVec 64) (carryHome resultHome : Reference)
    (call : CallingConditions program memory [left, right] [output])
    (carrySlot : frame.locals[15]? = some (.bytes .word64 carryHome))
    (resultSlot : frame.locals[segment.val + 16]? = some (.bytes .word64 resultHome))
    (incoming : c.toNat ≤ 1)
    (carryRead : read memory carryHome 8 1 = .ok (numberBytes c.toNat 8))
    (carryWrite : access memory carryHome 8 1 true = .ok ())
    (resultWrite : access memory resultHome 8 1 true = .ok ())
    (disjoint : WordsDisjoint carryHome resultHome)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ after,
      CarryPost (program := program) (inputLimb memory left segment)
        (inputLimb memory right segment) c carryHome resultHome memory after →
      ∃ fuel result returned,
        run program fuel method (base + (10 + 7 * segment.val)) args frame [] after = .ok (result, returned) ∧
          post result returned) :
    ∃ fuel result returned,
      run program fuel method (base + (3 + 7 * segment.val)) args frame [] memory =
        .ok (result, returned) ∧ post result returned := by
  apply sse_carry_segment program body method found leading tail base leadingLength carry storage reversed code
    segment left right args leftArg rightArg frame memory _ _ carryHome resultHome
    (call.input_formed (by simp)) (call.input_formed (by simp))
    (fun rest => call.input_field_instruction (by simp) _ rest)
    (fun rest => call.input_field_instruction (by simp) _ rest) carrySlot resultSlot
    (access_reference_valid _ _ _ _ _ carryWrite) (access_reference_valid _ _ _ _ _ resultWrite) post
  exact sse_indexed_carry program body method found leading tail base leadingLength carry storage reversed code carryFound
    segment args frame memory _ _ c carryHome resultHome call.1.1 incoming carryRead carryWrite resultWrite disjoint
    post continuation


/-- Advance the carry invariant through one actual SSE repair call. -/
theorem sse_carry_next (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (carry storage : Nat) (reversed : Bool) (code : body.code = leading ++ repairCodeOf reversed carry storage ++ tail)
    (carryFound : program[carry]? = some (carryBody body.profile))
    {original before : Memory} {frame : Frame}
    {left right output carryHome : Reference} {results : Fin 4 → Reference} (index : Fin 4)
    (state : ScalarCarryState (program := program) original before frame left right output carryHome results index.val 15 16)
    (args : List Value)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarCarryState (program := program) original after frame left right output carryHome results (index.val + 1) 15 16 →
      ∃ fuel result returned,
        run program fuel method (base + (10 + 7 * index.val)) args frame [] after = .ok (result, returned) ∧
          post result returned) :
    ∃ fuel result returned,
      run program fuel method (base + (3 + 7 * index.val)) args frame [] before =
        .ok (result, returned) ∧ post result returned := by
  apply sse_carry_segment_checked program body method found leading tail base leadingLength carry storage reversed code
    carryFound index left right output args leftArg rightArg frame before
    (scalarCarryValue original left right index.val) carryHome (results index) state.call
    state.carrySlot (state.resultSlots index) state.carryBound state.carryRead state.carryWrite
    (state.resultWrites index) (Or.inl (Ne.symm (state.carrySeparate index))) post
  intro after math
  apply continuation after
  apply state.advance index
  simpa only [inputLimb, state.inputBytes left (by simp), state.inputBytes right (by simp)] using math

/-- All four carry calls keep the initial operands, private homes and completed limbs. -/
theorem sse_carry_all (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (carry storage : Nat) (reversed : Bool) (code : body.code = leading ++ repairCodeOf reversed carry storage ++ tail)
    (carryFound : program[carry]? = some (carryBody body.profile))
    {original before : Memory} {frame : Frame}
    {left right output carryHome : Reference} {results : Fin 4 → Reference}
    (state : ScalarCarryState (program := program) original before frame left right output carryHome results 0 15 16)
    (args : List Value)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      ScalarCarryState (program := program) original after frame left right output carryHome results 4 15 16 →
      ∃ fuel result returned,
        run program fuel method (base + 31) args frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (base + 3) args frame [] before = .ok (result, returned) ∧ post result returned := by
  apply sse_carry_next program body method found leading tail base leadingLength carry storage reversed code carryFound
    0 state args leftArg rightArg post
  intro _ first
  apply sse_carry_next program body method found leading tail base leadingLength carry storage reversed code carryFound
    1 first args leftArg rightArg post
  intro _ second
  apply sse_carry_next program body method found leading tail base leadingLength carry storage reversed code carryFound
    2 second args leftArg rightArg post
  intro _ third
  exact sse_carry_next program body method found leading tail base leadingLength carry storage reversed code carryFound
    3 third args leftArg rightArg post continuation


/-- From the repair entry, zero the carry and run all four checked carry calls on the initial limbs. -/
theorem sse_repair_carry (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (carry storage : Nat) (reversed : Bool) (code : body.code = leading ++ repairCodeOf reversed carry storage ++ tail)
    (carryFound : program[carry]? = some (carryBody body.profile))
    (wordSpecs : ∀ i : Fin 5, specs[14 + i.val]? = some armWordSpec)
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
    (continuation : ∀ carryHome results after,
      ScalarCarryState (program := program) original after frame left right output carryHome results 4 15 16 →
      ∃ fuel final returned,
        run program fuel method (base + 31) args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method base args frame [] current = .ok (final, returned) ∧ post final returned := by
  apply sse_repair_start program body method specs found leading tail base leadingLength carry storage reversed code
    (wordSpecs 0) original.nextIdentity entered current [left, right] [output]
    frame root slots layout args currentCall enteredWF homes authority post
  intro carryHome after carrySlot carryRead retained afterCall afterAuthority _written
  obtain ⟨results, ready⟩ := vector128_sse_carry_ready program specs wordSpecs original entered after frame root slots layout
    left right output carryHome call afterCall (preserved.trans retained) homes enteredWF afterAuthority carrySlot carryRead
  exact sse_carry_all program body method found leading tail base leadingLength carry storage reversed code carryFound
    ready args leftArg rightArg post (continuation carryHome results)


/-- Push the output reference and the four completed sum words for the storage call. -/
theorem sse_store_prefix (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (carry storage : Nat) (reversed : Bool) (code : body.code = leading ++ repairCodeOf reversed carry storage ++ tail)
    (output : Reference) (args : List Value)
    (outputArg : args[2]? = some (.reference (.address output)))
    (frame : Frame) (memory : Memory) (results : Fin 4 → Reference) (words : Fin 4 → BitVec 64)
    (outputFormed : form memory output = .ok output)
    (slots : ∀ i, frame.locals[i.val + 16]? = some (.bytes .word64 (results i)))
    (reads : ∀ i, read memory (results i) 8 1 = .ok (numberBytes (words i).toNat 8))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method (base + 36) args frame (repairStack reversed output words) memory =
        .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (base + 31) args frame [] memory = .ok (result, returned) ∧ post result returned := by
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
  cases reversed <;> simp only [repairStack, Bool.cond_true, Bool.cond_false] at continuation
  all_goals
    repeat' first
      | exact continuation
      | (normalize_pc
         apply run_next_exists post found (by fetch_segment)
         simp (config := { implicitDefEqProofs := false })
           [step, checkedValue, formValue, outputArg, outputFormed, s0, s1, s2, s3, r0, r1, r2, r3,
             Bool.cond_true, Bool.cond_false, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
         first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

/-- Return the final carry word as the unsigned overflow flag and retire the frame. -/
theorem sse_return (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (carry storage : Nat) (reversed : Bool) (code : body.code = leading ++ repairCodeOf reversed carry storage ++ tail)
    (returns : body.returnsValue = true)
    (args : List Value) (frame : Frame) (memory : Memory)
    (carryHome : Reference) (carryWord : BitVec 64)
    (slot : frame.locals[15]? = some (.bytes .word64 carryHome))
    (loaded : read memory carryHome 8 1 = .ok (numberBytes carryWord.toNat 8)) :
    run program 5 method (base + 37) args frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (scalarOverflowFlag carryWord))]) := by
  have reading := load_local_word64_of_read loaded
  iterate 4
    normalize_pc
    apply Eq.trans
    · apply run_next found (by fetch_segment)
      simp (config := { implicitDefEqProofs := false })
        [step, slot, reading, checkedValue, numericValue, pureArity, scalars,
          CIL.step.eq_def, CIL.binary, CIL.unary, instruction, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
  normalize_pc
  have fetched : body.code[base + 41]? = some (.ret (some .unsigned8)) := code_at code leadingLength rfl
  by_cases positive : BitVec.ofNat 64 0 < carryWord
  all_goals simp [run, found, fetched, returns, step, checkedValue, numericValue, CIL.NarrowKind.extend,
    scalarOverflowFlag, positive, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]


/-- Store the four ripple words through the checked limb helper and return the exact carry. -/
theorem sse_finish (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (carry storage : Nat) (reversed : Bool) (code : body.code = leading ++ repairCodeOf reversed carry storage ++ tail)
    (storageFound : program[storage]? = some (repairStorage reversed body.profile))
    (returns : body.returnsValue = true)
    (original current : CIL.Safety.Memory) (frame : Frame)
    (left right output carryHome : Reference) (results : Fin 4 → Reference) (args : List Value)
    (outputArg : args[2]? = some (.reference (.address output)))
    (call : CallingConditions program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (state : ScalarCarryState (program := program) original current frame left right output carryHome results 4 15 16) :
    ∃ fuel final values,
      run program fuel method (base + 31) args frame [] current = .ok (final, values) ∧
      AddResult original final values left right output := by
  let words := scalarSumWord original left right
  let post := fun final values => AddResult original final values left right output
  have formed := state.call.output_formed (by simp : output ∈ [output])
  apply sse_store_prefix program body method found leading tail base leadingLength carry storage reversed code
    output args outputArg frame current results words formed state.resultSlots (fun i => state.completed i i.isLt) post
  obtain ⟨childFuel, stored, invoked, valid, outside, authority, value, _⟩ :
      ∃ fuel result,
        invoke program fuel storage (repairArgs reversed output words) current = .ok (result, []) ∧
        CallingConditions program result [left, right] [output] ∧
        (∀ id offset, OutsideOutput output id offset → result.cells id offset = current.cells id offset) ∧
        AccessBelow current.nextIdentity current result ∧
        inputValue result output = BitVec.ofNat 256
          ((words 0).toNat + (words 1).toNat * 2^64 + (words 2).toNat * 2^128 + (words 3).toNat * 2^192) ∧
        (∃ bytes, read result output 32 1 = .ok bytes) := by
    cases reversed
    · exact UInt256Proof.Multiply.LimbStorage.store_limbs_readable_contract body.profile program storage storageFound
        current [left, right] output (words 0) (words 1) (words 2) (words 3) state.call
    · exact ReversedStorage.store_limbs_readable_contract body.profile program storage storageFound
        current [left, right] output (words 0) (words 1) (words 2) (words 3) state.call
  have stepped : step body (.call storage 5) (base + 36) args frame (repairStack reversed output words) current =
      .ok (.call storage (repairArgs reversed output words) [] current) := by
    cases reversed <;>
      simp [step, repairStack, repairArgs, UInt256Proof.Multiply.LimbStorage.arguments, checkedValue, numericValue,
        formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] <;>
      exact ⟨rfl, rfl⟩
  obtain ⟨outputAllocation, outputPresent, _, _⟩ := formed_reference_live _ _ _
    (call.output_formed (by simp : output ∈ [output]))
  have outputOld := (call.1.1.1 _ _ outputPresent).1
  obtain ⟨carryAllocation, carryPresent, _, _⟩ := access_within_allocation _ _ _ _ _ state.carryWrite
  have carryOld := (state.call.1.1.1 _ _ carryPresent).1
  have distinct : carryHome.allocation ≠ output.allocation :=
    Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le outputOld state.carryFresh))
  have carryRead := authority.read_eq state.carryRead carryOld
    (fun i _ => outside _ _ (Or.inl distinct))
  have returned := sse_return program body method found leading tail base leadingLength carry storage reversed code returns
    args frame stored carryHome _ state.carrySlot carryRead
  obtain ⟨fuel, executed⟩ := run_call_exists found
    (code_at code leadingLength rfl) stepped ⟨childFuel, invoked⟩ ⟨5, returned⟩
  refine ⟨fuel, leaveFrame frame stored, _, executed, ?_⟩
  have retained := leaveFrame_preserves_memory_below frame stored original.nextIdentity owned
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


#print axioms sse_repair_start
#print axioms sse_carry_segment
#print axioms sse_indexed_carry
#print axioms sse_carry_segment_checked
#print axioms sse_carry_next
#print axioms sse_carry_all
#print axioms sse_repair_carry
#print axioms sse_store_prefix
#print axioms sse_return
#print axioms sse_finish
end UInt256Proof.Add.SSEShapes
