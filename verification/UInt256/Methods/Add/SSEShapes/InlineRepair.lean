import UInt256.Methods.Add.SSEShapes.Helper

namespace UInt256Proof.Add.SSEShapes
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety UInt256Proof.Add.CarrySafety UInt256Proof.Safety

/-- One inlined limb: sum, carry-in add, and the two-compare carry-out into local 15. -/
def inlineLimb (i : Nat) : List CIL.Op := [
  .arg 0, .fieldAt (8 * i) 8, .arg 1, .fieldAt (8 * i) 8, .add, .setLocal (16 + 2 * i),
  .local (16 + 2 * i), .local 15, .add, .setLocal (17 + 2 * i),
  .local (16 + 2 * i), .arg 0, .fieldAt (8 * i) 8, .ltu, .convI8,
  .local (17 + 2 * i), .local (16 + 2 * i), .ltu, .convI8, .add, .setLocal 15]

/-- Store the four sum words and return the carry flag. -/
def inlineTail (storage : Nat) : List CIL.Op :=
  [.arg 2, .local 17, .local 19, .local 21, .local 23, .call storage 5,
    .local 15, .const32 0, .convI8, .gtu, .ret (some .unsigned8)]

/-- The repair with the carry helper inlined: four limbs, one limb store, the carry flag. -/
def inlineRepairCode (storage : Nat) : List CIL.Op :=
  [.const32 0, .convI8, .setLocal 15] ++ inlineLimb 0 ++ inlineLimb 1 ++ inlineLimb 2 ++ inlineLimb 3 ++
  inlineTail storage

/-- Overwriting any private word home preserves every other word home. -/
theorem word_other_read (specs : List NumericLocalSpec) (entered before after : Memory) (boundary : Nat)
    (slots : List LocalSlot) (homes : NumericHomes entered boundary specs slots)
    (i j : Nat) (different : i ≠ j) (source target : Reference)
    (sourceSlot : slots[i]? = some (.bytes .word64 source))
    (targetSlot : slots[j]? = some (.bytes .word64 target))
    (bytes value : List (BitVec 8))
    (written : write before target bytes 1 = .ok after)
    (loaded : read before source 8 1 = .ok value) :
    read after source 8 1 = .ok value := by
  by_cases earlier : i < j
  · have ordered := homes.ordered i j .word64 .word64 source target earlier sourceSlot targetSlot
    exact write_preserves_disjoint_read written loaded (Or.inl (Nat.ne_of_lt ordered))
  · have ordered := homes.ordered j i .word64 .word64 target source (by omega) targetSlot sourceSlot
    exact write_preserves_disjoint_read written loaded (Or.inl (Nat.ne_of_gt ordered))

/-- Progress through the inlined limbs: carry word and completed sum words in their private homes. -/
structure InlineState (program : CIL.Program) (original entered current : Memory) (slots : List LocalSlot)
    (left right output : Reference) (done : Nat) : Prop where
  call : CallingConditions program current [left, right] [output]
  preserved : MemoryBelow original.nextIdentity original current
  authority : AccessBelow entered.nextIdentity entered current
  carry : ∃ home, slots[14]? = some (.bytes .word64 home) ∧
    read current home 8 1 = .ok (numberBytes (scalarCarryValue original left right done).toNat 8)
  carryBound : (scalarCarryValue original left right done).toNat ≤ 1
  completed : ∀ i : Fin 4, i.val < done → ∃ home, slots[16 + 2 * i.val]? = some (.bytes .word64 home) ∧
    read current home 8 1 = .ok (numberBytes (scalarSumWord original left right i).toNat 8)

/-- Zero the carry word. -/
theorem inline_start (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (storage : Nat) (code : body.code = leading ++ inlineRepairCode storage ++ tail)
    (carrySpec : specs[14]? = some armWordSpec)
    (original entered current : Memory) (frame : Frame) (slots : List LocalSlot)
    (left right output : Reference) (args : List Value)
    (layout : frame.locals = .root (some (.address right)) :: slots)
    (currentCall : CallingConditions program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered original.nextIdentity specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, InlineState program original entered after slots left right output 0 →
      ∃ fuel final returned,
        run program fuel method (base + 3) args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method base args frame [] current = .ok (final, returned) ∧ post final returned := by
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store program body specs original.nextIdentity entered current [left, right] [output] frame
      (.root (some (.address right))) slots layout currentCall enteredWF homes authority 14 armWordSpec carrySpec (.i64 0) 0 rfl
  have slotTail : slots[14]? = some (.bytes .word64 reference) := by simpa [layout, armWordSpec] using slot
  have done := continuation after ⟨afterCall, preserved.trans retained, afterAuthority, ⟨reference, slotTail, loaded⟩,
    by simp [scalarCarryValue], fun i bound => absurd bound (Nat.not_lt_zero _)⟩
  repeat' (normalize_pc; first
    | exact done
    | (apply run_next_exists post found (by fetch_segment)
       first
       | exact stored _ _ _
       | (simp (config := { implicitDefEqProofs := false })
           [step, pureArity, scalars, CIL.step.eq_def, CIL.unary, checkedValue, numericValue,
             Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)))

#print axioms word_other_read
#print axioms inline_start
end UInt256Proof.Add.SSEShapes

namespace UInt256Proof.Add.SSEShapes
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety UInt256Proof.Add.CarrySafety UInt256Proof.Safety

/-- The 21 instructions of one inlined limb, given its three private stores and the reads between them. -/
theorem inline_limb_run (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (i : Nat) (code : body.code = leading ++ inlineLimb i ++ tail)
    (args : List Value) (frame : Frame) (left right : Reference)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (a b c : BitVec 64) (current m1 m2 m3 : Memory)
    (formedL0 : form current left = .ok left) (formedR0 : form current right = .ok right)
    (formedL2 : form m2 left = .ok left)
    (fL0 : ∀ rest, instruction (.fieldAt (8 * i) 8) (.reference (.address left) :: rest) current =
      .ok (current, .scalar (.i64 a) :: rest))
    (fR0 : ∀ rest, instruction (.fieldAt (8 * i) 8) (.reference (.address right) :: rest) current =
      .ok (current, .scalar (.i64 b) :: rest))
    (fL2 : ∀ rest, instruction (.fieldAt (8 * i) 8) (.reference (.address left) :: rest) m2 =
      .ok (m2, .scalar (.i64 a) :: rest))
    (sStored : ∀ pc args rest, step body (.setLocal (16 + 2 * i)) pc args frame (.scalar (.i64 (a + b)) :: rest) current =
      .ok (.next (pc + 1) rest frame m1))
    (rStored : ∀ pc args rest, step body (.setLocal (17 + 2 * i)) pc args frame (.scalar (.i64 (a + b + c)) :: rest) m1 =
      .ok (.next (pc + 1) rest frame m2))
    (cStored : ∀ pc args rest, step body (.setLocal 15) pc args frame (.scalar (.i64 (carryWord a b c)) :: rest) m2 =
      .ok (.next (pc + 1) rest frame m3))
    (loadS1 : ∀ pc stack, step body (.local (16 + 2 * i)) pc args frame stack m1 =
      .ok (.next (pc + 1) (.scalar (.i64 (a + b)) :: stack) frame m1))
    (loadC1 : ∀ pc stack, step body (.local 15) pc args frame stack m1 =
      .ok (.next (pc + 1) (.scalar (.i64 c) :: stack) frame m1))
    (loadS2 : ∀ pc stack, step body (.local (16 + 2 * i)) pc args frame stack m2 =
      .ok (.next (pc + 1) (.scalar (.i64 (a + b)) :: stack) frame m2))
    (loadR2 : ∀ pc stack, step body (.local (17 + 2 * i)) pc args frame stack m2 =
      .ok (.next (pc + 1) (.scalar (.i64 (a + b + c)) :: stack) frame m2))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel method (base + 21) args frame [] m3 = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method base args frame [] current = .ok (final, returned) ∧ post final returned := by
  have carryForm : carryWord a b c =
      (if a + b < a then 1#64 else 0#64) + (if a + b + c < a + b then 1#64 else 0#64) := by
    simp only [carryWord]; split <;> split <;> rfl
  rw [carryForm] at cStored
  repeat' (normalize_pc; first
    | exact continuation
    | (apply run_next_exists post found (by fetch_segment)
       first
       | exact sStored _ _ _
       | exact rStored _ _ _
       | exact cStored _ _ _
       | exact loadS1 _ _
       | exact loadC1 _ _
       | exact loadS2 _ _
       | exact loadR2 _ _
       | (simp (config := { implicitDefEqProofs := false })
           [step, leftArg, rightArg, checkedValue, formValue, numericValue, formedL0, formedR0, formedL2,
             fL0, fR0, fL2, pureArity, scalars, CIL.step.eq_def, CIL.binary, CIL.unary,
             checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))))

#print axioms inline_limb_run
end UInt256Proof.Add.SSEShapes

namespace UInt256Proof.Add.SSEShapes
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety UInt256Proof.Add.CarrySafety UInt256Proof.Safety

/-- Each inlined limb sits after the carry reset and the earlier limbs. -/
theorem inline_limb_code (body : CIL.Method) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (storage : Nat) (code : body.code = leading ++ inlineRepairCode storage ++ tail) (index : Fin 4) :
    ∃ before after, body.code = before ++ inlineLimb index.val ++ after ∧
      before.length = base + (3 + 21 * index.val) := by
  obtain ⟨index, bound⟩ := index
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
  rw [code]
  rcases cases with rfl | rfl | rfl | rfl
  · exact ⟨leading ++ [.const32 0, .convI8, .setLocal 15],
        inlineLimb 1 ++ inlineLimb 2 ++ inlineLimb 3 ++ inlineTail storage ++ tail,
        by simp [inlineRepairCode], by simp [leadingLength]⟩
  · exact ⟨leading ++ [.const32 0, .convI8, .setLocal 15] ++ inlineLimb 0,
        inlineLimb 2 ++ inlineLimb 3 ++ inlineTail storage ++ tail,
        by simp [inlineRepairCode], by simp [leadingLength, inlineLimb]⟩
  · exact ⟨leading ++ [.const32 0, .convI8, .setLocal 15] ++ inlineLimb 0 ++ inlineLimb 1,
        inlineLimb 3 ++ inlineTail storage ++ tail,
        by simp [inlineRepairCode], by simp [leadingLength, inlineLimb]⟩
  · exact ⟨leading ++ [.const32 0, .convI8, .setLocal 15] ++ inlineLimb 0 ++ inlineLimb 1 ++ inlineLimb 2,
        inlineTail storage ++ tail, by simp [inlineRepairCode], by simp [leadingLength, inlineLimb]⟩

/-- A private word local loads the word last written to its home. -/
theorem word_local_step (body : CIL.Method) (args : List Value) (frame : Frame) (memory : Memory)
    (index : Nat) (home : Reference) (word : BitVec 64)
    (slot : frame.locals[index]? = some (.bytes .word64 home))
    (loaded : read memory home 8 1 = .ok (numberBytes word.toNat 8)) :
    ∀ pc stack, step body (.local index) pc args frame stack memory =
      .ok (.next (pc + 1) (.scalar (.i64 word) :: stack) frame memory) := by
  intro pc stack
  have reading := load_local_word64_of_read loaded
  simp (config := { implicitDefEqProofs := false })
    [step, slot, reading, checkedValue, numericValue, pureArity, scalars,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  try first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩

/-- An operand limb read after private writes still yields the caller's original limb. -/
theorem inline_field (program : CIL.Program) (original current : Memory) (left right output : Reference)
    (call : CallingConditions program original [left, right] [output])
    (currentCall : CallingConditions program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (reference : Reference) (member : reference ∈ [left, right]) (index : Fin 4) :
    ∀ rest, instruction (.fieldAt (8 * index.val) 8) (.reference (.address reference) :: rest) current =
      .ok (current, .scalar (.i64 (inputLimb original reference index)) :: rest) := by
  intro rest
  rw [currentCall.input_field_instruction member index rest]
  simp only [inputLimb, call.input_bytes_of_memory_below preserved member]

/-- One inlined limb advances the carry word and completes one sum word. -/
theorem inline_limb (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (storage : Nat) (code : body.code = leading ++ inlineRepairCode storage ++ tail)
    (wordSpecs : ∀ k : Fin 9, specs[14 + k.val]? = some armWordSpec)
    (original entered current : Memory) (frame : Frame) (slots : List LocalSlot)
    (left right output : Reference) (args : List Value)
    (layout : frame.locals = .root (some (.address right)) :: slots)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (call : CallingConditions program original [left, right] [output])
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered original.nextIdentity specs slots)
    (index : Fin 4)
    (state : InlineState program original entered current slots left right output index.val)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, InlineState program original entered after slots left right output (index.val + 1) →
      ∃ fuel final returned,
        run program fuel method (base + (3 + 21 * (index.val + 1))) args frame [] after = .ok (final, returned) ∧
          post final returned) :
    ∃ fuel final returned,
      run program fuel method (base + (3 + 21 * index.val)) args frame [] current = .ok (final, returned) ∧
        post final returned := by
  obtain ⟨before, after, limbCode, beforeLength⟩ := inline_limb_code body leading tail base leadingLength storage code index
  obtain ⟨carryHome, carrySlot, carryRead⟩ := state.carry
  have specS : specs[15 + 2 * index.val]? = some armWordSpec := by
    have h : specs[14 + (1 + 2 * index.val)]? = some armWordSpec := wordSpecs ⟨_, by omega⟩
    rwa [show 14 + (1 + 2 * index.val) = 15 + 2 * index.val by omega] at h
  have specR : specs[16 + 2 * index.val]? = some armWordSpec := by
    have h : specs[14 + (2 + 2 * index.val)]? = some armWordSpec := wordSpecs ⟨_, by omega⟩
    rwa [show 14 + (2 + 2 * index.val) = 16 + 2 * index.val by omega] at h
  have specC : specs[14]? = some armWordSpec := wordSpecs 0
  have carryLocal : frame.locals[15]? = some (.bytes .word64 carryHome) := by simp [layout, carrySlot]
  obtain ⟨sHome, m1, sSlot, sRead, sRetained, m1Call, m1Authority, sWritten, sStored⟩ :=
    vector128_local_store program body specs original.nextIdentity entered current [left, right] [output] frame
      (.root (some (.address right))) slots layout state.call enteredWF homes state.authority
      (15 + 2 * index.val) armWordSpec specS
      (.i64 (inputLimb original left index + inputLimb original right index))
      (inputLimb original left index + inputLimb original right index).toNat rfl
  have sSlots : slots[15 + 2 * index.val]? = some (.bytes .word64 sHome) := by simpa [layout, armWordSpec] using sSlot
  have sLocal : frame.locals[16 + 2 * index.val]? = some (.bytes .word64 sHome) := by
    rw [show 16 + 2 * index.val = 15 + 2 * index.val + 1 by omega]; exact sSlot
  have carryRead1 := word_other_read specs entered current m1 original.nextIdentity slots homes 14 (15 + 2 * index.val)
    (by omega) carryHome sHome carrySlot sSlots _ _ sWritten carryRead
  obtain ⟨rHome, m2, rSlot, rRead, rRetained, m2Call, m2Authority, rWritten, rStored⟩ :=
    vector128_local_store program body specs original.nextIdentity entered m1 [left, right] [output] frame
      (.root (some (.address right))) slots layout m1Call enteredWF homes m1Authority
      (16 + 2 * index.val) armWordSpec specR
      (.i64 (inputLimb original left index + inputLimb original right index +
        scalarCarryValue original left right index.val))
      (inputLimb original left index + inputLimb original right index +
        scalarCarryValue original left right index.val).toNat rfl
  have rSlots : slots[16 + 2 * index.val]? = some (.bytes .word64 rHome) := by simpa [layout, armWordSpec] using rSlot
  have rLocal : frame.locals[17 + 2 * index.val]? = some (.bytes .word64 rHome) := by
    rw [show 17 + 2 * index.val = 16 + 2 * index.val + 1 by omega]; exact rSlot
  have sRead2 := word_other_read specs entered m1 m2 original.nextIdentity slots homes (15 + 2 * index.val)
    (16 + 2 * index.val) (by omega) sHome rHome sSlots rSlots _ _ rWritten sRead
  obtain ⟨cHome, m3, cSlot, cRead, cRetained, m3Call, m3Authority, cWritten, cStored⟩ :=
    vector128_local_store program body specs original.nextIdentity entered m2 [left, right] [output] frame
      (.root (some (.address right))) slots layout m2Call enteredWF homes m2Authority 14 armWordSpec specC
      (.i64 (carryWord (inputLimb original left index) (inputLimb original right index)
        (scalarCarryValue original left right index.val)))
      (carryWord (inputLimb original left index) (inputLimb original right index)
        (scalarCarryValue original left right index.val)).toNat rfl
  have sameHome : cHome = carryHome := by
    have h := cSlot
    rw [show (14 : Nat) + 1 = 15 from rfl, carryLocal] at h
    simp [armWordSpec] at h
    exact h.symm
  subst sameHome
  have rRead3 := word_other_read specs entered m2 m3 original.nextIdentity slots homes (16 + 2 * index.val) 14
    (by omega) rHome cHome rSlots carrySlot _ _ cWritten rRead
  have toMiddle := state.preserved.trans sRetained
  have toEnd := toMiddle.trans rRetained
  have stepped := inline_limb_run program body method found before after (base + (3 + 21 * index.val)) beforeLength
    index.val limbCode args frame left right leftArg rightArg
    (inputLimb original left index) (inputLimb original right index) (scalarCarryValue original left right index.val)
    current m1 m2 m3 (state.call.input_formed (by simp)) (state.call.input_formed (by simp))
    (m2Call.input_formed (by simp))
    (inline_field program original current left right output call state.call state.preserved left (by simp) index)
    (inline_field program original current left right output call state.call state.preserved right (by simp) index)
    (inline_field program original m2 left right output call m2Call toEnd left (by simp) index)
    (fun pc args rest => by rw [show 16 + 2 * index.val = 15 + 2 * index.val + 1 by omega]; exact sStored pc args rest)
    (fun pc args rest => by rw [show 17 + 2 * index.val = 16 + 2 * index.val + 1 by omega]; exact rStored pc args rest)
    (fun pc args rest => cStored pc args rest)
    (word_local_step body args frame m1 _ sHome _ sLocal sRead)
    (word_local_step body args frame m1 _ cHome _ carryLocal carryRead1)
    (word_local_step body args frame m2 _ sHome _ sLocal sRead2)
    (word_local_step body args frame m2 _ rHome _ rLocal rRead) post
  rw [show base + (3 + 21 * index.val) + 21 = base + (3 + 21 * (index.val + 1)) by omega] at stepped
  apply stepped
  have carryNext : scalarCarryValue original left right (index.val + 1) =
      carryWord (inputLimb original left index) (inputLimb original right index)
        (scalarCarryValue original left right index.val) := by
    rw [carryWord_correct _ _ _ state.carryBound]
    simp [scalarCarryValue, index.isLt]
  apply continuation m3
  refine ⟨m3Call, toEnd.trans cRetained, m3Authority, ⟨cHome, carrySlot, by rw [carryNext]; exact cRead⟩,
    by rw [carryNext, carryWord_correct _ _ _ state.carryBound]; exact UInt256Proof.carry_bound _ _ _ state.carryBound, ?_⟩
  intro j bound
  by_cases same : j.val = index.val
  · have equal : j = index := Fin.ext same
    subst equal
    exact ⟨rHome, rSlots, rRead3⟩
  · obtain ⟨home, slot, loaded⟩ := state.completed j (by omega)
    have r1 := word_other_read specs entered current m1 original.nextIdentity slots homes (16 + 2 * j.val)
      (15 + 2 * index.val) (by omega) home sHome slot sSlots _ _ sWritten loaded
    have r2 := word_other_read specs entered m1 m2 original.nextIdentity slots homes (16 + 2 * j.val)
      (16 + 2 * index.val) (by omega) home rHome slot rSlots _ _ rWritten r1
    exact ⟨home, slot, word_other_read specs entered m2 m3 original.nextIdentity slots homes (16 + 2 * j.val) 14
      (by omega) home cHome slot carrySlot _ _ cWritten r2⟩

#print axioms inline_limb
#print axioms inline_limb_code
#print axioms word_local_step
#print axioms inline_field
end UInt256Proof.Add.SSEShapes

namespace UInt256Proof.Add.SSEShapes
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety UInt256Proof.Add.CarrySafety UInt256Proof.Safety

/-- Push the output reference and the four sum words for the storage call. -/
theorem inline_store_prefix (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (storage : Nat) (code : body.code = leading ++ inlineRepairCode storage ++ tail)
    (output : Reference) (args : List Value)
    (outputArg : args[2]? = some (.reference (.address output)))
    (frame : Frame) (memory : Memory) (results : Fin 4 → Reference) (words : Fin 4 → BitVec 64)
    (outputFormed : form memory output = .ok output)
    (slots : ∀ i : Fin 4, frame.locals[17 + 2 * i.val]? = some (.bytes .word64 (results i)))
    (reads : ∀ i, read memory (results i) 8 1 = .ok (numberBytes (words i).toNat 8))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method (base + 92) args frame (repairStack false output words) memory =
        .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (base + 87) args frame [] memory = .ok (result, returned) ∧ post result returned := by
  have s0 := slots 0
  have s1 := slots 1
  have s2 := slots 2
  have s3 := slots 3
  dsimp at s0 s1 s2 s3
  simp only [CIL.fin_val_three, Nat.reduceAdd, Nat.reduceMul] at s0 s1 s2 s3
  have r0 := load_local_word64_of_read (reads 0)
  have r1 := load_local_word64_of_read (reads 1)
  have r2 := load_local_word64_of_read (reads 2)
  have r3 := load_local_word64_of_read (reads 3)
  simp only [repairStack, Bool.cond_false] at continuation
  repeat' first
    | exact continuation
    | (normalize_pc
       apply run_next_exists post found (by fetch_segment)
       simp (config := { implicitDefEqProofs := false })
         [step, checkedValue, formValue, outputArg, outputFormed, s0, s1, s2, s3, r0, r1, r2, r3,
           checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

/-- Return the carry word as the unsigned overflow flag and retire the frame. -/
theorem inline_return (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (storage : Nat) (code : body.code = leading ++ inlineRepairCode storage ++ tail)
    (returns : body.returnsValue = true)
    (args : List Value) (frame : Frame) (memory : Memory)
    (carryHome : Reference) (carryWord : BitVec 64)
    (slot : frame.locals[15]? = some (.bytes .word64 carryHome))
    (loaded : read memory carryHome 8 1 = .ok (numberBytes carryWord.toNat 8)) :
    run program 5 method (base + 93) args frame [] memory =
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
  have fetched : body.code[base + 97]? = some (.ret (some .unsigned8)) := code_at code leadingLength rfl
  by_cases positive : BitVec.ofNat 64 0 < carryWord
  all_goals simp [run, found, fetched, returns, step, checkedValue, numericValue, CIL.NarrowKind.extend,
    scalarOverflowFlag, positive, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Store the four inlined sum words through the limb helper and return the exact carry. -/
theorem inline_finish (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (storage : Nat) (code : body.code = leading ++ inlineRepairCode storage ++ tail)
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body body.profile))
    (returns : body.returnsValue = true)
    (original entered current : Memory) (frame : Frame) (slots : List LocalSlot)
    (left right output : Reference) (args : List Value)
    (layout : frame.locals = .root (some (.address right)) :: slots)
    (outputArg : args[2]? = some (.reference (.address output)))
    (call : CallingConditions program original [left, right] [output])
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (wordSpecs : ∀ k : Fin 9, specs[14 + k.val]? = some armWordSpec)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered original.nextIdentity specs slots)
    (state : InlineState program original entered current slots left right output 4) :
    ∃ fuel final values,
      run program fuel method (base + 87) args frame [] current = .ok (final, values) ∧
      AddResult original final values left right output := by
  let words := scalarSumWord original left right
  let post := fun final values => AddResult original final values left right output
  have formed := state.call.output_formed (by simp : output ∈ [output])
  have homeOf : ∀ i : Fin 4, ∃ home, slots[16 + 2 * i.val]? = some (.bytes .word64 home) ∧
      read current home 8 1 = .ok (numberBytes (words i).toNat 8) := fun i => state.completed i i.isLt
  let results : Fin 4 → Reference := fun i => (homeOf i).choose
  have resultSlots : ∀ i : Fin 4, frame.locals[17 + 2 * i.val]? = some (.bytes .word64 (results i)) := by
    intro i
    have h := (homeOf i).choose_spec.1
    rw [layout, show 17 + 2 * i.val = (16 + 2 * i.val) + 1 by omega]
    simpa using h
  apply inline_store_prefix program body method found leading tail base leadingLength storage code
    output args outputArg frame current results words formed resultSlots (fun i => (homeOf i).choose_spec.2) post
  obtain ⟨carryHome, carrySlot, carryLoaded⟩ := state.carry
  have carryLocal : frame.locals[15]? = some (.bytes .word64 carryHome) := by simp [layout, carrySlot]
  obtain ⟨childFuel, stored, invoked, valid, outside, authority, value, _⟩ :=
    UInt256Proof.Multiply.LimbStorage.store_limbs_readable_contract body.profile program storage storageFound
      current [left, right] output (words 0) (words 1) (words 2) (words 3) state.call
  have stepped : step body (.call storage 5) (base + 92) args frame (repairStack false output words) current =
      .ok (.call storage (UInt256Proof.Multiply.LimbStorage.arguments output (words 0) (words 1) (words 2) (words 3))
        [] current) := by
    simp [step, repairStack, UInt256Proof.Multiply.LimbStorage.arguments, checkedValue, numericValue,
      formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨outputAllocation, outputPresent, _, _⟩ := formed_reference_live _ _ _
    (call.output_formed (by simp : output ∈ [output]))
  have outputOld := (call.1.1.1 _ _ outputPresent).1
  have carryFresh := homes.home_bound 14 .word64 carryHome carrySlot
  obtain ⟨home14, slot14, _, _, carryWritable⟩ := homes.home_at 14 armWordSpec (wordSpecs 0)
  obtain ⟨carryAllocation, carryEntered, _, _⟩ := access_within_allocation _ _ _ _ _ carryWritable
  have carryHomeEq : carryHome = home14 := by
    rw [carrySlot] at slot14
    simp [armWordSpec] at slot14
    exact slot14
  have enteredOld := (enteredWF.1 _ _ carryEntered).1
  have carryPresent : current.allocations carryHome.allocation = some carryAllocation := by
    rw [carryHomeEq, state.authority.allocations _ enteredOld]; exact carryEntered
  have carryOld := (state.call.1.1.1 _ _ carryPresent).1
  have distinct : carryHome.allocation ≠ output.allocation :=
    Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le outputOld carryFresh))
  have carryRead := authority.read_eq carryLoaded carryOld (fun i _ => outside _ _ (Or.inl distinct))
  have returned := inline_return program body method found leading tail base leadingLength storage code returns
    args frame stored carryHome _ carryLocal carryRead
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
    exact (retained.cells id old offset).trans ((outside id offset untouched).trans (state.preserved.cells id old offset))

#print axioms inline_store_prefix
#print axioms inline_return
#print axioms inline_finish
end UInt256Proof.Add.SSEShapes

namespace UInt256Proof.Add.SSEShapes
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety UInt256Proof.Add.CarrySafety UInt256Proof.Safety

/-- The repair with the carry helper inlined satisfies the repair contract. -/
theorem inline_repair (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (repair storage : Nat)
    (placed : At body.code repair (inlineRepairCode storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body body.profile))
    (wordSpecs : ∀ k : Fin 9, specs[14 + k.val]? = some armWordSpec)
    (returns : body.returnsValue = true) :
    RepairContract program method specs repair := by
  intro original entered current frame slots left right output args layout call currentCall preserved homes
    enteredWF authority leftArg rightArg outputArg owned
  obtain ⟨leading, tail, leadingLength, code⟩ := placed
  let post := fun final values => AddResult original final values left right output
  apply inline_start program body method specs found leading tail repair leadingLength storage code (wordSpecs 0)
    original entered current frame slots left right output args layout currentCall preserved enteredWF homes authority post
  intro m0 s0
  apply inline_limb program body method specs found leading tail repair leadingLength storage code wordSpecs
    original entered m0 frame slots left right output args layout leftArg rightArg call enteredWF homes 0 s0 post
  intro m1 s1
  apply inline_limb program body method specs found leading tail repair leadingLength storage code wordSpecs
    original entered m1 frame slots left right output args layout leftArg rightArg call enteredWF homes 1 s1 post
  intro m2 s2
  apply inline_limb program body method specs found leading tail repair leadingLength storage code wordSpecs
    original entered m2 frame slots left right output args layout leftArg rightArg call enteredWF homes 2 s2 post
  intro m3 s3
  apply inline_limb program body method specs found leading tail repair leadingLength storage code wordSpecs
    original entered m3 frame slots left right output args layout leftArg rightArg call enteredWF homes 3 s3 post
  intro m4 s4
  exact inline_finish program body method specs found leading tail repair leadingLength storage code storageFound returns
    original entered m4 frame slots left right output args layout outputArg call owned wordSpecs enteredWF homes s4

#print axioms inline_repair
end UInt256Proof.Add.SSEShapes
