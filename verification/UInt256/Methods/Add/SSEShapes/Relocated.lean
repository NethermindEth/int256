import UInt256.Methods.Add.SSEShapes.Segments

namespace UInt256Proof.Add.SSEShapes
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety CIL.Vector

/-- Apply the incoming all-ones carry mask to either half and initialize its speculative result home using the actual extracted subtraction/store block. -/
theorem correction_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (code : body.code = leading ++ correctionCode ++ tail)
    (slotsSpec : specs[9]? = some vector128ZeroSpec ∧ specs[10]? = some vector128ZeroSpec) (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (upper : Bool) (low high incoming : BitVec 128) (sumHome incomingHome : Reference)
    (sumSlot : frame.locals[5]? = some (.bytes .vector128 sumHome))
    (incomingSlot : frame.locals[if upper then 9 else 8]? = some (.bytes .vector128 incomingHome))
    (sumRead : read current sumHome 16 1 = .ok (numberBytes high.toNat 16))
    (incomingRead : read current incomingHome 16 1 = .ok (numberBytes incoming.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[if upper then 11 else 10]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok (numberBytes (corrected128 (if upper then high else low) incoming).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (corrected128 (if upper then high else low) incoming).toNat 16) 1 = .ok after →
      ∃ fuel result returned,
        run program fuel method (if upper then base + 7 else base + 3) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (if upper then base + 3 else base) args frame
        (if upper then [] else [.scalar (.v128 low)]) current = .ok (result, returned) ∧ post result returned := by
  have specified : specs[if upper then 10 else 9]? = some vector128ZeroSpec := by
    cases upper <;> exact (by first | exact slotsSpec.1 | exact slotsSpec.2)
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store program body specs boundary entered current inputs outputs frame root slots layout currentCall
      enteredWF homes authority _ vector128ZeroSpec specified
      (.v128 (corrected128 (if upper then high else low) incoming))
      (corrected128 (if upper then high else low) incoming).toNat rfl
  have actual : frame.locals[if upper then 11 else 10]? = some (.bytes .vector128 reference) := by
    cases upper <;> exact slot
  have done := continuation reference after actual loaded retained afterCall afterAuthority written
  have loadIncoming := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 incoming) incoming.toNat rfl incomingSlot incomingRead
  have loadSum := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 high) high.toNat rfl sumSlot sumRead
  cases upper <;> simp only [Bool.false_eq_true, ite_false, ite_true] at stored loadIncoming done ⊢
  all_goals
    repeat' first
      | exact done
      | (normalize_pc
         apply run_next_exists post found (by fetch_segment)
         first
         | exact loadIncoming _ _
         | exact loadSum _ _
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, pureArity, scalars, CIL.step.eq_def, CIL.Intrinsic.available,
               CIL.Vector.intrinsic_sub128, corrected128, checkedValue, numericValue,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms correction_checked

/-- Both speculative result stores retain the earlier operand, sum and mask snapshots. -/
theorem correction_pair (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (code : body.code = leading ++ correctionCode ++ tail)
    (slotsSpec : specs[9]? = some vector128ZeroSpec ∧ specs[10]? = some vector128ZeroSpec) (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (low high incomingLow incomingHigh : BitVec 128) (sumHome lowHome highHome : Reference)
    (sumSlot : slots[4]? = some (.bytes .vector128 sumHome))
    (lowSlot : slots[7]? = some (.bytes .vector128 lowHome))
    (highSlot : slots[8]? = some (.bytes .vector128 highHome))
    (sumRead : read current sumHome 16 1 = .ok (numberBytes high.toNat 16))
    (lowRead : read current lowHome 16 1 = .ok (numberBytes incomingLow.toNat 16))
    (highRead : read current highHome 16 1 = .ok (numberBytes incomingHigh.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ lowResult highResult after,
      slots[9]? = some (.bytes .vector128 lowResult) →
      slots[10]? = some (.bytes .vector128 highResult) →
      read after lowResult 16 1 = .ok (numberBytes (corrected128 low incomingLow).toNat 16) →
      read after highResult 16 1 = .ok (numberBytes (corrected128 high incomingHigh).toNat 16) →
      (∀ i, i < 9 → ∀ reference bytes,
        slots[i]? = some (.bytes .vector128 reference) →
        read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run program fuel method (base + 7) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method base args frame [.scalar (.v128 low)] current =
        .ok (result, returned) ∧ post result returned := by
  have actualSum : frame.locals[5]? = some (.bytes .vector128 sumHome) := by
    simpa [layout] using sumSlot
  have actualLow : frame.locals[8]? = some (.bytes .vector128 lowHome) := by
    simpa [layout] using lowSlot
  have actualHigh : frame.locals[9]? = some (.bytes .vector128 highHome) := by
    simpa [layout] using highSlot
  apply correction_checked program body method specs found leading tail base leadingLength code slotsSpec boundary entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority false low high incomingLow sumHome lowHome actualSum actualLow sumRead lowRead post
  intro lowResult middle lowLocal lowLoaded preserved middleCall middleAuthority firstWrite
  have lowTail : slots[9]? = some (.bytes .vector128 lowResult) := by simpa [layout] using lowLocal
  have savedSum := vector128_prior_read specs entered current middle boundary slots homes 4 9 (by decide)
    sumHome lowResult sumSlot lowTail _ _ firstWrite sumRead
  have savedHigh := vector128_prior_read specs entered current middle boundary slots homes 8 9 (by decide)
    highHome lowResult highSlot lowTail _ _ firstWrite highRead
  apply correction_checked program body method specs found leading tail base leadingLength code slotsSpec boundary entered middle inputs outputs frame root slots layout args
    middleCall enteredWF homes middleAuthority true low high incomingHigh sumHome highHome actualSum actualHigh savedSum savedHigh post
  intro highResult after highLocal highLoaded kept afterCall afterAuthority secondWrite
  have highTail : slots[10]? = some (.bytes .vector128 highResult) := by simpa [layout] using highLocal
  have lower := vector128_prior_read specs entered middle after boundary slots homes 9 10 (by decide)
    lowResult highResult lowTail highTail _ _ secondWrite lowLoaded
  have earlier : ∀ i, i < 9 → ∀ reference bytes,
      slots[i]? = some (.bytes .vector128 reference) →
      read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes := by
    intro i bound reference bytes slot loaded
    exact vector128_prior_read specs entered middle after boundary slots homes i 10 (by omega)
      reference highResult slot highTail _ _ secondWrite
      (vector128_prior_read specs entered current middle boundary slots homes i 9 bound
        reference lowResult slot lowTail _ _ firstWrite loaded)
  exact continuation lowResult highResult after lowTail highTail lower highLoaded earlier
    (preserved.trans kept) afterCall afterAuthority
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ firstWrite).next
      (write_extends_allocations _ _ _ _ _ secondWrite).next)

#print axioms correction_pair

/-- Detect a carry that propagated through a corrected zero lane, using saved initialized vectors after any overlapping early output write. -/
theorem propagation_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (code : body.code = leading ++ propagationCode ++ tail)
    (slotsSpec : specs[11]? = some vector128ZeroSpec ∧ specs[12]? = some vector128ZeroSpec) (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (upper : Bool) (result incoming : BitVec 128) (resultHome incomingHome : Reference)
    (resultSlot : frame.locals[if upper then 11 else 10]? = some (.bytes .vector128 resultHome))
    (incomingSlot : frame.locals[if upper then 9 else 8]? = some (.bytes .vector128 incomingHome))
    (resultRead : read current resultHome 16 1 = .ok (numberBytes result.toNat 16))
    (incomingRead : read current incomingHome 16 1 = .ok (numberBytes incoming.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[if upper then 13 else 12]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok (numberBytes (propagating128 result incoming).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (propagating128 result incoming).toNat 16) 1 = .ok after →
      ∃ fuel final returned,
        run program fuel method (if upper then base + 12 else base + 6) args frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method (if upper then base + 6 else base) args frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have specified : specs[if upper then 12 else 11]? = some vector128ZeroSpec := by
    cases upper <;> exact (by first | exact slotsSpec.1 | exact slotsSpec.2)
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store program body specs boundary entered current inputs outputs frame root slots layout currentCall
      enteredWF homes authority _ vector128ZeroSpec specified
      (.v128 (propagating128 result incoming)) (propagating128 result incoming).toNat rfl
  have actual : frame.locals[if upper then 13 else 12]? = some (.bytes .vector128 reference) := by
    cases upper <;> exact slot
  have done := continuation reference after actual loaded retained afterCall afterAuthority written
  have loadResult := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 result) result.toNat rfl resultSlot resultRead
  have loadIncoming := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 incoming) incoming.toNat rfl incomingSlot incomingRead
  cases upper <;> simp only [Bool.false_eq_true, ite_false, ite_true] at stored loadResult loadIncoming done ⊢
  all_goals
    repeat' first
      | exact done
      | (normalize_pc
         apply run_next_exists post found (by fetch_segment)
         first
         | exact loadResult _ _
         | exact loadIncoming _ _
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, pureArity, scalars, CIL.step.eq_def, CIL.Intrinsic.available,
               CIL.Vector.intrinsic_zero128, CIL.Vector.intrinsic_eq128, CIL.Vector.intrinsic_and128,
               propagating128, checkedValue, numericValue,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms propagation_checked

/-- Compose both propagation masks while retaining every earlier vector home and all older caller storage, including ARM's early output readbacks. -/
theorem propagation_pair (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (code : body.code = leading ++ propagationCode ++ tail)
    (slotsSpec : specs[11]? = some vector128ZeroSpec ∧ specs[12]? = some vector128ZeroSpec) (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (low high incomingLow incomingHigh : BitVec 128)
    (lowHome highHome lowIncoming highIncoming : Reference)
    (lowSlot : slots[9]? = some (.bytes .vector128 lowHome))
    (highSlot : slots[10]? = some (.bytes .vector128 highHome))
    (lowIncomingSlot : slots[7]? = some (.bytes .vector128 lowIncoming))
    (highIncomingSlot : slots[8]? = some (.bytes .vector128 highIncoming))
    (lowRead : read current lowHome 16 1 = .ok (numberBytes low.toNat 16))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (lowIncomingRead : read current lowIncoming 16 1 = .ok (numberBytes incomingLow.toNat 16))
    (highIncomingRead : read current highIncoming 16 1 = .ok (numberBytes incomingHigh.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ lowMask highMask after,
      slots[11]? = some (.bytes .vector128 lowMask) →
      slots[12]? = some (.bytes .vector128 highMask) →
      read after lowMask 16 1 = .ok (numberBytes (propagating128 low incomingLow).toNat 16) →
      read after highMask 16 1 = .ok (numberBytes (propagating128 high incomingHigh).toNat 16) →
      (∀ i, i < 11 → ∀ reference bytes,
        slots[i]? = some (.bytes .vector128 reference) →
        read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run program fuel method (base + 12) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method base args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  have actualLow : frame.locals[10]? = some (.bytes .vector128 lowHome) := by simpa [layout] using lowSlot
  have actualHigh : frame.locals[11]? = some (.bytes .vector128 highHome) := by simpa [layout] using highSlot
  have actualLowIncoming : frame.locals[8]? = some (.bytes .vector128 lowIncoming) := by simpa [layout] using lowIncomingSlot
  have actualHighIncoming : frame.locals[9]? = some (.bytes .vector128 highIncoming) := by simpa [layout] using highIncomingSlot
  apply propagation_checked program body method specs found leading tail base leadingLength code slotsSpec boundary entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority false low incomingLow lowHome lowIncoming actualLow actualLowIncoming lowRead lowIncomingRead post
  intro lowMask middle lowLocal lowLoaded preserved middleCall middleAuthority firstWrite
  have lowTail : slots[11]? = some (.bytes .vector128 lowMask) := by simpa [layout] using lowLocal
  have savedHigh := vector128_prior_read specs entered current middle boundary slots homes 10 11 (by decide)
    highHome lowMask highSlot lowTail _ _ firstWrite highRead
  have savedIncoming := vector128_prior_read specs entered current middle boundary slots homes 8 11 (by decide)
    highIncoming lowMask highIncomingSlot lowTail _ _ firstWrite highIncomingRead
  apply propagation_checked program body method specs found leading tail base leadingLength code slotsSpec boundary entered middle inputs outputs frame root slots layout args
    middleCall enteredWF homes middleAuthority true high incomingHigh highHome highIncoming actualHigh actualHighIncoming savedHigh savedIncoming post
  intro highMask after highLocal highLoaded kept afterCall afterAuthority secondWrite
  have highTail : slots[12]? = some (.bytes .vector128 highMask) := by simpa [layout] using highLocal
  have lower := vector128_prior_read specs entered middle after boundary slots homes 11 12 (by decide)
    lowMask highMask lowTail highTail _ _ secondWrite lowLoaded
  have earlier : ∀ i, i < 11 → ∀ reference bytes,
      slots[i]? = some (.bytes .vector128 reference) →
      read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes := by
    intro i bound reference bytes slot loaded
    exact vector128_prior_read specs entered middle after boundary slots homes i 12 (by omega)
      reference highMask slot highTail _ _ secondWrite
      (vector128_prior_read specs entered current middle boundary slots homes i 11 bound
        reference lowMask slot lowTail _ _ firstWrite loaded)
  exact continuation lowMask highMask after lowTail highTail lower highLoaded earlier
    (preserved.trans kept) afterCall afterAuthority
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ firstWrite).next
      (write_extends_allocations _ _ _ _ _ secondWrite).next)

#print axioms propagation_pair
end UInt256Proof.Add.SSEShapes
