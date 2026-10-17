import UInt256.Methods.Add.SSEShapes.Relocated

namespace UInt256Proof.Add.SSEShapes
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety CIL.Vector

/-- The SSE incoming-carry block: shift the low mask, align the high mask. -/
def sseIncomingCode : List CIL.Op := [
  .local 6, .const32 8, .intrinsic (.sse .shiftLeftBytes) 2, .setLocal 8,
  .local 7, .intrinsic (.vector (.reinterpret 128)) 1, .local 6, .intrinsic (.vector (.reinterpret 128)) 1,
  .const32 8, .intrinsic (.sse .alignBytes) 3, .intrinsic (.vector (.reinterpret 128)) 1, .setLocal 9]

/-- Follow the SSE incoming-mask instructions and initialize its private slot. -/
theorem incoming_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (tail : List CIL.Op)
    (leading : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (code : body.code = leading ++ sseIncomingCode ++ tail)
    (sse2 : body.profile.sse2 = true) (ssse3 : body.profile.ssse3 = true)
    (slotsSpec : specs[7]? = some vector128ZeroSpec ∧ specs[8]? = some vector128ZeroSpec) (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (upper : Bool) (low high : BitVec 128) (stack : List Value) (lowHome highHome : Reference)
    (lowSlot : frame.locals[6]? = some (.bytes .vector128 lowHome))
    (highSlot : frame.locals[7]? = some (.bytes .vector128 highHome))
    (lowRead : read current lowHome 16 1 = .ok (numberBytes low.toNat 16))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[(if upper then 9 else 8)]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok
        (numberBytes (if upper then incoming128High low high else incoming128Low low).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference
        (numberBytes (if upper then incoming128High low high else incoming128Low low).toNat 16) 1 = .ok after →
      ∃ fuel result returned,
        run program fuel method (if upper then base + 12 else base + 4) args frame
          stack after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (if upper then base + 4 else base) args frame
        stack current = .ok (result, returned) ∧ post result returned := by
  have specified : specs[(if upper then 8 else 7)]? = some vector128ZeroSpec := by
    cases upper <;> exact (by first | exact slotsSpec.1 | exact slotsSpec.2)
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store program body specs boundary entered current inputs outputs frame root slots layout currentCall
      enteredWF homes authority _ vector128ZeroSpec specified
      (.v128 (if upper then incoming128High low high else incoming128Low low))
      (if upper then incoming128High low high else incoming128Low low).toNat rfl
  have actual : frame.locals[(if upper then 9 else 8)]? = some (.bytes .vector128 reference) := by
    cases upper <;> exact slot
  have done := continuation reference after actual loaded retained afterCall afterAuthority written
  have loadLow := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 low) low.toNat rfl lowSlot lowRead
  have loadHigh := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 high) high.toNat rfl highSlot highRead
  have finished : ∃ fuel result returned,
      run program fuel method (if upper then base + 11 else base + 3) args frame
        (.scalar (.v128 (if upper then incoming128High low high else incoming128Low low)) :: stack)
        current = .ok (result, returned) ∧ post result returned := by
    cases upper <;> simp only [Bool.false_eq_true, ite_false, ite_true] at done ⊢
    all_goals
      apply run_next_exists post found (by fetch_segment)
      · exact stored _ _ _
      · simpa only [Nat.add_assoc, Nat.reduceAdd] using done
  have finishedMath := finished
  rw [← incomingRaw_eq false upper low high] at finished
  cases upper <;> simp only [Bool.false_eq_true, ite_false, ite_true] at stored finished finishedMath ⊢
  all_goals
    simp only [Nat.reduceAdd] at stored
    simp only [incomingRaw, Bool.false_eq_true, ite_false, ite_true] at finished finishedMath ⊢
    repeat' first
      | exact finished
      | with_reducible exact finishedMath
      | (normalize_pc
         apply run_next_exists post found (by fetch_segment)
         first
         | exact loadLow _ _
         | exact loadHigh _ _
         | (simp (config := { implicitDefEqProofs := false })
             [show (BitVec.setWidth 8 (8 : BitVec 32)).toNat = 8 from rfl, step, sse2, ssse3, pureArity, scalars, CIL.step.eq_def, CIL.Intrinsic.available,
               CIL.Vector.intrinsic_zero128, CIL.Vector.intrinsic_sse_shift, CIL.Vector.intrinsic_sse_align,
               CIL.Vector.intrinsic_reinterpret128,
               incoming128_sse_low, incoming128_sse_high, checkedValue, numericValue,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms incoming_checked

/-- Both SSE incoming-mask blocks preserve every earlier initialized vector home, including the initial operands, upper sum and generated masks. -/
theorem incoming_pair (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (tail : List CIL.Op)
    (leading : List CIL.Op) (base : Nat) (leadingLength : leading.length = base)
    (code : body.code = leading ++ sseIncomingCode ++ tail)
    (sse2 : body.profile.sse2 = true) (ssse3 : body.profile.ssse3 = true)
    (slotsSpec : specs[7]? = some vector128ZeroSpec ∧ specs[8]? = some vector128ZeroSpec) (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (low high : BitVec 128) (stack : List Value) (lowHome highHome : Reference)
    (lowSlot : slots[5]? = some (.bytes .vector128 lowHome))
    (highSlot : slots[6]? = some (.bytes .vector128 highHome))
    (lowRead : read current lowHome 16 1 = .ok (numberBytes low.toNat 16))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ lowIncoming highIncoming after,
      slots[7]? = some (.bytes .vector128 lowIncoming) →
      slots[8]? = some (.bytes .vector128 highIncoming) →
      read after lowIncoming 16 1 = .ok (numberBytes (incoming128Low low).toNat 16) →
      read after highIncoming 16 1 = .ok (numberBytes (incoming128High low high).toNat 16) →
      (∀ i, i < 7 → ∀ reference bytes,
        slots[i]? = some (.bytes .vector128 reference) →
        read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run program fuel method (base + 12) args frame stack after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method base args frame stack current =
        .ok (result, returned) ∧ post result returned := by
  have actualLow : frame.locals[6]? = some (.bytes .vector128 lowHome) := by
    simpa [layout, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lowSlot
  have actualHigh : frame.locals[7]? = some (.bytes .vector128 highHome) := by
    simpa [layout, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using highSlot
  apply incoming_checked program body method specs found tail leading base leadingLength code sse2 ssse3 slotsSpec boundary entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority false low high stack lowHome highHome actualLow actualHigh lowRead highRead post
  intro lowIncoming middle lowLocal lowLoaded preserved middleCall middleAuthority firstWrite
  have lowTail : slots[7]? = some (.bytes .vector128 lowIncoming) := by simpa [layout, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lowLocal
  have savedLow := vector128_prior_read specs entered current middle boundary slots homes (5) (7) (by omega)
    lowHome lowIncoming lowSlot lowTail _ _ firstWrite lowRead
  have savedHigh := vector128_prior_read specs entered current middle boundary slots homes (6) (7) (by omega)
    highHome lowIncoming highSlot lowTail _ _ firstWrite highRead
  apply incoming_checked program body method specs found tail leading base leadingLength code sse2 ssse3 slotsSpec boundary entered middle inputs outputs frame root slots layout args
    middleCall enteredWF homes middleAuthority true low high stack lowHome highHome actualLow actualHigh savedLow savedHigh post
  intro highIncoming after highLocal highLoaded kept afterCall afterAuthority secondWrite
  have highTail : slots[8]? = some (.bytes .vector128 highIncoming) := by simpa [layout, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using highLocal
  have lower := vector128_prior_read specs entered middle after boundary slots homes (7) (8) (by omega)
    lowIncoming highIncoming lowTail highTail _ _ secondWrite lowLoaded
  have earlier : ∀ i, i < 7 → ∀ reference bytes,
      slots[i]? = some (.bytes .vector128 reference) →
      read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes := by
    intro i bound reference bytes slot loaded
    exact vector128_prior_read specs entered middle after boundary slots homes i (8) (by omega)
      reference highIncoming slot highTail _ _ secondWrite
      (vector128_prior_read specs entered current middle boundary slots homes i (7) bound
        reference lowIncoming slot lowTail _ _ firstWrite loaded)
  exact continuation lowIncoming highIncoming after lowTail highTail lower highLoaded earlier
    (preserved.trans kept) afterCall afterAuthority
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ firstWrite).next
      (write_extends_allocations _ _ _ _ _ secondWrite).next)

#print axioms incoming_pair
end UInt256Proof.Add.SSEShapes
