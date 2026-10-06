import UInt256.Methods.Subtract.VectorSafetyPrepared

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def vectorWordZero : NumericLocalSpec := ⟨.word32, .i32 0, 0, rfl⟩

/-- Convert either saved vector mask to its checked initialized word local. -/
theorem vector_movemask_checked (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary vectorSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (second : Bool) (maskHome : Reference) (mask : BitVec 256)
    (slot : frame.locals[if second then 5 else 3]? = some (.bytes .vector256 maskHome))
    (loaded : read current maskHome 32 1 = .ok (numberBytes mask.toNat 32))
    (post : Memory → List Value → Prop)
    (continuation : ∀ wordHome after,
      frame.locals[if second then 7 else 6]? = some (.bytes .word32 wordHome) →
      read after wordHome 4 1 = .ok (numberBytes (CIL.Vector.moveMask64 mask).toNat 4) →
      MemoryBelow wordHome.allocation current after →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vectorIndex (vectorTestStart + 8 + (if second then 4 else 0))
          args frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex (vectorTestStart + 4 + (if second then 4 else 0))
        args frame [] current = .ok (result, returned) ∧ post result returned := by
  have specified : vectorSpecs[if second then 7 else 6]? = some vectorWordZero := by
    cases second <;> rfl
  obtain ⟨wordHome, after, wordSlot, readback, preserved, afterCall, afterAuthority, written, stored⟩ :=
    vector_local_store boundary entered current inputs outputs frame currentCall enteredWF homes authority
      _ vectorWordZero specified (.i32 (CIL.Vector.moveMask64 mask)) (CIL.Vector.moveMask64 mask).toNat rfl
  have earlier := write_preserves_memory_below _ _ _ _ _ _ (Nat.le_refl wordHome.allocation) written
  have done := continuation wordHome after wordSlot readback earlier preserved afterCall afterAuthority
    (write_extends_allocations _ _ _ _ _ written).next
  have loadMask := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vectorBody) (args := args) (pc := pc) (stack := stack)
    .vector256 (.v256 mask) mask.toNat rfl slot loaded
  have found : Extracted.program[vectorIndex]? = some vectorBody := by rfl
  have profile : vectorBody.profile = Extracted.profile := by rfl
  cases second <;> simp only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero] at loadMask stored done ⊢
  all_goals
    conv at done in vectorTestStart => cbv
    conv in vectorTestStart => cbv
    repeat' first
      | exact done
      | (apply run_next_exists post found (by rfl)
         first
         | exact stored _ _ _
         | exact loadMask _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.Intrinsic.available,
               CIL.Vector.intrinsic_reinterpret256, CIL.Vector.intrinsic_movemask256,
               checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector_movemask_checked

/-- Initialize both scalar masks for cascade-index arithmetic. -/
theorem vector_movemasks_checked (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary vectorSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (generatedHome equalHome : Reference) (generated equal : BitVec 256)
    (generatedSlot : frame.locals[3]? = some (.bytes .vector256 generatedHome))
    (equalSlot : frame.locals[5]? = some (.bytes .vector256 equalHome))
    (generatedRead : read current generatedHome 32 1 = .ok (numberBytes generated.toNat 32))
    (equalRead : read current equalHome 32 1 = .ok (numberBytes equal.toNat 32))
    (post : Memory → List Value → Prop)
    (continuation : ∀ generatedWord equalWord after,
      frame.locals[6]? = some (.bytes .word32 generatedWord) →
      frame.locals[7]? = some (.bytes .word32 equalWord) →
      read after generatedWord 4 1 = .ok (numberBytes (CIL.Vector.moveMask64 generated).toNat 4) →
      read after equalWord 4 1 = .ok (numberBytes (CIL.Vector.moveMask64 equal).toNat 4) →
      MemoryBelow generatedWord.allocation current after →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vectorIndex (vectorTestStart + 12) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vectorIndex (vectorTestStart + 4) args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  apply vector_movemask_checked boundary entered current inputs outputs frame args currentCall
    enteredWF homes authority false generatedHome generated generatedSlot generatedRead post
  intro generatedWord middle generatedWordSlot generatedWordRead firstEarlier firstPreserved middleCall middleAuthority firstNext
  have equalOld := homes.ordered 5 6 .vector256 .word32 equalHome generatedWord
    (by decide) equalSlot generatedWordSlot
  have retainedEqual := (firstEarlier.read equalHome equalOld 32 1).trans equalRead
  apply vector_movemask_checked boundary entered middle inputs outputs frame args middleCall
    enteredWF homes middleAuthority true equalHome equal equalSlot retainedEqual post
  intro equalWord after equalWordSlot equalWordRead secondEarlier secondPreserved afterCall afterAuthority secondNext
  have generatedOld := homes.ordered 6 7 .word32 .word32 generatedWord equalWord
    (by decide) generatedWordSlot equalWordSlot
  exact continuation generatedWord equalWord after generatedWordSlot equalWordSlot
    ((secondEarlier.read generatedWord generatedOld 4 1).trans generatedWordRead) equalWordRead
    (firstEarlier.trans (secondEarlier.weaken (Nat.le_of_lt generatedOld)))
    (firstPreserved.trans secondPreserved) afterCall afterAuthority (Nat.le_trans firstNext secondNext)

#print axioms vector_movemasks_checked
end UInt256Proof.Subtract.Safety
