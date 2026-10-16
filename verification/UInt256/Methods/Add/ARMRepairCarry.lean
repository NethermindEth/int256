import UInt256.Methods.Add.ARMRepairMasks

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector CIL.Vector

def repaired128Carry (carry propagation full repair : BitVec 128) : BitVec 128 :=
  carry ||| (propagation ||| (full &&& repair))

/-- Update the saved high carry mask from initialized private snapshots. -/
theorem vector128_arm_repair_carry (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (leadingLength : leading.length = 113)
    (code : body.code = leading ++ armRepairCode ++ tail)
    (repairSpecs : ∀ i : Fin 4, specs[19 + i.val]? = some vector128ZeroSpec)  (baseSpecs : ∀ i : Fin 14, specs[i.val]? = some vector128ZeroSpec)  (enabled : body.profile.advSimd = true)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (carry : BitVec 128) (carryHome : Reference)
    (carrySlot : frame.locals[7]? = some (.bytes .vector128 carryHome))
    (carryRead : read current carryHome 16 1 = .ok (numberBytes carry.toNat 16))
    (propagation : BitVec 128) (propagationHome : Reference)
    (propagationSlot : frame.locals[13]? = some (.bytes .vector128 propagationHome))
    (propagationRead : read current propagationHome 16 1 = .ok (numberBytes propagation.toNat 16))
    (full : BitVec 128) (fullHome : Reference)
    (fullSlot : frame.locals[21]? = some (.bytes .vector128 fullHome))
    (fullRead : read current fullHome 16 1 = .ok (numberBytes full.toNat 16))
    (repair : BitVec 128) (repairHome : Reference)
    (repairSlot : frame.locals[23]? = some (.bytes .vector128 repairHome))
    (repairRead : read current repairHome 16 1 = .ok (numberBytes repair.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[7]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok (numberBytes (repaired128Carry carry propagation full repair).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (repaired128Carry carry propagation full repair).toNat 16) 1 = .ok after →
      ∃ fuel final returned,
        run program fuel method 145 args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 137 args frame [] current = .ok (final, returned) ∧ post final returned := by
  first
  | solve | simp [body.profile] at enabled
  |
    obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
      vector128_local_store program body specs boundary entered current inputs outputs frame root slots layout currentCall
        enteredWF homes authority 6 vector128ZeroSpec (baseSpecs 6)
        (.v128 (repaired128Carry carry propagation full repair))
        (repaired128Carry carry propagation full repair).toNat rfl
    have done := continuation reference after slot loaded retained afterCall afterAuthority written
    have load_carry := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 carry) carry.toNat rfl carrySlot carryRead
    have load_propagation := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 propagation) propagation.toNat rfl propagationSlot propagationRead
    have load_full := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 full) full.toNat rfl fullSlot fullRead
    have load_repair := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 repair) repair.toNat rfl repairSlot repairRead
    repeat' first
      | exact done
      | (apply run_next_exists post found (by simp [code, List.getElem?_append, leadingLength, armRepairCode]; rfl)
         first
         | exact load_carry _ _
         | exact load_propagation _ _
         | exact load_full _ _
         | exact load_repair _ _
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [localResult, checkedIntrinsic, step, enabled, pureArity, scalars, CIL.step.eq_def, CIL.Intrinsic.available,
               CIL.Vector.intrinsic_and128, CIL.Vector.intrinsic_or128, repaired128Carry,
               checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_arm_repair_carry
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector

/-- Compose the carry-mask and high-result overwrites, retaining every other private vector and the exact initialized values of both updated homes. -/
theorem vector128_arm_update_pair (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (leadingLength : leading.length = 113)
    (code : body.code = leading ++ armRepairCode ++ tail)
    (repairSpecs : ∀ i : Fin 4, specs[19 + i.val]? = some vector128ZeroSpec)  (baseSpecs : ∀ i : Fin 14, specs[i.val]? = some vector128ZeroSpec)   (enabled : body.profile.advSimd = true)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (carry : BitVec 128) (carryHome : Reference)
    (carrySlot : frame.locals[7]? = some (.bytes .vector128 carryHome))
    (carryRead : read current carryHome 16 1 = .ok (numberBytes carry.toNat 16))
    (propagation : BitVec 128) (propagationHome : Reference)
    (propagationSlot : frame.locals[13]? = some (.bytes .vector128 propagationHome))
    (propagationRead : read current propagationHome 16 1 = .ok (numberBytes propagation.toNat 16))
    (full : BitVec 128) (fullHome : Reference)
    (fullSlot : frame.locals[21]? = some (.bytes .vector128 fullHome))
    (fullRead : read current fullHome 16 1 = .ok (numberBytes full.toNat 16))
    (repair : BitVec 128) (repairHome : Reference)
    (repairSlot : frame.locals[23]? = some (.bytes .vector128 repairHome))
    (repairRead : read current repairHome 16 1 = .ok (numberBytes repair.toNat 16))
    (high : BitVec 128) (highHome : Reference)
    (highSlot : slots[10]? = some (.bytes .vector128 highHome))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ updatedCarry updatedHigh after,
      slots[6]? = some (.bytes .vector128 updatedCarry) →
      slots[10]? = some (.bytes .vector128 updatedHigh) →
      read after updatedCarry 16 1 = .ok (numberBytes (repaired128Carry carry propagation full repair).toNat 16) →
      read after updatedHigh 16 1 = .ok (numberBytes (corrected128 high repair).toNat 16) →
      (∀ i, i ≠ 6 → i ≠ 10 → ∀ reference bytes,
        slots[i]? = some (.bytes .vector128 reference) →
        read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned,
        run program fuel method 149 args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 137 args frame [] current = .ok (final, returned) ∧ post final returned := by
  apply vector128_arm_repair_carry program body method specs found leading tail leadingLength code repairSpecs baseSpecs enabled boundary entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority carry carryHome carrySlot carryRead
    propagation propagationHome propagationSlot propagationRead full fullHome fullSlot fullRead
    repair repairHome repairSlot repairRead post
  intro updatedCarry middle updatedCarrySlot updatedCarryRead preserved middleCall middleAuthority firstWrite
  have carryTail : slots[6]? = some (.bytes .vector128 updatedCarry) := by simpa [layout] using updatedCarrySlot
  have repairTail : slots[22]? = some (.bytes .vector128 repairHome) := by simpa [layout] using repairSlot
  have savedHigh := vector128_other_read specs entered current middle boundary slots homes 10 6 (by decide)
    highHome updatedCarry highSlot carryTail _ _ firstWrite highRead
  have savedRepair := vector128_other_read specs entered current middle boundary slots homes 22 6 (by decide)
    repairHome updatedCarry repairTail carryTail _ _ firstWrite repairRead
  have actualHigh : frame.locals[11]? = some (.bytes .vector128 highHome) := by simpa [layout] using highSlot
  apply vector128_arm_repair_value program body method specs found leading tail leadingLength code repairSpecs baseSpecs enabled boundary entered middle inputs outputs frame root slots layout args
    middleCall enteredWF homes middleAuthority true high repair highHome repairHome actualHigh repairSlot savedHigh savedRepair post
  intro updatedHigh after updatedHighSlot updatedHighRead kept afterCall afterAuthority secondWrite
  have highTail : slots[10]? = some (.bytes .vector128 updatedHigh) := by simpa [layout] using updatedHighSlot
  have savedCarry := vector128_other_read specs entered middle after boundary slots homes 6 10 (by decide)
    updatedCarry updatedHigh carryTail highTail _ _ secondWrite updatedCarryRead
  have others : ∀ i, i ≠ 6 → i ≠ 10 → ∀ reference bytes,
      slots[i]? = some (.bytes .vector128 reference) →
      read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes := by
    intro i notCarry notHigh reference bytes slot loaded
    exact vector128_other_read specs entered middle after boundary slots homes i 10 notHigh
      reference updatedHigh slot highTail _ _ secondWrite
      (vector128_other_read specs entered current middle boundary slots homes i 6 notCarry
        reference updatedCarry slot carryTail _ _ firstWrite loaded)
  exact continuation updatedCarry updatedHigh after carryTail highTail savedCarry updatedHighRead others
    (preserved.trans kept) afterCall afterAuthority
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ firstWrite).next
      (write_extends_allocations _ _ _ _ _ secondWrite).next)

#print axioms vector128_arm_update_pair
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety CIL.Vector UInt256Model UInt256Model.Safety UInt256Proof.SIMD

/-- The checked ARM extraction/OR expression is the independently specified propagated repair mask. -/
theorem vector128_arm_extra_value (a b : Limbs) :
    incoming128High (propagationLo a b) (propagationHi a b) |||
      incoming128Low (full128 (correctedHi a b) &&&
        incoming128High (propagationLo a b) (propagationHi a b)) = extraHi a b := by
  simp only [extraHi, full128, show (0 : BitVec 128) = BitVec.ofNat 128 0 from rfl]
  rw [incoming128_arm_low]
  simp only [propagationARM, incoming128_arm_high]

theorem vector128_arm_repaired_high (a b : Limbs) :
    corrected128 (correctedHi a b) (extraHi a b) = repairedHi a b := by rfl

theorem vector128_arm_repaired_carry (a b : Limbs) :
    repaired128Carry (pack128 (carryMask (a 2) (b 2)) (carryMask (a 3) (b 3)))
      (propagationHi a b) (full128 (correctedHi a b)) (extraHi a b) =
      UInt256Proof.Reporting.repairedCarryHi a b := by
  simp only [repaired128Carry, UInt256Proof.Reporting.repairedCarryHi, full128, BitVec.or_assoc,
    show (0 : BitVec 128) = BitVec.ofNat 128 0 from rfl]

theorem vector128_snapshot_high_carry (memory : Memory) (left right : Reference) :
    vector128SnapshotValue memory left right 6 =
      pack128 (carryMask (inputLimb memory left 2) (inputLimb memory right 2))
        (carryMask (inputLimb memory left 3) (inputLimb memory right 3)) := by
  simp only [vector128SnapshotValue, show (6 : Fin 11).val = 6 from rfl,
    input_half_high, halfCarry, halfSum, zip128, lane128_0, lane128_1, carryMask]

#print axioms vector128_arm_extra_value
#print axioms vector128_arm_repaired_high
#print axioms vector128_arm_repaired_carry
#print axioms vector128_snapshot_high_carry
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector

def repair128Mask (high lowPropagation highPropagation : BitVec 128) : BitVec 128 :=
  incoming128High lowPropagation highPropagation |||
    incoming128Low (full128 high &&& incoming128High lowPropagation highPropagation)

/-- All repair-mask preparation, retaining the fourteen original snapshots. -/
theorem vector128_arm_prepare (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (leadingLength : leading.length = 113)
    (code : body.code = leading ++ armRepairCode ++ tail)
    (repairSpecs : ∀ i : Fin 4, specs[19 + i.val]? = some vector128ZeroSpec)  (baseSpecs : ∀ i : Fin 14, specs[i.val]? = some vector128ZeroSpec)   (enabled : body.profile.advSimd = true)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag) (argument : args[3]? = some (.scalar (.i32 flag)))
    (values : Fin 14 → BitVec 128)
    (condition : values 13 = selectedPropagation128 body.profile.advSimd flag (values 11) (values 12))
    (snapshots : ∀ i : Fin 14, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
      read current reference 16 1 = .ok (numberBytes (values i).toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ fullHome repairHome after,
      slots[20]? = some (.bytes .vector128 fullHome) →
      slots[22]? = some (.bytes .vector128 repairHome) →
      read after fullHome 16 1 = .ok (numberBytes (full128 (values 10)).toNat 16) →
      read after repairHome 16 1 = .ok (numberBytes (repair128Mask (values 10) (values 11) (values 12)).toNat 16) →
      (∀ i : Fin 14, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
        read after reference 16 1 = .ok (numberBytes (values i).toNat 16)) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned,
        run program fuel method 137 args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 113 args frame [] current = .ok (final, returned) ∧ post final returned := by
  obtain ⟨lowHome, lowSlot, lowRead⟩ := snapshots 11
  obtain ⟨highHome, highSlot, highRead⟩ := snapshots 12
  obtain ⟨conditionHome, conditionSlot, conditionRead⟩ := snapshots 13
  obtain ⟨resultHome, resultSlot, resultRead⟩ := snapshots 10
  change slots[11]? = _ at lowSlot
  change slots[12]? = _ at highSlot
  change slots[13]? = _ at conditionSlot
  change slots[10]? = _ at resultSlot
  have actualLow : frame.locals[12]? = some (.bytes .vector128 lowHome) := by simpa [layout] using lowSlot
  have actualHigh : frame.locals[13]? = some (.bytes .vector128 highHome) := by simpa [layout] using highSlot
  have actualCondition : frame.locals[14]? = some (.bytes .vector128 conditionHome) := by simpa [layout] using conditionSlot
  rw [condition] at conditionRead
  apply vector128_arm_repair_mask program body method specs found leading tail leadingLength code repairSpecs enabled boundary entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority flag flagFit argument (values 11) (values 12) lowHome highHome
    actualLow actualHigh lowRead highRead conditionHome actualCondition conditionRead post
  intro propagationHome first propagationSlot propagationRead firstPreserved firstCall firstAuthority firstWrite
  have propagationTail : slots[19]? = some (.bytes .vector128 propagationHome) := by simpa [layout] using propagationSlot
  have savedResult := vector128_prior_read specs entered current first boundary slots homes 10 19 (by decide)
    resultHome propagationHome resultSlot propagationTail _ _ firstWrite resultRead
  have firstSnapshots : ∀ i : Fin 14, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
      read first reference 16 1 = .ok (numberBytes (values i).toNat 16) := by
    intro i
    obtain ⟨reference, slot, loaded⟩ := snapshots i
    exact ⟨reference, slot, vector128_prior_read specs entered current first boundary slots homes i.val 19 (by omega)
      reference propagationHome slot propagationTail _ _ firstWrite loaded⟩
  apply vector128_arm_extra_pair program body method specs found leading tail leadingLength code repairSpecs baseSpecs enabled boundary entered first inputs outputs frame root slots layout args
    firstCall enteredWF homes firstAuthority (values 10) (incoming128High (values 11) (values 12))
    resultHome propagationHome resultSlot propagationTail savedResult propagationRead post
  intro fullHome extraHome second fullSlot extraSlot fullRead extraRead kept secondPreserved secondCall secondAuthority secondNext
  have savedPropagation := kept 19 (by decide) propagationHome _ propagationTail propagationRead
  have actualExtra : frame.locals[22]? = some (.bytes .vector128 extraHome) := by simpa [layout] using extraSlot
  apply vector128_arm_repair_value program body method specs found leading tail leadingLength code repairSpecs baseSpecs enabled boundary entered second inputs outputs frame root slots layout args
    secondCall enteredWF homes secondAuthority false (incoming128High (values 11) (values 12))
    (incoming128Low (full128 (values 10) &&& incoming128High (values 11) (values 12)))
    propagationHome extraHome propagationSlot actualExtra savedPropagation extraRead post
  intro repairHome after repairSlot repairRead thirdPreserved afterCall afterAuthority thirdWrite
  have repairTail : slots[22]? = some (.bytes .vector128 repairHome) := by simpa [layout] using repairSlot
  have savedFull := vector128_prior_read specs entered second after boundary slots homes 20 22 (by decide)
    fullHome repairHome fullSlot repairTail _ _ thirdWrite fullRead
  have finalSnapshots : ∀ i : Fin 14, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
      read after reference 16 1 = .ok (numberBytes (values i).toNat 16) := by
    intro i
    obtain ⟨reference, slot, loaded⟩ := firstSnapshots i
    exact ⟨reference, slot, vector128_prior_read specs entered second after boundary slots homes i.val 22 (by omega)
      reference repairHome slot repairTail _ _ thirdWrite (kept i.val (by omega) reference _ slot loaded)⟩
  exact continuation fullHome repairHome after fullSlot repairTail savedFull repairRead finalSnapshots
    ((firstPreserved.trans secondPreserved).trans thirdPreserved) afterCall afterAuthority
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ firstWrite).next
      (Nat.le_trans secondNext (write_extends_allocations _ _ _ _ _ thirdWrite).next))

#print axioms vector128_arm_prepare
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def armRepairSnapshot (values : Fin 14 → BitVec 128) (i : Fin 14) : BitVec 128 :=
  let repair := repair128Mask (values 10) (values 11) (values 12)
  if i.val = 6 then repaired128Carry (values 6) (values 12) (full128 (values 10)) repair
  else if i.val = 10 then corrected128 (values 10) repair else values i

/-- Complete ARM private repair state from the selected propagation condition through both overwrites, retaining all unaffected original snapshots. -/
theorem vector128_arm_repair_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (leadingLength : leading.length = 113)
    (code : body.code = leading ++ armRepairCode ++ tail)
    (repairSpecs : ∀ i : Fin 4, specs[19 + i.val]? = some vector128ZeroSpec)  (baseSpecs : ∀ i : Fin 14, specs[i.val]? = some vector128ZeroSpec)    (enabled : body.profile.advSimd = true)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (flag : BitVec 32) (flagFit : CIL.NarrowKind.unsigned8.extend flag = flag) (argument : args[3]? = some (.scalar (.i32 flag)))
    (values : Fin 14 → BitVec 128)
    (condition : values 13 = selectedPropagation128 body.profile.advSimd flag (values 11) (values 12))
    (snapshots : ∀ i : Fin 14, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
      read current reference 16 1 = .ok (numberBytes (values i).toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      (∀ i : Fin 14, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
        read after reference 16 1 = .ok (numberBytes (armRepairSnapshot values i).toNat 16)) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned,
        run program fuel method 149 args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 113 args frame [] current = .ok (final, returned) ∧ post final returned := by
  apply vector128_arm_prepare program body method specs found leading tail leadingLength code repairSpecs baseSpecs enabled boundary entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority flag flagFit argument values condition snapshots post
  intro fullHome repairHome middle fullSlot repairSlot fullRead repairRead saved preserved middleCall middleAuthority advanced
  obtain ⟨carryHome, carrySlot, carryRead⟩ := saved 6
  obtain ⟨propagationHome, propagationSlot, propagationRead⟩ := saved 12
  obtain ⟨highHome, highSlot, highRead⟩ := saved 10
  change slots[6]? = _ at carrySlot
  change slots[12]? = _ at propagationSlot
  change slots[10]? = _ at highSlot
  have actualCarry : frame.locals[7]? = some (.bytes .vector128 carryHome) := by simpa [layout] using carrySlot
  have actualPropagation : frame.locals[13]? = some (.bytes .vector128 propagationHome) := by simpa [layout] using propagationSlot
  have actualFull : frame.locals[21]? = some (.bytes .vector128 fullHome) := by simpa [layout] using fullSlot
  have actualRepair : frame.locals[23]? = some (.bytes .vector128 repairHome) := by simpa [layout] using repairSlot
  apply vector128_arm_update_pair program body method specs found leading tail leadingLength code repairSpecs baseSpecs enabled boundary entered middle inputs outputs frame root slots layout args
    middleCall enteredWF homes middleAuthority (values 6) carryHome actualCarry carryRead
    (values 12) propagationHome actualPropagation propagationRead (full128 (values 10)) fullHome actualFull fullRead
    (repair128Mask (values 10) (values 11) (values 12)) repairHome actualRepair repairRead
    (values 10) highHome highSlot highRead post
  intro updatedCarry updatedHigh after updatedCarrySlot updatedHighSlot updatedCarryRead updatedHighRead kept
    finalPreserved afterCall afterAuthority next
  have complete : ∀ i : Fin 14, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
      read after reference 16 1 = .ok (numberBytes (armRepairSnapshot values i).toNat 16) := by
    intro i
    by_cases carry : i.val = 6
    · have same : i = 6 := by omega
      subst i
      exact ⟨updatedCarry, updatedCarrySlot, updatedCarryRead⟩
    · by_cases high : i.val = 10
      · have same : i = 10 := by omega
        subst i
        exact ⟨updatedHigh, updatedHighSlot, updatedHighRead⟩
      · obtain ⟨reference, slot, loaded⟩ := saved i
        refine ⟨reference, slot, ?_⟩
        simp only [armRepairSnapshot, carry, high, ite_false]
        exact kept i.val carry high reference _ slot loaded
  exact continuation after complete (preserved.trans finalPreserved) afterCall afterAuthority (Nat.le_trans advanced next)

#print axioms vector128_arm_repair_checked
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.SIMD

def vector128DecisionValues (advSimd : Bool) (memory : Memory) (left right : Reference) (flag : BitVec 32)
    (i : Fin 14) : BitVec 128 :=
  if within : i.val < 13 then vector128BranchValue memory left right ⟨i.val, within⟩
  else selectedPropagation128 advSimd flag (vector128BranchValue memory left right 11) (vector128BranchValue memory left right 12)

theorem vector128_decision_values_old (advSimd : Bool) (memory : Memory) (left right : Reference) (flag : BitVec 32) (i : Fin 13) :
    vector128DecisionValues advSimd memory left right flag ⟨i.val, by omega⟩ = vector128BranchValue memory left right i := by
  simp only [vector128DecisionValues, dite_eq_left i.isLt]

theorem vector128_decision_repair_mask (advSimd : Bool) (memory : Memory) (left right : Reference) (flag : BitVec 32) :
    repair128Mask (vector128DecisionValues advSimd memory left right flag 10)
      (vector128DecisionValues advSimd memory left right flag 11) (vector128DecisionValues advSimd memory left right flag 12) =
      extraHi (inputLimb memory left) (inputLimb memory right) := by
  change repair128Mask (vector128SnapshotValue memory left right 10)
    (vector128BranchValue memory left right 11) (vector128BranchValue memory left right 12) = _
  rw [vector128_snapshot_high, vector128_branch_low, vector128_branch_high]
  exact vector128_arm_extra_value _ _

theorem vector128_repaired_snapshot_high (advSimd : Bool) (memory : Memory) (left right : Reference) (flag : BitVec 32) :
    armRepairSnapshot (vector128DecisionValues advSimd memory left right flag) 10 =
      repairedHi (inputLimb memory left) (inputLimb memory right) := by
  change corrected128 (vector128SnapshotValue memory left right 10)
    (repair128Mask (vector128DecisionValues advSimd memory left right flag 10)
      (vector128DecisionValues advSimd memory left right flag 11) (vector128DecisionValues advSimd memory left right flag 12)) = _
  rw [vector128_snapshot_high, vector128_decision_repair_mask]
  exact vector128_arm_repaired_high _ _

theorem vector128_repaired_snapshot_carry (advSimd : Bool) (memory : Memory) (left right : Reference) (flag : BitVec 32) :
    armRepairSnapshot (vector128DecisionValues advSimd memory left right flag) 6 =
      UInt256Proof.Reporting.repairedCarryHi (inputLimb memory left) (inputLimb memory right) := by
  change repaired128Carry (vector128SnapshotValue memory left right 6)
    (vector128BranchValue memory left right 12) (full128 (vector128SnapshotValue memory left right 10))
    (repair128Mask (vector128DecisionValues advSimd memory left right flag 10)
      (vector128DecisionValues advSimd memory left right flag 11) (vector128DecisionValues advSimd memory left right flag 12)) = _
  rw [vector128_snapshot_high_carry, vector128_branch_high, vector128_snapshot_high, vector128_decision_repair_mask]
  exact vector128_arm_repaired_carry _ _

#print axioms vector128_decision_values_old
#print axioms vector128_decision_repair_mask
#print axioms vector128_repaired_snapshot_high
#print axioms vector128_repaired_snapshot_carry
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety CIL.Vector UInt256Model.Safety UInt256Proof.SIMD UInt256Proof.Reporting

/-- The actual fast-return mask encodes overflow when reporting was requested. -/
theorem vector128_snapshot_fast_flag (advSimd : Bool) (memory : Memory) (left right : Reference) (flag : BitVec 32)
    (reporting : flag ≠ BitVec.ofNat 32 0)
    (fast : selectedPropagation128 advSimd flag (vector128BranchValue memory left right 11)
      (vector128BranchValue memory left right 12) = BitVec.ofNat 128 0) :
    (if lane64 (vector128SnapshotValue memory left right 6) 1 > BitVec.ofNat 64 0
      then (1 : BitVec 32) else 0) =
      if 2^256 ≤ (inputValue memory left).toNat + (inputValue memory right).toNat then 1 else 0 := by
  rw [vector128_branch_low, vector128_branch_high] at fast
  have carry := vector128_reporting_fast_carry advSimd (inputLimb memory left) (inputLimb memory right)
    flag reporting fast
  rw [vector128_snapshot_high_carry, lane128_1, carry_mask_negative, ← carry]
  simp only [word_positive, ne_eq, BitVec.neg_eq_zero_iff]
  have overflow := finalCarry_overflow (inputLimb memory left) (inputLimb memory right)
  rw [input_limbs_value, input_limbs_value] at overflow
  change (finalCarry (inputLimb memory left) (inputLimb memory right) ≠ BitVec.ofNat 64 0) ↔ _ at overflow
  simp only [overflow]

/-- The repaired high mask gives overflow of the original caller operands. -/
theorem vector128_snapshot_repaired_flag (advSimd : Bool) (memory : Memory) (left right : Reference) (flag : BitVec 32) :
    (if lane64 (armRepairSnapshot (vector128DecisionValues advSimd memory left right flag) 6) 1 > BitVec.ofNat 64 0
      then (1 : BitVec 32) else 0) =
      if 2^256 ≤ (inputValue memory left).toNat + (inputValue memory right).toNat then 1 else 0 := by
  rw [vector128_repaired_snapshot_carry, repaired_high_flag]
  simp only [word_positive, ne_eq, BitVec.neg_eq_zero_iff]
  have overflow := finalCarry_overflow (inputLimb memory left) (inputLimb memory right)
  rw [input_limbs_value, input_limbs_value] at overflow
  change (finalCarry (inputLimb memory left) (inputLimb memory right) ≠ BitVec.ofNat 64 0) ↔ _ at overflow
  simp only [overflow]

#print axioms vector128_snapshot_fast_flag
#print axioms vector128_snapshot_repaired_flag
end UInt256Proof.Add.Safety
