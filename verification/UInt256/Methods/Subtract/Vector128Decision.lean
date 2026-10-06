import UInt256.Methods.Subtract.Vector128BinaryPair
import UInt256.Methods.AddSubtract.Vector128IncomingPair

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def vector128PreparedValue (values : Fin 4 → BitVec 128) (i : Fin 8) : BitVec 128 :=
  if h : i.val < 4 then values ⟨i.val, h⟩
  else if i.val = 4 then vector128BinaryValue false (values 0) (values 2)
  else if i.val = 5 then vector128BinaryValue false (values 1) (values 3)
  else if i.val = 6 then vector128BinaryValue true (values 0) (values 2)
  else vector128BinaryValue true (values 1) (values 3)

/-- Both difference halves and both initial borrow masks are stored before any
    caller output write. All eight initialized snapshots survive the prefix. -/
theorem vector128_prepared (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (locations : Fin 4 → Reference) (values : Fin 4 → BitVec 128)
    (located : ∀ i : Fin 4, slots[i.val]? = some (.bytes .vector128 (locations i)))
    (readable : ∀ i, read current (locations i) 16 1 = .ok (numberBytes (values i).toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      (∀ i : Fin 8, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
        read after reference 16 1 = .ok (numberBytes (vector128PreparedValue values i).toNat 16)) →
      MemoryBelow boundary current after → CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after → current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned,
        run Extracted.program fuel vector128Index 38 args frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 22 args frame [] current = .ok (final, returned) ∧ post final returned := by
  apply vector128_binary_pair false boundary entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority locations values located readable post
  intro low high middle lowSlot highSlot lowRead highRead saved preserved middleCall middleAuthority next
  have reads (i : Fin 4) : read middle (locations i) 16 1 = .ok (numberBytes (values i).toNat 16) :=
    saved i.val i.isLt _ _ (located i) (readable i)
  apply vector128_binary_pair true boundary entered middle inputs outputs frame root slots layout args
    middleCall enteredWF homes middleAuthority locations values located reads post
  intro lowMask highMask after lowMaskSlot highMaskSlot lowMaskRead highMaskRead kept retained afterCall afterAuthority advanced
  have snapshots : ∀ i : Fin 8, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
      read after reference 16 1 = .ok (numberBytes (vector128PreparedValue values i).toNat 16) := by
    intro i
    by_cases original : i.val < 4
    · refine ⟨locations ⟨i.val, original⟩, located ⟨i.val, original⟩, ?_⟩
      simp only [vector128PreparedValue, dite_eq_left original]
      exact kept i.val (show i.val < 6 by omega) _ _ (located ⟨i.val, original⟩) (reads ⟨i.val, original⟩)
    · have cases : i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
      rcases cases with rfl | rfl | rfl | rfl
      · exact ⟨low, lowSlot, kept 4 (by decide) _ _ lowSlot lowRead⟩
      · exact ⟨high, highSlot, kept 5 (by decide) _ _ highSlot highRead⟩
      · exact ⟨lowMask, lowMaskSlot, lowMaskRead⟩
      · exact ⟨highMask, highMaskSlot, highMaskRead⟩
  exact continuation after snapshots (preserved.trans retained) afterCall afterAuthority (Nat.le_trans next advanced)

#print axioms vector128_prepared

def vector128InputValues (memory : Memory) (left right : Reference) (i : Fin 4) : BitVec 128 :=
  if i = 0 then inputHalf memory left 0 else if i = 1 then inputHalf memory left 1
  else if i = 2 then inputHalf memory right 0 else inputHalf memory right 1

/-- Entry through all initial arithmetic stores, expressed entirely in terms of
    the original caller operands and with every original caller byte preserved. -/
theorem vector128_prepared_entry (original entered : Memory)
    (inputs outputs : List Reference) (left right : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (setup : enterFrame vector128Body args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity vector128Specs slots)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      (∀ i : Fin 8, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
        read after reference 16 1 = .ok (numberBytes
          (vector128PreparedValue (vector128InputValues original left right) i).toNat 16)) →
      MemoryBelow original.nextIdentity original after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after → entered.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned,
        run Extracted.program fuel vector128Index 38 args (vector128SavedFrame frame slots right) [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 0 args frame [] entered = .ok (final, returned) ∧ post final returned := by
  apply vector128_inputs_checked original entered inputs outputs left right frame slots args call setup layout homes
    leftMember rightMember leftArg rightArg post
  intro l0 l1 r0 r1 current s0 s1 s2 s3 read0 read1 read2 read3 preserved currentCall authority next
  let locations : Fin 4 → Reference := fun i => if i = 0 then l0 else if i = 1 then l1 else if i = 2 then r0 else r1
  have located : ∀ i : Fin 4, slots[i.val]? = some (.bytes .vector128 (locations i)) := by
    intro i
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> simp_all [locations]
    exact s3
  have readable : ∀ i : Fin 4, read current (locations i) 16 1 =
      .ok (numberBytes (vector128InputValues original left right i).toNat 16) := by
    intro i
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> simp_all [locations, vector128InputValues]
  apply vector128_prepared original.nextIdentity entered current inputs outputs (vector128SavedFrame frame slots right)
    (.root (some (.address right))) slots rfl args currentCall
    (enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup) homes authority locations
    (vector128InputValues original left right) located readable post
  intro after snapshots retained afterCall afterAuthority advanced
  exact continuation after snapshots (preserved.trans retained) afterCall afterAuthority (Nat.le_trans next advanced)

#print axioms vector128_prepared_entry

end UInt256Proof.Subtract.Safety

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector

@[simp] theorem incoming128Offset_subtract : incoming128Offset = 1 := by rfl

def vector128IncomingValue (values : Fin 4 → BitVec 128) (i : Fin 10) : BitVec 128 :=
  if h : i.val < 8 then vector128PreparedValue values ⟨i.val, h⟩
  else if i.val = 8 then incoming128Low (vector128PreparedValue values 6)
  else incoming128High (vector128PreparedValue values 6) (vector128PreparedValue values 7)

/-- The operand, difference and borrow snapshots remain initialized through both
    incoming-mask stores; their values refer to the initial caller operands. -/
theorem vector128_incoming_entry (original entered : Memory)
    (inputs outputs : List Reference) (left right : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions Extracted.program original inputs outputs)
    (setup : enterFrame vector128Body args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity vector128Specs slots)
    (leftMember : left ∈ inputs) (rightMember : right ∈ inputs)
    (leftArg : args[0]? = some (.reference (.address left)))
    (rightArg : args[1]? = some (.reference (.address right)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      (∀ i : Fin 10, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
        read after reference 16 1 = .ok (numberBytes
          (vector128IncomingValue (vector128InputValues original left right) i).toNat 16)) →
      MemoryBelow original.nextIdentity original after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after → entered.nextIdentity ≤ after.nextIdentity →
      ∃ fuel final returned,
        run Extracted.program fuel vector128Index 63 args (vector128SavedFrame frame slots right) [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel vector128Index 0 args frame [] entered = .ok (final, returned) ∧ post final returned := by
  apply vector128_prepared_entry original entered inputs outputs left right frame slots args call setup layout homes
    leftMember rightMember leftArg rightArg post
  intro current snapshots preserved currentCall authority next
  obtain ⟨low, lowSlot, lowRead⟩ := snapshots 6
  obtain ⟨high, highSlot, highRead⟩ := snapshots 7
  apply vector128_incoming_pair original.nextIdentity entered current inputs outputs
    (vector128SavedFrame frame slots right) (.root (some (.address right))) slots rfl args currentCall
    (enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup) homes authority
    (vector128PreparedValue (vector128InputValues original left right) 6)
    (vector128PreparedValue (vector128InputValues original left right) 7) [] low high lowSlot highSlot lowRead highRead post
  intro lowIncoming highIncoming after lowIncomingSlot highIncomingSlot lowIncomingRead highIncomingRead
    kept retained afterCall afterAuthority advanced
  have allSnapshots : ∀ i : Fin 10, ∃ reference, slots[i.val]? = some (.bytes .vector128 reference) ∧
      read after reference 16 1 = .ok (numberBytes
        (vector128IncomingValue (vector128InputValues original left right) i).toNat 16) := by
    intro i
    by_cases earlier : i.val < 8
    · obtain ⟨reference, slot, loaded⟩ := snapshots ⟨i.val, earlier⟩
      refine ⟨reference, slot, ?_⟩
      simp only [vector128IncomingValue, dite_eq_left earlier]
      exact kept i.val earlier reference _ slot loaded
    · have cases : i = 8 ∨ i = 9 := by omega
      rcases cases with rfl | rfl
      · exact ⟨lowIncoming, lowIncomingSlot, lowIncomingRead⟩
      · exact ⟨highIncoming, highIncomingSlot, highIncomingRead⟩
  exact continuation after allSnapshots (preserved.trans retained) afterCall afterAuthority (Nat.le_trans next advanced)

#print axioms vector128_incoming_entry
end UInt256Proof.Subtract.Safety

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector

def vector128Propagation (low high incomingLow incomingHigh : BitVec 128) : BitVec 128 :=
  (zip128 (fun x y => mask64 (x == y)) low 0 &&& incomingLow) |||
  (zip128 (fun x y => mask64 (x == y)) high 0 &&& incomingHigh)

/-- Evaluate the actual propagation test using initialized snapshots. The test
    changes neither caller memory nor private snapshots. -/
theorem vector128_decision (memory : Memory) (frame : Frame) (args : List Value)
    (low high incomingLow incomingHigh : BitVec 128)
    (lowHome highHome incomingLowHome incomingHighHome : Reference)
    (lowSlot : frame.locals[5]? = some (.bytes .vector128 lowHome))
    (highSlot : frame.locals[6]? = some (.bytes .vector128 highHome))
    (incomingLowSlot : frame.locals[9]? = some (.bytes .vector128 incomingLowHome))
    (incomingHighSlot : frame.locals[10]? = some (.bytes .vector128 incomingHighHome))
    (lowRead : read memory lowHome 16 1 = .ok (numberBytes low.toNat 16))
    (highRead : read memory highHome 16 1 = .ok (numberBytes high.toNat 16))
    (incomingLowRead : read memory incomingLowHome 16 1 = .ok (numberBytes incomingLow.toNat 16))
    (incomingHighRead : read memory incomingHighHome 16 1 = .ok (numberBytes incomingHigh.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel vector128Index
        (if vector128Propagation low high incomingLow incomingHigh = BitVec.ofNat 128 0 then 119 else 77)
        args frame [] memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 63 args frame [] memory = .ok (result, returned) ∧ post result returned := by
  have loadLow := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 low) low.toNat rfl lowSlot lowRead
  have loadHigh := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 high) high.toNat rfl highSlot highRead
  have loadIncomingLow := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 incomingLow) incomingLow.toNat rfl incomingLowSlot incomingLowRead
  have loadIncomingHigh := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 incomingHigh) incomingHigh.toNat rfl incomingHighSlot incomingHighRead
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  have profile : vector128Body.profile = Extracted.profile := by rfl
  by_cases zero : vector128Propagation low high incomingLow incomingHigh = BitVec.ofNat 128 0
  all_goals
    simp only [zero, ite_true, ite_false] at continuation
    simp only [vector128Propagation] at zero
    iterate 14
      apply run_next_exists post found (by rfl)
      first
      | exact loadLow _ _
      | exact loadHigh _ _
      | exact loadIncomingLow _ _
      | exact loadIncomingHigh _ _
      | (simp (config := { implicitDefEqProofs := false })
             [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.Intrinsic.available,
               intrinsic_zero128, intrinsic_eq128, intrinsic_and128, intrinsic_or128, intrinsic_equal_all128,
               show (0 : BitVec 128) = BitVec.ofNat 128 0 from rfl, zero,
               checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
         first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)
    simp at zero
    simp_all

#print axioms vector128_decision
end UInt256Proof.Subtract.Safety
