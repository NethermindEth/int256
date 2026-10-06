import UInt256.Methods.Subtract.Vector128BinaryPair

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
