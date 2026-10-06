import UInt256.Methods.Add.Vector128CorrectionPair

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Initial operands and the exact saved vectors at the output-stage boundary. -/
def vector128SnapshotValue (memory : Memory) (left right : Reference) (i : Fin 11) : BitVec 128 :=
  let a := inputHalf memory left 0
  let b := inputHalf memory left 1
  let c := inputHalf memory right 0
  let d := inputHalf memory right 1
  let low := halfSum a c
  let high := halfSum b d
  let lowMask := halfCarry low a
  let highMask := halfCarry high b
  match i.val with
  | 0 => a | 1 => b | 2 => c | 3 => d
  | 4 => high | 5 => lowMask | 6 => highMask
  | 7 => incoming128Low lowMask | 8 => incoming128High lowMask highMask
  | 9 => corrected128 low (incoming128Low lowMask)
  | _ => corrected128 high (incoming128High lowMask highMask)

/-- Complete checked execution from entry to the first output-stage instruction.
    Every saved vector is initialized from the original inputs; caller bytes are
    unchanged, without any restriction on valid caller overlap. -/
theorem vector128_snapshots_checked (original entered : Memory)
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
      (∀ i : Fin 11, ∃ reference,
        slots[i.val]? = some (.bytes .vector128 reference) ∧
        read after reference 16 1 = .ok (numberBytes (vector128SnapshotValue original left right i).toNat 16)) →
      MemoryBelow original.nextIdentity original after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      entered.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index 69 args (vector128SavedFrame frame slots right) [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 0 args frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  apply vector128_start_checked original entered inputs outputs left right frame slots args call setup
    layout homes leftMember rightMember leftArg rightArg post
  intro locations sum lowMask highMask prepared located sumSlot lowSlot highSlot sumRead lowRead highRead
    inputReads p0 c0 a0 n0
  apply vector128_incoming_pair original.nextIdentity entered prepared inputs outputs
    (vector128SavedFrame frame slots right) (.root (some (.address right))) slots rfl args c0 enteredWF homes a0
    (vector128SnapshotValue original left right 5) (vector128SnapshotValue original left right 6)
    (halfSum (inputHalf original left 0) (inputHalf original right 0))
    lowMask highMask lowSlot highSlot lowRead highRead post
  intro lowIncoming highIncoming incoming lowIncomingSlot highIncomingSlot lowIncomingRead highIncomingRead
    keptIncoming p1 c1 a1 n1
  apply vector128_correction_pair original.nextIdentity entered incoming inputs outputs
    (vector128SavedFrame frame slots right) (.root (some (.address right))) slots rfl args c1 enteredWF homes a1
    (halfSum (inputHalf original left 0) (inputHalf original right 0))
    (vector128SnapshotValue original left right 4)
    (vector128SnapshotValue original left right 7) (vector128SnapshotValue original left right 8)
    sum lowIncoming highIncoming sumSlot lowIncomingSlot highIncomingSlot
    (keptIncoming 4 (by decide) sum _ sumSlot sumRead) lowIncomingRead highIncomingRead post
  intro lowResult highResult after lowResultSlot highResultSlot lowResultRead highResultRead keptResult p2 c2 a2 n2
  have earlier : ∀ i, i < 7 → ∀ reference bytes,
      slots[i]? = some (.bytes .vector128 reference) →
      read prepared reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes := by
    intro i bound reference bytes slot loaded
    exact keptResult i (by omega) reference bytes slot (keptIncoming i bound reference bytes slot loaded)
  have snapshots : ∀ i : Fin 11, ∃ reference,
      slots[i.val]? = some (.bytes .vector128 reference) ∧
      read after reference 16 1 = .ok (numberBytes (vector128SnapshotValue original left right i).toNat 16) := by
    intro i
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
        i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨locations 0, located 0, earlier 0 (by decide) _ _ (located 0) (inputReads 0)⟩
    · exact ⟨locations 1, located 1, earlier 1 (by decide) _ _ (located 1) (inputReads 1)⟩
    · exact ⟨locations 2, located 2, earlier 2 (by decide) _ _ (located 2) (inputReads 2)⟩
    · exact ⟨locations 3, located 3, earlier 3 (by decide) _ _ (located 3) (inputReads 3)⟩
    · exact ⟨sum, sumSlot, earlier 4 (by decide) _ _ sumSlot sumRead⟩
    · exact ⟨lowMask, lowSlot, earlier 5 (by decide) _ _ lowSlot lowRead⟩
    · exact ⟨highMask, highSlot, earlier 6 (by decide) _ _ highSlot highRead⟩
    · exact ⟨lowIncoming, lowIncomingSlot, keptResult 7 (by decide) _ _ lowIncomingSlot lowIncomingRead⟩
    · exact ⟨highIncoming, highIncomingSlot, keptResult 8 (by decide) _ _ highIncomingSlot highIncomingRead⟩
    · exact ⟨lowResult, lowResultSlot, lowResultRead⟩
    · exact ⟨highResult, highResultSlot, highResultRead⟩
  exact continuation after snapshots (p0.trans (p1.trans p2)) c2 a2 (Nat.le_trans n0 (Nat.le_trans n1 n2))

#print axioms vector128_snapshots_checked
end UInt256Proof.Add.Safety
