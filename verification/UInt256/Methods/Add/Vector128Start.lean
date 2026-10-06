import UInt256.Methods.Add.Vector128Prepared

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def vector128InitialHalves (memory : Memory) (left right : Reference) (i : Fin 4) : BitVec 128 :=
  if i = 0 then inputHalf memory left 0 else if i = 1 then inputHalf memory left 1
  else if i = 2 then inputHalf memory right 0 else inputHalf memory right 1

/-- Actual execution from helper entry through mask preparation. All arithmetic
    values refer to the original caller snapshots, before any output write. -/
theorem vector128_start_checked (original entered : Memory)
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
    (continuation : ∀ (locations : Fin 4 → Reference) sum lowMask highMask after,
      (∀ i : Fin 4, slots[i.val]? = some (.bytes .vector128 (locations i))) →
      slots[4]? = some (.bytes .vector128 sum) →
      slots[5]? = some (.bytes .vector128 lowMask) →
      slots[6]? = some (.bytes .vector128 highMask) →
      read after sum 16 1 = .ok
        (numberBytes (halfSum (inputHalf original left 1) (inputHalf original right 1)).toNat 16) →
      read after lowMask 16 1 = .ok (numberBytes
        (halfCarry (halfSum (inputHalf original left 0) (inputHalf original right 0)) (inputHalf original left 0)).toNat 16) →
      read after highMask 16 1 = .ok (numberBytes
        (halfCarry (halfSum (inputHalf original left 1) (inputHalf original right 1)) (inputHalf original left 1)).toNat 16) →
      (∀ i, read after (locations i) 16 1 = .ok
        (numberBytes (vector128InitialHalves original left right i).toNat 16)) →
      MemoryBelow original.nextIdentity original after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      entered.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index 37 args (vector128SavedFrame frame slots right)
          [.scalar (.v128 (halfSum (inputHalf original left 0) (inputHalf original right 0)))] after =
            .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 0 args frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  apply vector128_inputs_checked original entered inputs outputs left right frame slots args call setup
    layout homes leftMember rightMember leftArg rightArg post
  intro l0 l1 r0 r1 current s0 s1 s2 s3 read0 read1 read2 read3 preserved currentCall authority next
  let locations : Fin 4 → Reference := fun i =>
    if i = 0 then l0 else if i = 1 then l1 else if i = 2 then r0 else r1
  have located : ∀ i : Fin 4, slots[i.val]? = some (.bytes .vector128 (locations i)) := by
    intro i
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> simpa [locations] using (by assumption)
  have readable : ∀ i, read current (locations i) 16 1 =
      .ok (numberBytes (vector128InitialHalves original left right i).toNat 16) := by
    intro i
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simpa [locations, vector128InitialHalves] using (by assumption)
  apply vector128_prepare_checked original.nextIdentity entered current inputs outputs
    (vector128SavedFrame frame slots right) (.root (some (.address right))) slots rfl args
    currentCall (enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup) homes authority
    locations (vector128InitialHalves original left right) located readable post
  intro sum lowMask highMask after sumSlot lowSlot highSlot sumRead lowRead highRead reads kept afterCall afterAuthority advanced
  exact continuation locations sum lowMask highMask after located sumSlot lowSlot highSlot
    sumRead lowRead highRead reads (preserved.trans kept) afterCall afterAuthority (Nat.le_trans next advanced)

#print axioms vector128_start_checked
end UInt256Proof.Add.Safety
