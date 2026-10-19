import UInt256.Methods.Add.ARMLanes.Incoming
import UInt256.Methods.Add.Vector128Start

namespace UInt256Proof.Add.ARMLanes
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety UInt256Proof.Add.SSEShapes

/-- The permuted lane sums and mask stores, keeping the four operand homes readable. -/
theorem lanes_prepare_full (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (tail : List CIL.Op) (code : body.code = lanesPrefix ++ tail)
    (firstSeven : ∀ i : Fin 7, specs[i.val]? = some vector128ZeroSpec)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (locations : Fin 4 → Reference) (values : Fin 4 → BitVec 128)
    (located : ∀ i : Fin 4, slots[i.val]? = some (.bytes .vector128 (locations i)))
    (readable : ∀ i, read current (locations i) 16 1 = .ok (numberBytes (values i).toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ sum lowMask highMask after,
      slots[4]? = some (.bytes .vector128 sum) →
      slots[5]? = some (.bytes .vector128 lowMask) →
      slots[6]? = some (.bytes .vector128 highMask) →
      read after sum 16 1 = .ok (numberBytes (halfSum (values 3) (values 0)).toNat 16) →
      read after lowMask 16 1 = .ok
        (numberBytes (halfCarry (halfSum (values 1) (values 2)) (values 1)).toNat 16) →
      read after highMask 16 1 = .ok
        (numberBytes (halfCarry (halfSum (values 3) (values 0)) (values 3)).toNat 16) →
      (∀ i, read after (locations i) 16 1 = .ok (numberBytes (values i).toNat 16)) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run program fuel method 37 args frame
          [.scalar (.v128 (halfSum (values 1) (values 2)))] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 22 args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  have actual : ∀ i : Fin 4, frame.locals[i.val + 1]? = some (.bytes .vector128 (locations i)) := by
    intro i
    simpa [layout] using located i
  apply lanes_sum program body method specs found tail code firstSeven boundary entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority locations values actual readable post
  intro sum m0 sumSlot sumRead p0 c0 a0 w0
  have sumTail : slots[4]? = some (.bytes .vector128 sum) := by simpa [layout] using sumSlot
  have reads0 : ∀ i, read m0 (locations i) 16 1 = .ok (numberBytes (values i).toNat 16) := by
    intro i
    exact vector128_prior_read specs entered current m0 boundary slots homes i.val 4 i.isLt
      (locations i) sum (located i) sumTail _ _ w0 (readable i)
  apply lanes_carry program body method specs found tail code firstSeven boundary entered m0 inputs outputs frame root slots layout args c0
    enteredWF homes a0 false (halfSum (values 1) (values 2)) (halfSum (values 3) (values 0))
    (values 1) sum (locations 1) sumSlot (actual 1) sumRead (reads0 1) post
  intro lowMask m1 lowSlot lowRead p1 c1 a1 w1
  have lowTail : slots[5]? = some (.bytes .vector128 lowMask) := by simpa [layout] using lowSlot
  have sumRead1 := vector128_prior_read specs entered m0 m1 boundary slots homes 4 5 (by decide)
    sum lowMask sumTail lowTail _ _ w1 sumRead
  have reads1 : ∀ i, read m1 (locations i) 16 1 = .ok (numberBytes (values i).toNat 16) := by
    intro i
    exact vector128_prior_read specs entered m0 m1 boundary slots homes i.val 5 (by omega)
      (locations i) lowMask (located i) lowTail _ _ w1 (reads0 i)
  apply lanes_carry program body method specs found tail code firstSeven boundary entered m1 inputs outputs frame root slots layout args c1
    enteredWF homes a1 true (halfSum (values 1) (values 2)) (halfSum (values 3) (values 0))
    (values 3) sum (locations 3) sumSlot (actual 3) sumRead1 (reads1 3) post
  intro highMask after highSlot highRead p2 c2 a2 w2
  have highTail : slots[6]? = some (.bytes .vector128 highMask) := by simpa [layout] using highSlot
  have sumFinal := vector128_prior_read specs entered m1 after boundary slots homes 4 6 (by decide)
    sum highMask sumTail highTail _ _ w2 sumRead1
  have lowFinal := vector128_prior_read specs entered m1 after boundary slots homes 5 6 (by decide)
    lowMask highMask lowTail highTail _ _ w2 lowRead
  have reads2 : ∀ i, read after (locations i) 16 1 = .ok (numberBytes (values i).toNat 16) := by
    intro i
    exact vector128_prior_read specs entered m1 after boundary slots homes i.val 6 (by omega)
      (locations i) highMask (located i) highTail _ _ w2 (reads1 i)
  exact continuation sum lowMask highMask after sumTail lowTail highTail sumFinal lowFinal highRead reads2
    (p0.trans (p1.trans p2)) c2 a2
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ w0).next
      (Nat.le_trans (write_extends_allocations _ _ _ _ _ w1).next
        (write_extends_allocations _ _ _ _ _ w2).next))

/-- Entry through the permuted start, exposing every saved home at the incoming-mask boundary. -/
theorem lanes_start_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (tail : List CIL.Op) (code : body.code = lanesPrefix ++ tail)
    (firstSeven : ∀ i : Fin 7, specs[i.val]? = some vector128ZeroSpec)
    (original entered : Memory)
    (inputs outputs : List Reference) (left right : Reference)
    (frame : Frame) (slots : List LocalSlot) (args : List Value)
    (call : CallingConditions program original inputs outputs)
    (setup : enterFrame body args original = .ok (frame, entered))
    (layout : frame.locals = .root (some .null) :: slots)
    (homes : NumericHomes entered original.nextIdentity specs slots)
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
        (numberBytes (lanesHalves original left right i).toNat 16)) →
      MemoryBelow original.nextIdentity original after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      entered.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run program fuel method 37 args (vector128SavedFrame frame slots right)
          [.scalar (.v128 (halfSum (inputHalf original left 0) (inputHalf original right 0)))] after =
            .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 0 args frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  apply lanes_inputs program body method specs found tail code (fun i => firstSeven ⟨i.val, by omega⟩)
    original entered inputs outputs left right frame slots args call setup layout homes leftMember rightMember
    leftArg rightArg post
  intro r1 l0 r0 l1 current s0 s1 s2 s3 read0 read1 read2 read3 preserved currentCall authority next
  let locations : Fin 4 → Reference := fun i =>
    if i = 0 then r1 else if i = 1 then l0 else if i = 2 then r0 else l1
  have located : ∀ i : Fin 4, slots[i.val]? = some (.bytes .vector128 (locations i)) := by
    intro i
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> simpa [locations] using (by assumption)
  have readable : ∀ i, read current (locations i) 16 1 =
      .ok (numberBytes (lanesHalves original left right i).toNat 16) := by
    intro i
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simpa [locations, lanesHalves] using (by assumption)
  apply lanes_prepare_full program body method specs found tail code firstSeven original.nextIdentity entered current inputs outputs
    (vector128SavedFrame frame slots right) (.root (some (.address right))) slots rfl args
    currentCall (enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup) homes authority
    locations (lanesHalves original left right) located readable post
  intro sum lowMask highMask after sumSlot lowSlot highSlot sumRead lowRead highRead reads kept afterCall afterAuthority advanced
  exact continuation locations sum lowMask highMask after located sumSlot lowSlot highSlot sumRead lowRead highRead
    reads (preserved.trans kept) afterCall afterAuthority (Nat.le_trans next advanced)

#print axioms lanes_prepare_full
#print axioms lanes_start_checked
end UInt256Proof.Add.ARMLanes
