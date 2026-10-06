import UInt256.Methods.Add.Vector128Carry

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Compose lane addition and both mask stores. Every snapshot needed by the
    remaining vector path stays initialized and retains its exact value. -/
theorem vector128_prepare_checked (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (locations : Fin 4 → Reference) (values : Fin 4 → BitVec 128)
    (located : ∀ i : Fin 4, slots[i.val]? = some (.bytes .vector128 (locations i)))
    (readable : ∀ i, read current (locations i) 16 1 = .ok (numberBytes (values i).toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ sum lowMask highMask after,
      slots[4]? = some (.bytes .vector128 sum) →
      slots[5]? = some (.bytes .vector128 lowMask) →
      slots[6]? = some (.bytes .vector128 highMask) →
      read after sum 16 1 = .ok (numberBytes (halfSum (values 1) (values 3)).toNat 16) →
      read after lowMask 16 1 = .ok
        (numberBytes (halfCarry (halfSum (values 0) (values 2)) (values 0)).toNat 16) →
      read after highMask 16 1 = .ok
        (numberBytes (halfCarry (halfSum (values 1) (values 3)) (values 1)).toNat 16) →
      (∀ i, read after (locations i) 16 1 = .ok (numberBytes (values i).toNat 16)) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index 37 args frame
          [.scalar (.v128 (halfSum (values 0) (values 2)))] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 22 args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  have actual : ∀ i : Fin 4, frame.locals[i.val + 1]? = some (.bytes .vector128 (locations i)) := by
    intro i
    simpa [layout] using located i
  apply vector128_sum_checked boundary entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority locations values actual readable post
  intro sum m0 sumSlot sumRead p0 c0 a0 w0
  have sumTail : slots[4]? = some (.bytes .vector128 sum) := by simpa [layout] using sumSlot
  have reads0 : ∀ i, read m0 (locations i) 16 1 = .ok (numberBytes (values i).toNat 16) := by
    intro i
    exact vector128_prior_read entered current m0 boundary slots homes i.val 4 i.isLt
      (locations i) sum (located i) sumTail _ _ w0 (readable i)
  apply vector128_carry_checked boundary entered m0 inputs outputs frame root slots layout args c0
    enteredWF homes a0 false (halfSum (values 0) (values 2)) (halfSum (values 1) (values 3))
    (values 0) sum (locations 0) sumSlot (actual 0) sumRead (reads0 0) post
  intro lowMask m1 lowSlot lowRead p1 c1 a1 w1
  have lowTail : slots[5]? = some (.bytes .vector128 lowMask) := by simpa [layout] using lowSlot
  have sumRead1 := vector128_prior_read entered m0 m1 boundary slots homes 4 5 (by decide)
    sum lowMask sumTail lowTail _ _ w1 sumRead
  have reads1 : ∀ i, read m1 (locations i) 16 1 = .ok (numberBytes (values i).toNat 16) := by
    intro i
    exact vector128_prior_read entered m0 m1 boundary slots homes i.val 5 (by omega)
      (locations i) lowMask (located i) lowTail _ _ w1 (reads0 i)
  apply vector128_carry_checked boundary entered m1 inputs outputs frame root slots layout args c1
    enteredWF homes a1 true (halfSum (values 0) (values 2)) (halfSum (values 1) (values 3))
    (values 1) sum (locations 1) sumSlot (actual 1) sumRead1 (reads1 1) post
  intro highMask after highSlot highRead p2 c2 a2 w2
  have highTail : slots[6]? = some (.bytes .vector128 highMask) := by simpa [layout] using highSlot
  have sumFinal := vector128_prior_read entered m1 after boundary slots homes 4 6 (by decide)
    sum highMask sumTail highTail _ _ w2 sumRead1
  have lowFinal := vector128_prior_read entered m1 after boundary slots homes 5 6 (by decide)
    lowMask highMask lowTail highTail _ _ w2 lowRead
  have readsFinal : ∀ i, read after (locations i) 16 1 = .ok (numberBytes (values i).toNat 16) := by
    intro i
    exact vector128_prior_read entered m1 after boundary slots homes i.val 6 (by omega)
      (locations i) highMask (located i) highTail _ _ w2 (reads1 i)
  exact continuation sum lowMask highMask after sumTail lowTail highTail sumFinal lowFinal highRead
    readsFinal (p0.trans (p1.trans p2)) c2 a2
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ w0).next
      (Nat.le_trans (write_extends_allocations _ _ _ _ _ w1).next
        (write_extends_allocations _ _ _ _ _ w2).next))

#print axioms vector128_prepare_checked
end UInt256Proof.Add.Safety
