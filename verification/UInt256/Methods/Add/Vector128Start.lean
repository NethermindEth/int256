import UInt256.Methods.AddSubtract.Vector128Prefix
import CIL.SIMD.EvaluationLemmas

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def halfSum (a b : BitVec 128) : BitVec 128 := CIL.Vector.zip128 (· + ·) a b

/-- Compute both lane sums from the four initialized snapshots, keeping the
    lower sum on the stack and storing the upper sum in its actual private home. -/
theorem vector128_sum_checked (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (locations : Fin 4 → Reference) (values : Fin 4 → BitVec 128)
    (located : ∀ i, frame.locals[i.val + 1]? = some (.bytes .vector128 (locations i)))
    (readable : ∀ i, read current (locations i) 16 1 = .ok (numberBytes (values i).toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[5]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok (numberBytes (halfSum (values 1) (values 3)).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (halfSum (values 1) (values 3)).toNat 16) 1 = .ok after →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index 29 args frame
          [.scalar (.v128 (halfSum (values 0) (values 2)))] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 22 args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store boundary entered current inputs outputs frame root slots layout currentCall
      enteredWF homes authority 4 vector128ZeroSpec (by rfl)
      (.v128 (halfSum (values 1) (values 3))) (halfSum (values 1) (values 3)).toNat rfl
  have done := continuation reference after slot loaded retained afterCall afterAuthority written
  have load := fun (i : Fin 4) (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 (values i)) (values i).toNat rfl (located i) (readable i)
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  have profile : vector128Body.profile = Extracted.profile := by rfl
  repeat' first
    | exact done
    | (apply run_next_exists post found (by rfl)
       first
       | exact load 0 _ _
       | exact load 1 _ _
       | exact load 2 _ _
       | exact load 3 _ _
       | exact stored _ _ _
       | (simp (config := { implicitDefEqProofs := false })
           [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.Intrinsic.available,
             CIL.Vector.intrinsic_add128, halfSum, checkedValue, numericValue,
             Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_sum_checked
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def halfCarry (sum left : BitVec 128) : BitVec 128 :=
  CIL.Vector.zip128 (fun x y => CIL.Vector.mask64 (x.ult y)) sum left

/-- Both extracted carry-mask blocks compare a saved lane sum with its initial
    left operand. The lower sum remains on the stack across each private store. -/
theorem vector128_carry_checked (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary vector128Specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (upper : Bool) (low high left : BitVec 128) (sumHome leftHome : Reference)
    (sumSlot : frame.locals[5]? = some (.bytes .vector128 sumHome))
    (leftSlot : frame.locals[if upper then 2 else 1]? = some (.bytes .vector128 leftHome))
    (sumRead : read current sumHome 16 1 = .ok (numberBytes high.toNat 16))
    (leftRead : read current leftHome 16 1 = .ok (numberBytes left.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[if upper then 7 else 6]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok (numberBytes (halfCarry (if upper then high else low) left).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions Extracted.program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (halfCarry (if upper then high else low) left).toNat 16) 1 = .ok after →
      ∃ fuel result returned,
        run Extracted.program fuel vector128Index (if upper then 37 else 33) args frame
          [.scalar (.v128 low)] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index (if upper then 33 else 29) args frame
        [.scalar (.v128 low)] current = .ok (result, returned) ∧ post result returned := by
  have specified : vector128Specs[if upper then 6 else 5]? = some vector128ZeroSpec := by
    cases upper <;> rfl
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store boundary entered current inputs outputs frame root slots layout currentCall
      enteredWF homes authority _ vector128ZeroSpec specified
      (.v128 (halfCarry (if upper then high else low) left))
      (halfCarry (if upper then high else low) left).toNat rfl
  have actual : frame.locals[if upper then 7 else 6]? = some (.bytes .vector128 reference) := by
    cases upper <;> exact slot
  have done := continuation reference after actual loaded retained afterCall afterAuthority written
  have loadLeft := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 left) left.toNat rfl leftSlot leftRead
  have loadSum := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 high) high.toNat rfl sumSlot sumRead
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  have profile : vector128Body.profile = Extracted.profile := by rfl
  cases upper <;> simp only [Bool.false_eq_true, ite_false, ite_true] at stored loadLeft done ⊢
  all_goals
    repeat' first
      | exact done
      | (apply run_next_exists post found (by rfl)
         first
         | exact loadLeft _ _
         | exact loadSum _ _
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.Intrinsic.available,
               CIL.Vector.intrinsic_lt128, halfCarry, checkedValue, numericValue,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_carry_checked
end UInt256Proof.Add.Safety

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
