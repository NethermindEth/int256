import CIL.StepEquations
import CIL.Safety.Equations
import UInt256.Methods.AddSubtract.Vector128Inputs

namespace UInt256Proof.Add.Safety
def vector128AddPrefix : List CIL.Op := [
  .arg 0,
  .memory .asRef,
  .memory .asRef,
  .arg 1,
  .memory .asRef,
  .memory .asRef,
  .setLocal 0,
  .dup,
  .memory .load128,
  .setLocal 1,
  .const32 1,
  .memory (.add 16 true),
  .memory .load128,
  .setLocal 2,
  .local 0,
  .memory .load128,
  .setLocal 3,
  .local 0,
  .const32 1,
  .memory (.add 16 true),
  .memory .load128,
  .setLocal 4,
  .local 1,
  .local 3,
  .intrinsic (.vector (.add64 128)) 2,
  .local 2,
  .local 4,
  .intrinsic (.vector (.add64 128)) 2,
  .setLocal 5,
  .dup,
  .local 1,
  .intrinsic (.vector (.ltu64 128)) 2,
  .setLocal 6,
  .local 5,
  .local 2,
  .intrinsic (.vector (.ltu64 128)) 2,
  .setLocal 7]
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Compute both lane sums from the four initialized snapshots, keeping the lower sum on the stack and storing the upper sum in its actual private home. -/
theorem vector128_sum_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (tail : List CIL.Op) (code : body.code = vector128AddPrefix ++ tail)
    (firstSeven : ∀ i : Fin 7, specs[i.val]? = some vector128ZeroSpec)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (locations : Fin 4 → Reference) (values : Fin 4 → BitVec 128)
    (located : ∀ i, frame.locals[i.val + 1]? = some (.bytes .vector128 (locations i)))
    (readable : ∀ i, read current (locations i) 16 1 = .ok (numberBytes (values i).toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[5]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok (numberBytes (halfSum (values 1) (values 3)).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (halfSum (values 1) (values 3)).toNat 16) 1 = .ok after →
      ∃ fuel result returned,
        run program fuel method 29 args frame
          [.scalar (.v128 (halfSum (values 0) (values 2)))] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 22 args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store program body specs boundary entered current inputs outputs frame root slots layout currentCall
      enteredWF homes authority 4 vector128ZeroSpec (firstSeven 4)
      (.v128 (halfSum (values 1) (values 3))) (halfSum (values 1) (values 3)).toNat rfl
  have done := continuation reference after slot loaded retained afterCall afterAuthority written
  have load := fun (i : Fin 4) (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 (values i)) (values i).toNat rfl (located i) (readable i)

  repeat' first
    | exact done
    | (apply run_next_exists post found (by simp [code, vector128AddPrefix]; rfl)
       first
       | exact load 0 _ _
       | exact load 1 _ _
       | exact load 2 _ _
       | exact load 3 _ _
       | exact stored _ _ _
       | (simp (config := { implicitDefEqProofs := false })
           [step, checkedIntrinsic, pureArity, scalars, CIL.step.eq_def, CIL.Intrinsic.available,
             CIL.Vector.intrinsic_add128, halfSum, checkedValue, numericValue,
             Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_sum_checked
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Both extracted carry-mask blocks compare a saved lane sum with its initial left operand. -/
theorem vector128_carry_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (tail : List CIL.Op) (code : body.code = vector128AddPrefix ++ tail)
    (firstSeven : ∀ i : Fin 7, specs[i.val]? = some vector128ZeroSpec)
    (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs slots)
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
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (halfCarry (if upper then high else low) left).toNat 16) 1 = .ok after →
      ∃ fuel result returned,
        run program fuel method (if upper then 37 else 33) args frame
          [.scalar (.v128 low)] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (if upper then 33 else 29) args frame
        [.scalar (.v128 low)] current = .ok (result, returned) ∧ post result returned := by
  have specified : specs[if upper then 6 else 5]? = some vector128ZeroSpec := by
    cases upper <;> first | exact firstSeven 5 | exact firstSeven 6
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store program body specs boundary entered current inputs outputs frame root slots layout currentCall
      enteredWF homes authority _ vector128ZeroSpec specified
      (.v128 (halfCarry (if upper then high else low) left))
      (halfCarry (if upper then high else low) left).toNat rfl
  have actual : frame.locals[if upper then 7 else 6]? = some (.bytes .vector128 reference) := by
    cases upper <;> exact slot
  have done := continuation reference after actual loaded retained afterCall afterAuthority written
  have loadLeft := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 left) left.toNat rfl leftSlot leftRead
  have loadSum := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 high) high.toNat rfl sumSlot sumRead

  cases upper <;> simp only [Bool.false_eq_true, ite_false, ite_true] at stored loadLeft done ⊢
  all_goals
    repeat' first
      | exact done
      | (apply run_next_exists post found (by simp [code, vector128AddPrefix]; rfl)
         first
         | exact loadLeft _ _
         | exact loadSum _ _
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, checkedIntrinsic, pureArity, scalars, CIL.step.eq_def, CIL.Intrinsic.available,
               CIL.Vector.intrinsic_lt128, halfCarry, checkedValue, numericValue,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_carry_checked
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Compose lane addition and both mask stores. -/
theorem vector128_prepare_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (tail : List CIL.Op) (code : body.code = vector128AddPrefix ++ tail)
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
      read after sum 16 1 = .ok (numberBytes (halfSum (values 1) (values 3)).toNat 16) →
      read after lowMask 16 1 = .ok
        (numberBytes (halfCarry (halfSum (values 0) (values 2)) (values 0)).toNat 16) →
      read after highMask 16 1 = .ok
        (numberBytes (halfCarry (halfSum (values 1) (values 3)) (values 1)).toNat 16) →
      (∀ i, read after (locations i) 16 1 = .ok (numberBytes (values i).toNat 16)) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run program fuel method 37 args frame
          [.scalar (.v128 (halfSum (values 0) (values 2)))] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 22 args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  have actual : ∀ i : Fin 4, frame.locals[i.val + 1]? = some (.bytes .vector128 (locations i)) := by
    intro i
    simpa [layout] using located i
  apply vector128_sum_checked program body method specs found tail code firstSeven boundary entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority locations values actual readable post
  intro sum m0 sumSlot sumRead p0 c0 a0 w0
  have sumTail : slots[4]? = some (.bytes .vector128 sum) := by simpa [layout] using sumSlot
  have reads0 : ∀ i, read m0 (locations i) 16 1 = .ok (numberBytes (values i).toNat 16) := by
    intro i
    exact vector128_prior_read specs entered current m0 boundary slots homes i.val 4 i.isLt
      (locations i) sum (located i) sumTail _ _ w0 (readable i)
  apply vector128_carry_checked program body method specs found tail code firstSeven boundary entered m0 inputs outputs frame root slots layout args c0
    enteredWF homes a0 false (halfSum (values 0) (values 2)) (halfSum (values 1) (values 3))
    (values 0) sum (locations 0) sumSlot (actual 0) sumRead (reads0 0) post
  intro lowMask m1 lowSlot lowRead p1 c1 a1 w1
  have lowTail : slots[5]? = some (.bytes .vector128 lowMask) := by simpa [layout] using lowSlot
  have sumRead1 := vector128_prior_read specs entered m0 m1 boundary slots homes 4 5 (by decide)
    sum lowMask sumTail lowTail _ _ w1 sumRead
  have reads1 : ∀ i, read m1 (locations i) 16 1 = .ok (numberBytes (values i).toNat 16) := by
    intro i
    exact vector128_prior_read specs entered m0 m1 boundary slots homes i.val 5 (by omega)
      (locations i) lowMask (located i) lowTail _ _ w1 (reads0 i)
  apply vector128_carry_checked program body method specs found tail code firstSeven boundary entered m1 inputs outputs frame root slots layout args c1
    enteredWF homes a1 true (halfSum (values 0) (values 2)) (halfSum (values 1) (values 3))
    (values 1) sum (locations 1) sumSlot (actual 1) sumRead1 (reads1 1) post
  intro highMask after highSlot highRead p2 c2 a2 w2
  have highTail : slots[6]? = some (.bytes .vector128 highMask) := by simpa [layout] using highSlot
  have sumFinal := vector128_prior_read specs entered m1 after boundary slots homes 4 6 (by decide)
    sum highMask sumTail highTail _ _ w2 sumRead1
  have lowFinal := vector128_prior_read specs entered m1 after boundary slots homes 5 6 (by decide)
    lowMask highMask lowTail highTail _ _ w2 lowRead
  have readsFinal : ∀ i, read after (locations i) 16 1 = .ok (numberBytes (values i).toNat 16) := by
    intro i
    exact vector128_prior_read specs entered m1 after boundary slots homes i.val 6 (by omega)
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

/-- Actual execution from helper entry through mask preparation. -/
theorem vector128_start_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (tail : List CIL.Op) (code : body.code = vector128AddPrefix ++ tail)
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
        (numberBytes (vector128InitialHalves original left right i).toNat 16)) →
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
  have prefixCode : body.code = vector128PrefixCode ++ body.code.drop 22 := by rw [code]; rfl
  apply vector128_inputs_checked program body method specs found (body.code.drop 22) prefixCode
    (fun i => firstSeven ⟨i.val, by omega⟩) original entered inputs outputs left right frame slots args call setup
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
  apply vector128_prepare_checked program body method specs found tail code firstSeven original.nextIdentity entered current inputs outputs
    (vector128SavedFrame frame slots right) (.root (some (.address right))) slots rfl args
    currentCall (enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup) homes authority
    locations (vector128InitialHalves original left right) located readable post
  intro sum lowMask highMask after sumSlot lowSlot highSlot sumRead lowRead highRead reads kept afterCall afterAuthority advanced
  exact continuation locations sum lowMask highMask after located sumSlot lowSlot highSlot
    sumRead lowRead highRead reads (preserved.trans kept) afterCall afterAuthority (Nat.le_trans next advanced)

#print axioms vector128_start_checked
end UInt256Proof.Add.Safety
