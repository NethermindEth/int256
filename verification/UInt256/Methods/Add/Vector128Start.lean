import CIL.Safety.SymbolicExecution
import CIL.StepEquations
import CIL.Safety.Equations
import UInt256.Methods.AddSubtract.Vector128Inputs

/-!
Vector128 addition from helper entry to its carry masks: save the operand halves, add both
lanes and compare each lane sum with its left operand.
-/

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def vector128AddPrefix : List CIL.Op := [
  .arg 0, .memory .asRef, .memory .asRef, .arg 1, .memory .asRef, .memory .asRef, .setLocal 0,
  .dup, .memory .load128, .setLocal 1,
  .const32 1, .memory (.add 16 true), .memory .load128, .setLocal 2,
  .local 0, .memory .load128, .setLocal 3,
  .local 0, .const32 1, .memory (.add 16 true), .memory .load128, .setLocal 4,
  .local 1, .local 3, .intrinsic (.vector (.add64 128)) 2,
  .local 2, .local 4, .intrinsic (.vector (.add64 128)) 2, .setLocal 5,
  .dup, .local 1, .intrinsic (.vector (.ltu64 128)) 2, .setLocal 6,
  .local 5, .local 2, .intrinsic (.vector (.ltu64 128)) 2, .setLocal 7]

def vector128InitialHalves (memory : Memory) (left right : Reference) (i : Fin 4) : BitVec 128 :=
  if i = 0 then inputHalf memory left 0 else if i = 1 then inputHalf memory left 1
  else if i = 2 then inputHalf memory right 0 else inputHalf memory right 1
/-- Actual execution from helper entry through mask preparation. -/
theorem vector128_start_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (code : CodeAt body 0 (vector128AddPrefix))
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
  apply vector128_inputs_checked program body method specs found (code.take 22)
    (fun i => firstSeven ⟨i.val, by omega⟩) original entered inputs outputs left right frame slots
    args call setup layout homes leftMember rightMember leftArg rightArg post
  intro l0 l1 r0 r1 current s0 s1 s2 s3 read0 read1 read2 read3 preserved currentCall authority
    next
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
  have store := fun before (beforeCall : CallingConditions program before inputs outputs)
      (beforeAuthority : AccessBelow entered.nextIdentity entered before) index
      (declared : index < 7) (value : BitVec 128) =>
    vector128_local_store program body specs original.nextIdentity entered before inputs outputs
      (vector128SavedFrame frame slots right) _ slots rfl beforeCall
      (enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup) homes beforeAuthority index
      vector128ZeroSpec (firstSeven ⟨index, declared⟩) (.v128 value) value.toNat rfl
  obtain ⟨sum, summed, sumSlot, sumRead, p0, c0, a0, w0, storeSum⟩ := store current currentCall
    authority 4 (by decide) (halfSum (inputHalf original left 1) (inputHalf original right 1))
  obtain ⟨lowMask, masked, lowSlot, lowRead, p1, c1, a1, w1, storeLow⟩ := store summed c0 a0 5
    (by decide)
    (halfCarry (halfSum (inputHalf original left 0) (inputHalf original right 0))
      (inputHalf original left 0))
  obtain ⟨highMask, after, highSlot, highRead, p2, c2, a2, w2, storeHigh⟩ := store masked c1 a1 6
    (by decide)
    (halfCarry (halfSum (inputHalf original left 1) (inputHalf original right 1))
      (inputHalf original left 1))
  have earlier := fun before after i j (lower : i < j) source target sourceSlot targetSlot =>
    vector128_prior_read specs entered before after _ slots homes i j lower source target
      sourceSlot targetSlot
  have load := fun memory home (value : BitVec 128) index
      (slot : slots[index]? = some (.bytes .vector128 home))
      (loaded : read memory home 16 1 = .ok (numberBytes value.toNat 16)) pc stack =>
    step_load_numeric_local (body := body) (args := args) (pc := pc) (stack := stack)
      (frame := vector128SavedFrame frame slots right) (index := index + 1)
      .vector128 (.v128 value) value.toNat rfl slot loaded
  have loadLeftLow := load current l0 _ 0 s0 read0
  have loadLeftHigh := load current l1 _ 1 s1 read1
  have loadRightLow := load current r0 _ 2 s2 read2
  have loadRightHigh := load current r1 _ 3 s3 read3
  have reloadLeftLow := load summed l0 _ 0 s0
    (earlier _ _ 0 4 (by decide) _ _ s0 sumSlot _ _ w0 read0)
  have loadSum := load masked sum _ 4 sumSlot
    (earlier _ _ 4 5 (by decide) _ _ sumSlot lowSlot _ _ w1 sumRead)
  have reloadLeftHigh := load masked l1 _ 1 s1 (earlier _ _ 1 5 (by decide) _ _ s1 lowSlot _ _ w1
    (earlier _ _ 1 4 (by decide) _ _ s1 sumSlot _ _ w0 read1))
  have done := continuation locations sum lowMask highMask after located sumSlot lowSlot highSlot
    (earlier _ _ 4 6 (by decide) _ _ sumSlot highSlot _ _ w2
      (earlier _ _ 4 5 (by decide) _ _ sumSlot lowSlot _ _ w1 sumRead))
    (earlier _ _ 5 6 (by decide) _ _ lowSlot highSlot _ _ w2 lowRead) highRead
    (fun i => earlier _ _ i 6 (by omega) _ _ (located i) highSlot _ _ w2
      (earlier _ _ i 5 (by omega) _ _ (located i) lowSlot _ _ w1
        (earlier _ _ i 4 i.isLt _ _ (located i) sumSlot _ _ w0 (readable i))))
    (preserved.trans (p0.trans (p1.trans p2))) c2 a2
    (Nat.le_trans next (Nat.le_trans (write_extends_allocations _ _ _ _ _ w0).next
      (Nat.le_trans (write_extends_allocations _ _ _ _ _ w1).next
        (write_extends_allocations _ _ _ _ _ w2).next)))
  cil_contract_steps [found, code, loadLeftLow, loadLeftHigh, loadRightLow, loadRightHigh,
    reloadLeftLow, loadSum, reloadLeftHigh, storeSum, storeLow, storeHigh,
    CIL.Vector.intrinsic_add128, CIL.Vector.intrinsic_lt128, halfSum, halfCarry] until done

end UInt256Proof.Add.Safety
