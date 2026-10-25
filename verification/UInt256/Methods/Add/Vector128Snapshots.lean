import CIL.Safety.SymbolicExecution
import UInt256.Methods.Add.Vector128Start
import UInt256.Methods.AddSubtract.Vector128Incoming

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def correctionCode : List CIL.Op := [.local 8, .intrinsic (.vector (.sub64 128)) 2, .setLocal 10,
  .local 5, .local 9, .intrinsic (.vector (.sub64 128)) 2, .setLocal 11]
/-- Apply the incoming all-ones carry mask to either half and initialize its speculative result home using the actual extracted subtraction/store block. -/
theorem vector128_correction_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (code : CodeAt body 62 (correctionCode))
    (slotsSpec : specs[9]? = some vector128ZeroSpec ∧ specs[10]? = some vector128ZeroSpec) (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (upper : Bool) (low high incoming : BitVec 128) (sumHome incomingHome : Reference)
    (sumSlot : frame.locals[5]? = some (.bytes .vector128 sumHome))
    (incomingSlot : frame.locals[if upper then 9 else 8]? = some (.bytes .vector128 incomingHome))
    (sumRead : read current sumHome 16 1 = .ok (numberBytes high.toNat 16))
    (incomingRead : read current incomingHome 16 1 = .ok (numberBytes incoming.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[if upper then 11 else 10]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok (numberBytes (corrected128 (if upper then high else low) incoming).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (corrected128 (if upper then high else low) incoming).toNat 16) 1 = .ok after →
      ∃ fuel result returned,
        run program fuel method (if upper then 69 else 65) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (if upper then 65 else 62) args frame
        (if upper then [] else [.scalar (.v128 low)]) current = .ok (result, returned) ∧ post result returned := by
  have specified : specs[if upper then 10 else 9]? = some vector128ZeroSpec := by
    cases upper <;> exact (by first | exact slotsSpec.1 | exact slotsSpec.2)
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store program body specs boundary entered current inputs outputs frame root slots layout currentCall
      enteredWF homes authority _ vector128ZeroSpec specified
      (.v128 (corrected128 (if upper then high else low) incoming))
      (corrected128 (if upper then high else low) incoming).toNat rfl
  have actual : frame.locals[if upper then 11 else 10]? = some (.bytes .vector128 reference) := by
    cases upper <;> exact slot
  have done := continuation reference after actual loaded retained afterCall afterAuthority written
  have loadIncoming := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 incoming) incoming.toNat rfl incomingSlot incomingRead
  have loadSum := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 high) high.toNat rfl sumSlot sumRead
  cases upper <;> simp only [Bool.false_eq_true, ite_false, ite_true] at stored loadIncoming done ⊢
  all_goals
    repeat' first
      | exact done
      | (apply run_next_exists post found (by (conv => lhs; arg 2; whnf); cil_lookup [code])
         first
         | exact loadIncoming _ _
         | exact loadSum _ _
         | exact stored _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, cil_guard, observerCount, pureArity, scalars, CIL.step.eq_def, CIL.Intrinsic.available,
               CIL.Vector.intrinsic_sub128, corrected128, checkedValue, numericValue,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector128_correction_checked
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- Both speculative result stores retain the earlier operand, sum and mask snapshots. -/
theorem vector128_correction_pair (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (code : CodeAt body 62 (correctionCode))
    (slotsSpec : specs[9]? = some vector128ZeroSpec ∧ specs[10]? = some vector128ZeroSpec) (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (low high incomingLow incomingHigh : BitVec 128) (sumHome lowHome highHome : Reference)
    (sumSlot : slots[4]? = some (.bytes .vector128 sumHome))
    (lowSlot : slots[7]? = some (.bytes .vector128 lowHome))
    (highSlot : slots[8]? = some (.bytes .vector128 highHome))
    (sumRead : read current sumHome 16 1 = .ok (numberBytes high.toNat 16))
    (lowRead : read current lowHome 16 1 = .ok (numberBytes incomingLow.toNat 16))
    (highRead : read current highHome 16 1 = .ok (numberBytes incomingHigh.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ lowResult highResult after,
      slots[9]? = some (.bytes .vector128 lowResult) →
      slots[10]? = some (.bytes .vector128 highResult) →
      read after lowResult 16 1 = .ok (numberBytes (corrected128 low incomingLow).toNat 16) →
      read after highResult 16 1 = .ok (numberBytes (corrected128 high incomingHigh).toNat 16) →
      (∀ i, i < 9 → ∀ reference bytes,
        slots[i]? = some (.bytes .vector128 reference) →
        read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run program fuel method 69 args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 62 args frame [.scalar (.v128 low)] current =
        .ok (result, returned) ∧ post result returned := by
  have actualSum : frame.locals[5]? = some (.bytes .vector128 sumHome) := by
    simpa [layout] using sumSlot
  have actualLow : frame.locals[8]? = some (.bytes .vector128 lowHome) := by
    simpa [layout] using lowSlot
  have actualHigh : frame.locals[9]? = some (.bytes .vector128 highHome) := by
    simpa [layout] using highSlot
  apply vector128_correction_checked program body method specs found code slotsSpec boundary entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority false low high incomingLow sumHome lowHome actualSum actualLow sumRead lowRead post
  intro lowResult middle lowLocal lowLoaded preserved middleCall middleAuthority firstWrite
  have lowTail : slots[9]? = some (.bytes .vector128 lowResult) := by simpa [layout] using lowLocal
  have savedSum := vector128_prior_read specs entered current middle boundary slots homes 4 9 (by decide)
    sumHome lowResult sumSlot lowTail _ _ firstWrite sumRead
  have savedHigh := vector128_prior_read specs entered current middle boundary slots homes 8 9 (by decide)
    highHome lowResult highSlot lowTail _ _ firstWrite highRead
  apply vector128_correction_checked program body method specs found code slotsSpec boundary entered middle inputs outputs frame root slots layout args
    middleCall enteredWF homes middleAuthority true low high incomingHigh sumHome highHome actualSum actualHigh savedSum savedHigh post
  intro highResult after highLocal highLoaded kept afterCall afterAuthority secondWrite
  have highTail : slots[10]? = some (.bytes .vector128 highResult) := by simpa [layout] using highLocal
  have lower := vector128_prior_read specs entered middle after boundary slots homes 9 10 (by decide)
    lowResult highResult lowTail highTail _ _ secondWrite lowLoaded
  have earlier : ∀ i, i < 9 → ∀ reference bytes,
      slots[i]? = some (.bytes .vector128 reference) →
      read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes := by
    intro i bound reference bytes slot loaded
    exact vector128_prior_read specs entered middle after boundary slots homes i 10 (by omega)
      reference highResult slot highTail _ _ secondWrite
      (vector128_prior_read specs entered current middle boundary slots homes i 9 bound
        reference lowResult slot lowTail _ _ firstWrite loaded)
  exact continuation lowResult highResult after lowTail highTail lower highLoaded earlier
    (preserved.trans kept) afterCall afterAuthority
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ firstWrite).next
      (write_extends_allocations _ _ _ _ _ secondWrite).next)

#print axioms vector128_correction_pair
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector
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

/-- Complete checked execution from entry to the first output-stage instruction. -/
theorem vector128_snapshots_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body)
    (startCode : CodeAt body 0 vector128AddPrefix)
    (incomingCode : CodeAt body 0 (incomingPrefix body.profile.advSimd))
    (correctionCodeFound : CodeAt body 62 correctionCode)
    (firstEleven : ∀ i : Fin 11, specs[i.val]? = some vector128ZeroSpec)
    (sse : body.profile.advSimd = false → body.profile.sse2 = true)
    (ssse : body.profile.advSimd = false → body.profile.ssse3 = true) (original entered : Memory)
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
    (continuation : ∀ after,
      (∀ i : Fin 11, ∃ reference,
        slots[i.val]? = some (.bytes .vector128 reference) ∧
        read after reference 16 1 = .ok (numberBytes (vector128SnapshotValue original left right i).toNat 16)) →
      MemoryBelow original.nextIdentity original after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      entered.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run program fuel method 69 args (vector128SavedFrame frame slots right) [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 0 args frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  have enteredWF := enterFrame_preserves_wellFormed _ _ _ _ _ call.1.1 setup
  apply vector128_start_checked program body method specs found startCode (fun i => firstEleven ⟨i.val, by omega⟩) original entered inputs outputs left right frame slots args call setup
    layout homes leftMember rightMember leftArg rightArg post
  intro locations sum lowMask highMask prepared located sumSlot lowSlot highSlot sumRead lowRead highRead
    inputReads p0 c0 a0 n0
  apply UInt256Proof.AddSubtract.Safety.vector128_incoming_pair program body method specs found incomingCode sse ssse ⟨firstEleven 7, firstEleven 8⟩ original.nextIdentity entered prepared inputs outputs
    (vector128SavedFrame frame slots right) (.root (some (.address right))) slots rfl args c0 enteredWF homes a0
    (vector128SnapshotValue original left right 5) (vector128SnapshotValue original left right 6)
    [.scalar (.v128 (halfSum (inputHalf original left 0) (inputHalf original right 0)))]
    lowMask highMask lowSlot highSlot lowRead highRead post
  intro lowIncoming highIncoming incoming lowIncomingSlot highIncomingSlot lowIncomingRead highIncomingRead
    keptIncoming p1 c1 a1 n1
  apply vector128_correction_pair program body method specs found correctionCodeFound ⟨firstEleven 9, firstEleven 10⟩ original.nextIdentity entered incoming inputs outputs
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
