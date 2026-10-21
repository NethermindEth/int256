import UInt256.Safety.DispatchEquation
import UInt256.Safety.StepEquation
import UInt256.Methods.AddSubtract.Vector128Inputs

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety CIL.Vector
def incomingPrefix (adv : Bool) : List CIL.Op := if adv then [
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
.setLocal 7,
.feature .advSimd,
.brzero 50,
.intrinsic (.vector (.zero 128)) 0,
.local 6,
.const32 1,
.intrinsic (.advSimd .extract64) 3,
.setLocal 8,
.local 6,
.local 7,
.const32 1,
.intrinsic (.advSimd .extract64) 3,
.setLocal 9,
.branch 62,
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile"
] else [
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
.setLocal 7,
.feature .advSimd,
.brzero 50,
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.local 6,
.const32 8,
.intrinsic (.sse .shiftLeftBytes) 2,
.setLocal 8,
.local 7,
.intrinsic (.vector (.reinterpret 128)) 1,
.local 6,
.intrinsic (.vector (.reinterpret 128)) 1,
.const32 8,
.intrinsic (.sse .alignBytes) 3,
.intrinsic (.vector (.reinterpret 128)) 1,
.setLocal 9
]
def incomingRaw (adv upper : Bool) (low high : BitVec 128) : BitVec 128 :=
  if adv then
    if upper then advExtract64 low high (BitVec.setWidth 8 (1 : BitVec 32)).toNat
    else advExtract64 0 low (BitVec.setWidth 8 (1 : BitVec 32)).toNat
  else
    if upper then ssseAlignBytes high low (BitVec.setWidth 8 (8 : BitVec 32)).toNat
    else sseShiftLeftBytes low (BitVec.setWidth 8 (8 : BitVec 32)).toNat

theorem incomingRaw_eq (adv upper : Bool) (low high : BitVec 128) :
    incomingRaw adv upper low high = if upper then incoming128High low high else incoming128Low low := by
  cases adv <;> cases upper
  · exact incoming128_sse_low low
  · exact incoming128_sse_high low high
  · exact incoming128_arm_low low
  · exact incoming128_arm_high low high
def incoming128Start (body : CIL.Method) (upper : Bool) : Nat :=
  (if body.profile.advSimd then (if upper then 44 else 39) else (if upper then 54 else 50))

def incoming128End (body : CIL.Method) (upper : Bool) : Nat :=
  (if body.profile.advSimd then (if upper then 49 else 44) else (if upper then 62 else 54))

/-- Follow the selected ISA's actual incoming-mask instructions and initialize its private slot. -/

theorem vector128_incoming_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (tail : List CIL.Op)
    (code : body.code = incomingPrefix body.profile.advSimd ++ tail)
    (sse : body.profile.advSimd = false → body.profile.sse2 = true)
    (ssse : body.profile.advSimd = false → body.profile.ssse3 = true)
    (slotsSpec : specs[7]? = some vector128ZeroSpec ∧ specs[8]? = some vector128ZeroSpec) (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (upper : Bool) (low high : BitVec 128) (stack : List Value) (lowHome highHome : Reference)
    (lowSlot : frame.locals[6]? = some (.bytes .vector128 lowHome))
    (highSlot : frame.locals[7]? = some (.bytes .vector128 highHome))
    (lowRead : read current lowHome 16 1 = .ok (numberBytes low.toNat 16))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[(if upper then 9 else 8)]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok
        (numberBytes (if upper then incoming128High low high else incoming128Low low).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference
        (numberBytes (if upper then incoming128High low high else incoming128Low low).toNat 16) 1 = .ok after →
      ∃ fuel result returned,
        run program fuel method (incoming128End body upper) args frame
          stack after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (incoming128Start body upper) args frame
        stack current = .ok (result, returned) ∧ post result returned := by
  have specified : specs[(if upper then 8 else 7)]? = some vector128ZeroSpec := by
    cases upper <;> exact (by first | exact slotsSpec.1 | exact slotsSpec.2)
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store program body specs boundary entered current inputs outputs frame root slots layout currentCall
      enteredWF homes authority _ vector128ZeroSpec specified
      (.v128 (if upper then incoming128High low high else incoming128Low low))
      (if upper then incoming128High low high else incoming128Low low).toNat rfl
  have actual : frame.locals[(if upper then 9 else 8)]? = some (.bytes .vector128 reference) := by
    cases upper <;> exact slot
  have done := continuation reference after actual loaded retained afterCall afterAuthority written
  have loadLow := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 low) low.toNat rfl lowSlot lowRead
  have loadHigh := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 high) high.toNat rfl highSlot highRead
  have finished : ∃ fuel result returned,
      run program fuel method (incoming128End body upper - 1) args frame
        (.scalar (.v128 (if upper then incoming128High low high else incoming128Low low)) :: stack)
        current = .ok (result, returned) ∧ post result returned := by
    cases selected : body.profile.advSimd <;> cases upper <;>
      simp only [incoming128End, selected, Bool.false_eq_true, ite_false, ite_true, Nat.reduceSub] at done ⊢
    all_goals
      apply run_next_exists post found (by simp [code, incomingPrefix, selected]; rfl)
      · exact stored _ _ _
      · exact done
  have finishedMath := finished
  rw [← incomingRaw_eq body.profile.advSimd upper low high] at finished
  cases selected : body.profile.advSimd <;> cases upper <;> simp only [Bool.false_eq_true, ite_false, ite_true] at stored finished finishedMath ⊢
  all_goals
    simp only [Nat.reduceAdd] at stored
    simp only [incomingRaw, Nat.reduceSub, incoming128Start, incoming128End, selected, Bool.false_eq_true, ite_false, ite_true] at finished finishedMath ⊢
    repeat' first
      | exact finished
      | with_reducible exact finishedMath
      | (apply run_next_exists post found (by simp [code, incomingPrefix, selected]; rfl)
         first
         | exact loadLow _ _
         | exact loadHigh _ _
         
         | (simp (config := { implicitDefEqProofs := false })
             [show (BitVec.setWidth 8 (8 : BitVec 32)).toNat = 8 from rfl, step, selected, sse, ssse, pureArity, scalars, CIL.step.eq_def, CIL.Intrinsic.available,
               CIL.Vector.intrinsic_zero128, CIL.Vector.intrinsic_adv_extract,
               CIL.Vector.intrinsic_sse_shift, CIL.Vector.intrinsic_sse_align,
               CIL.Vector.intrinsic_reinterpret128, incoming128_arm_low, incoming128_arm_high,
               incoming128_sse_low, incoming128_sse_high, checkedValue, numericValue,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

/-- The feature guard and ARM-only final jump follow the selected extraction. -/
theorem vector128_incoming_dispatch (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (tail : List CIL.Op)
    (code : body.code = incomingPrefix body.profile.advSimd ++ tail) (memory : Memory) (frame : Frame) (args stack : List Value)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method (incoming128Start body false) args frame stack memory =
        .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (37) args frame stack memory =
        .ok (result, returned) ∧ post result returned := by
  cases selected : body.profile.advSimd <;> simp only [incoming128Start, selected, Bool.false_eq_true, ite_false, ite_true] at continuation ⊢
  all_goals repeat' first
    | exact continuation
    | (apply run_next_exists post found (by simp [code, incomingPrefix, selected]; rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, selected, pureArity, scalars, CIL.step.eq_def, CIL.FeatureProfile.evaluate,
           checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

theorem vector128_incoming_join (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (tail : List CIL.Op)
    (code : body.code = incomingPrefix body.profile.advSimd ++ tail) (memory : Memory) (frame : Frame) (args stack : List Value)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method (62) args frame stack memory =
        .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (incoming128End body true) args frame stack memory =
        .ok (result, returned) ∧ post result returned := by
  cases selected : body.profile.advSimd <;> simp only [incoming128End, selected, Bool.false_eq_true, ite_false, ite_true] at continuation ⊢
  all_goals repeat' first
    | exact continuation
    | (apply run_next_exists post found (by simp [code, incomingPrefix, selected]; rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, pureArity, scalars, CIL.step.eq_def, checkedValue, numericValue,
           Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

#print axioms vector128_incoming_checked
#print axioms vector128_incoming_dispatch
#print axioms vector128_incoming_join
end UInt256Proof.AddSubtract.Safety
namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety CIL.Vector

/-- Both selected incoming-mask blocks preserve every earlier initialized vector home, including the initial operands, upper sum and generated masks. -/
theorem vector128_incoming_pair (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (tail : List CIL.Op)
    (code : body.code = incomingPrefix body.profile.advSimd ++ tail)
    (sse : body.profile.advSimd = false → body.profile.sse2 = true)
    (ssse : body.profile.advSimd = false → body.profile.ssse3 = true)
    (slotsSpec : specs[7]? = some vector128ZeroSpec ∧ specs[8]? = some vector128ZeroSpec) (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (low high : BitVec 128) (stack : List Value) (lowHome highHome : Reference)
    (lowSlot : slots[5]? = some (.bytes .vector128 lowHome))
    (highSlot : slots[6]? = some (.bytes .vector128 highHome))
    (lowRead : read current lowHome 16 1 = .ok (numberBytes low.toNat 16))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ lowIncoming highIncoming after,
      slots[7]? = some (.bytes .vector128 lowIncoming) →
      slots[8]? = some (.bytes .vector128 highIncoming) →
      read after lowIncoming 16 1 = .ok (numberBytes (incoming128Low low).toNat 16) →
      read after highIncoming 16 1 = .ok (numberBytes (incoming128High low high).toNat 16) →
      (∀ i, i < 7 → ∀ reference bytes,
        slots[i]? = some (.bytes .vector128 reference) →
        read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run program fuel method (62) args frame stack after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (37) args frame stack current =
        .ok (result, returned) ∧ post result returned := by
  have actualLow : frame.locals[6]? = some (.bytes .vector128 lowHome) := by
    simpa [layout, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lowSlot
  have actualHigh : frame.locals[7]? = some (.bytes .vector128 highHome) := by
    simpa [layout, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using highSlot
  apply vector128_incoming_dispatch program body method found tail code current frame args stack post
  apply vector128_incoming_checked program body method specs found tail code sse ssse slotsSpec boundary entered current inputs outputs frame root slots layout args
    currentCall enteredWF homes authority false low high stack lowHome highHome actualLow actualHigh lowRead highRead post
  intro lowIncoming middle lowLocal lowLoaded preserved middleCall middleAuthority firstWrite
  have lowTail : slots[7]? = some (.bytes .vector128 lowIncoming) := by simpa [layout, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using lowLocal
  have savedLow := vector128_prior_read specs entered current middle boundary slots homes (5) (7) (by omega)
    lowHome lowIncoming lowSlot lowTail _ _ firstWrite lowRead
  have savedHigh := vector128_prior_read specs entered current middle boundary slots homes (6) (7) (by omega)
    highHome lowIncoming highSlot lowTail _ _ firstWrite highRead
  apply vector128_incoming_checked program body method specs found tail code sse ssse slotsSpec boundary entered middle inputs outputs frame root slots layout args
    middleCall enteredWF homes middleAuthority true low high stack lowHome highHome actualLow actualHigh savedLow savedHigh post
  intro highIncoming after highLocal highLoaded kept afterCall afterAuthority secondWrite
  have highTail : slots[8]? = some (.bytes .vector128 highIncoming) := by simpa [layout, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using highLocal
  have lower := vector128_prior_read specs entered middle after boundary slots homes (7) (8) (by omega)
    lowIncoming highIncoming lowTail highTail _ _ secondWrite lowLoaded
  have earlier : ∀ i, i < 7 → ∀ reference bytes,
      slots[i]? = some (.bytes .vector128 reference) →
      read current reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes := by
    intro i bound reference bytes slot loaded
    exact vector128_prior_read specs entered middle after boundary slots homes i (8) (by omega)
      reference highIncoming slot highTail _ _ secondWrite
      (vector128_prior_read specs entered current middle boundary slots homes i (7) bound
        reference lowIncoming slot lowTail _ _ firstWrite loaded)
  apply vector128_incoming_join program body method found tail code after frame args stack post
  exact continuation lowIncoming highIncoming after lowTail highTail lower highLoaded earlier
    (preserved.trans kept) afterCall afterAuthority
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ firstWrite).next
      (write_extends_allocations _ _ _ _ _ secondWrite).next)

#print axioms vector128_incoming_pair
end UInt256Proof.AddSubtract.Safety
