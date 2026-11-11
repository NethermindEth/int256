import CIL.StepEquations
import CIL.Safety.Equations
import UInt256.Methods.AddSubtract.Vector128Inputs

/-!
The incoming-carry masks of Vector128 addition: each ISA shifts the low lane's carry mask into
the next lane with its own instructions, and both store the same two masks in private homes.
-/

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety CIL.Vector

def incomingPrefix (adv : Bool) : List CIL.Op := if adv then [
  .arg 0, .memory .asRef, .memory .asRef, .arg 1, .memory .asRef, .memory .asRef, .setLocal 0,
  .dup, .memory .load128, .setLocal 1,
  .const32 1, .memory (.add 16 true), .memory .load128, .setLocal 2,
  .local 0, .memory .load128, .setLocal 3,
  .local 0, .const32 1, .memory (.add 16 true), .memory .load128, .setLocal 4,
  .local 1, .local 3, .intrinsic (.vector (.add64 128)) 2,
  .local 2, .local 4, .intrinsic (.vector (.add64 128)) 2, .setLocal 5,
  .dup, .local 1, .intrinsic (.vector (.ltu64 128)) 2, .setLocal 6,
  .local 5, .local 2, .intrinsic (.vector (.ltu64 128)) 2, .setLocal 7,
  .feature .advSimd, .brzero 50,
  .intrinsic (.vector (.zero 128)) 0, .local 6, .const32 1, .intrinsic (.advSimd .extract64) 3,
  .setLocal 8,
  .local 6, .local 7, .const32 1, .intrinsic (.advSimd .extract64) 3, .setLocal 9,
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
  .arg 0, .memory .asRef, .memory .asRef, .arg 1, .memory .asRef, .memory .asRef, .setLocal 0,
  .dup, .memory .load128, .setLocal 1,
  .const32 1, .memory (.add 16 true), .memory .load128, .setLocal 2,
  .local 0, .memory .load128, .setLocal 3,
  .local 0, .const32 1, .memory (.add 16 true), .memory .load128, .setLocal 4,
  .local 1, .local 3, .intrinsic (.vector (.add64 128)) 2,
  .local 2, .local 4, .intrinsic (.vector (.add64 128)) 2, .setLocal 5,
  .dup, .local 1, .intrinsic (.vector (.ltu64 128)) 2, .setLocal 6,
  .local 5, .local 2, .intrinsic (.vector (.ltu64 128)) 2, .setLocal 7,
  .feature .advSimd, .brzero 50,
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
  .local 6, .const32 8, .intrinsic (.sse .shiftLeftBytes) 2, .setLocal 8,
  .local 7, .intrinsic (.vector (.reinterpret 128)) 1,
  .local 6, .intrinsic (.vector (.reinterpret 128)) 1,
  .const32 8, .intrinsic (.sse .alignBytes) 3, .intrinsic (.vector (.reinterpret 128)) 1,
  .setLocal 9]
/-- Both selected incoming-mask blocks preserve every earlier initialized vector home, including the initial operands, upper sum and generated masks. -/
theorem vector128_incoming_pair (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (code : CodeAt body 0 (incomingPrefix body.profile.advSimd))
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
  have store := fun before (beforeCall : CallingConditions program before inputs outputs)
      (beforeAuthority : AccessBelow entered.nextIdentity entered before) index specified
      (mask : BitVec 128) =>
    vector128_local_store program body specs boundary entered before inputs outputs frame root
      slots layout beforeCall enteredWF homes beforeAuthority index vector128ZeroSpec specified
      (.v128 mask) mask.toNat rfl
  obtain ⟨lowIncoming, middle, lowLocal, lowLoaded, preserved, middleCall, middleAuthority,
    firstWrite, storeLow⟩ := store current currentCall authority 7 slotsSpec.1 (incoming128Low low)
  obtain ⟨highIncoming, after, highLocal, highLoaded, kept, afterCall, afterAuthority,
    secondWrite, storeHigh⟩ :=
    store middle middleCall middleAuthority 8 slotsSpec.2 (incoming128High low high)
  rw [layout] at lowLocal highLocal
  have earlier := fun before after i j (lower : i < j) source target sourceSlot targetSlot =>
    vector128_prior_read specs entered before after boundary slots homes i j lower source target
      sourceSlot targetSlot
  have load := fun memory home (mask : BitVec 128)
      index (slot : slots[index]? = some (.bytes .vector128 home))
      (loaded : read memory home 16 1 = .ok (numberBytes mask.toNat 16)) pc stack =>
    step_load_numeric_local (body := body) (args := args) (pc := pc) (stack := stack)
      (frame := frame) (index := index + 1) .vector128 (.v128 mask) mask.toNat rfl
      (by rw [layout]; exact slot) loaded
  have loadLow := load current lowHome low 5 lowSlot lowRead
  have reloadLow := load middle lowHome low 5 lowSlot
    (earlier _ _ 5 7 (by decide) _ _ lowSlot lowLocal _ _ firstWrite lowRead)
  have loadHigh := load middle highHome high 6 highSlot
    (earlier _ _ 6 7 (by decide) _ _ highSlot lowLocal _ _ firstWrite highRead)
  have done := continuation lowIncoming highIncoming after lowLocal highLocal
    (earlier _ _ 7 8 (by decide) _ _ lowLocal highLocal _ _ secondWrite lowLoaded) highLoaded
    (fun i bound reference bytes slot loaded =>
      earlier _ _ i 8 (by omega) _ _ slot highLocal _ _ secondWrite
        (earlier _ _ i 7 bound _ _ slot lowLocal _ _ firstWrite loaded))
    (preserved.trans kept) afterCall afterAuthority
    (Nat.le_trans (write_extends_allocations _ _ _ _ _ firstWrite).next
      (write_extends_allocations _ _ _ _ _ secondWrite).next)
  cases selected : body.profile.advSimd <;> simp only [selected] at code
  · rw [← incoming128_sse_low] at storeLow
    rw [← incoming128_sse_high] at storeHigh
    cil_contract_steps [found, code, selected, sse selected, ssse selected, loadLow, reloadLow,
      loadHigh, storeLow, storeHigh,
      show body.profile.evaluate .advSimd = false from selected, intrinsic_sse_shift,
      intrinsic_sse_align, intrinsic_reinterpret128] until done
  · rw [← incoming128_arm_low] at storeLow
    rw [← incoming128_arm_high] at storeHigh
    cil_contract_steps 2 [found, code, show body.profile.evaluate .advSimd = true from selected]
    -- The taken feature branch leaves its target as an undecided literal comparison.
    simp only [BitVec.reduceEq, not_false_eq_true, ↓reduceIte]
    cil_contract_steps [found, code, selected, loadLow, reloadLow, loadHigh, storeLow, storeHigh,
      intrinsic_zero128, intrinsic_adv_extract] until done

end UInt256Proof.AddSubtract.Safety
