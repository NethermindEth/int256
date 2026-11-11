import CIL.StepEquations
import CIL.Safety.Equations
import UInt256.Methods.AddSubtract.Vector128Inputs

/-!
The incoming-mask block that Vector128 addition and subtraction share: each ISA shifts the low
lane's carry or borrow mask into the next lane with its own instructions, and both store the
same two masks in private homes. The block is stated at any position and local layout.
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

/-- The incoming-mask block at `base`: locals `home + 1` and `home + 2` hold the lane masks and
    the shifted masks go to locals `home + 3` and `home + 4`. -/
def incomingCode (adv : Bool) (base home : Nat) : List CIL.Op := if adv then [
  .feature .advSimd, .brzero (base + 13),
  .intrinsic (.vector (.zero 128)) 0, .local (home + 1), .const32 1,
  .intrinsic (.advSimd .extract64) 3, .setLocal (home + 3),
  .local (home + 1), .local (home + 2), .const32 1, .intrinsic (.advSimd .extract64) 3,
  .setLocal (home + 4),
  .branch (base + 25),
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
  .feature .advSimd, .brzero (base + 13),
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
  .local (home + 1), .const32 8, .intrinsic (.sse .shiftLeftBytes) 2, .setLocal (home + 3),
  .local (home + 2), .intrinsic (.vector (.reinterpret 128)) 1,
  .local (home + 1), .intrinsic (.vector (.reinterpret 128)) 1,
  .const32 8, .intrinsic (.sse .alignBytes) 3, .intrinsic (.vector (.reinterpret 128)) 1,
  .setLocal (home + 4)]

/-- Addition's prefix ends with the shared block over its carry masks. -/
theorem incomingPrefix_block {body : CIL.Method} {adv : Bool}
    (code : CodeAt body 0 (incomingPrefix adv)) : CodeAt body 37 (incomingCode adv 37 5) := by
  cases adv <;> exact code.drop 37

/-- The selected ISA's incoming-mask instructions store both shifted masks. -/
theorem vector128_incoming_checked (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (specs : List NumericLocalSpec) (found : program[method]? = some body) (base home : Nat)
    (code : CodeAt body base (incomingCode body.profile.advSimd base home))
    (sse : body.profile.advSimd = false → body.profile.sse2 = true)
    (ssse : body.profile.advSimd = false → body.profile.ssse3 = true)
    (lowSpec : specs[home + 2]? = some vector128ZeroSpec)
    (highSpec : specs[home + 3]? = some vector128ZeroSpec)
    (boundary : Nat) (origin entered current : Memory) (inputs outputs : List Reference)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args stack : List Value)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary specs slots)
    (value : Nat → BitVec 128)
    (lowIncoming : value (home + 2) = incoming128Low (value home))
    (highIncoming : value (home + 3) = incoming128High (value home) (value (home + 1)))
    (state : VectorState program boundary origin entered current inputs outputs slots value
      (home + 2))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      VectorState program boundary origin entered after inputs outputs slots value (home + 4) →
      ∃ fuel result returned,
        run program fuel method (base + 25) args frame stack after = .ok (result, returned) ∧
          post result returned) :
    ∃ fuel result returned,
      run program fuel method base args frame stack current = .ok (result, returned) ∧
        post result returned := by
  obtain ⟨middle, lowState, storeLow⟩ :=
    state.store body specs frame root layout enteredWF homes lowSpec _ lowIncoming
  obtain ⟨after, highState, storeHigh⟩ :=
    lowState.store body specs frame root layout enteredWF homes highSpec _ highIncoming
  have loadLow := state.snapshots.load frame root layout home (by omega) body
  have reloadLow := lowState.snapshots.load frame root layout home (by omega) body
  have loadHigh := lowState.snapshots.load frame root layout (home + 1) (by omega) body
  have done := continuation after highState
  cases selected : body.profile.advSimd <;> simp only [selected] at code
  · rw [← incoming128_sse_low] at storeLow
    rw [← incoming128_sse_high] at storeHigh
    cil_contract_steps [found, code, selected, sse selected, ssse selected, loadLow, reloadLow,
      loadHigh, storeLow, storeHigh,
      show body.profile.evaluate .advSimd = false from selected, intrinsic_sse_shift,
      intrinsic_sse_align, intrinsic_reinterpret128] until done
  · rw [← incoming128_arm_low] at storeLow
    rw [← incoming128_arm_high] at storeHigh
    cil_contract_steps [found, code, selected, loadLow, reloadLow, loadHigh, storeLow, storeHigh,
      show body.profile.evaluate .advSimd = true from selected,
      intrinsic_zero128, intrinsic_adv_extract] until done

end UInt256Proof.AddSubtract.Safety
