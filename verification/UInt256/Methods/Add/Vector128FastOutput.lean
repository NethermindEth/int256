import CIL.Safety.Equations
import CIL.Safety.ReturnMemory
import UInt256.Methods.Add.Vector128Decision

namespace UInt256Proof.Add.Safety
def fastOutputCode (adv : Bool) : List CIL.Op := if adv then [
.feature .advSimd,
.brnonzero 215,
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.unsupported "Unreachable under selected profile",
.local 7,
.const32 1,
.intrinsic (.vector (.extract64 128)) 2,
.const32 0,
.convI8,
.gtu,
.ret (some .unsigned8)
] else [
.feature .advSimd,
.brnonzero 215,
.arg 2,
.memory .asRef,
.dup,
.local 10,
.memory .store128,
.const32 1,
.memory (.add 16 true),
.local 11,
.memory .store128,
.local 7,
.const32 1,
.intrinsic (.vector (.extract64 128)) 2,
.const32 0,
.convI8,
.gtu,
.ret (some .unsigned8)
]
end UInt256Proof.Add.Safety
namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- The fast suffix returns the saved high-lane carry bit and retires its frame. -/
theorem vector128_fast_return (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (leadingLength : leading.length = 204)
    (code : body.code = leading ++ fastOutputCode body.profile.advSimd ++ tail) (returns : body.returnsValue = true) (memory : Memory) (frame : Frame) (args : List Value)
    (home : Reference) (mask : BitVec 128)
    (slot : frame.locals[7]? = some (.bytes .vector128 home))
    (loaded : read memory home 16 1 = .ok (numberBytes mask.toNat 16)) :
    run program 7 method 215 args frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if CIL.Vector.lane64 mask 1 > BitVec.ofNat 64 0 then 1 else 0))]) := by
  have load := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 mask) mask.toNat rfl slot loaded
  cases selected : body.profile.advSimd <;> iterate 6
    apply Eq.trans
    · apply run_next found (by simp [code, List.getElem?_append, leadingLength, fastOutputCode, selected]; rfl)
      first
      | exact load _ _
      | (simp (config := { implicitDefEqProofs := false })
          [localResult, checkedIntrinsic, step, cil_guard, observerCount, selected, pureArity, scalars, CIL.step.eq_def, CIL.binary,
            CIL.Intrinsic.available, CIL.Vector.intrinsic_extract128,
            checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
         first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)
  all_goals have fetched : body.code[221]? = some (.ret (some .unsigned8)) := by simp [code, List.getElem?_append, leadingLength, fastOutputCode, selected]
  all_goals by_cases carry : CIL.Vector.lane64 mask 1 > BitVec.ofNat 64 0
  all_goals simp [run, found, fetched, returns, step, cil_guard, observerCount, checkedValue, numericValue, CIL.NarrowKind.extend, carry,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms vector128_fast_return
end UInt256Proof.Add.Safety

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def vector128FastOutputStart (body : CIL.Method) : Nat := if body.profile.advSimd then 215 else 206

/-- SSE writes the saved result halves on the fast path; ARM has already written them. -/
theorem vector128_fast_output (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (leadingLength : leading.length = 204)
    (code : body.code = leading ++ fastOutputCode body.profile.advSimd ++ tail) (original entered current : Memory)
    (inputs outputs : List Reference) (output : Reference) (frame : Frame) (args : List Value)
    (call : CallingConditions program original inputs outputs)
    (currentCall : CallingConditions program current inputs outputs)
    (member : output ∈ outputs) (authority : AccessBelow entered.nextIdentity entered current)
    (argument : args[2]? = some (.reference (.address output)))
    (low high : BitVec 128) (lowHome highHome : Reference)
    (lowSlot : frame.locals[10]? = some (.bytes .vector128 lowHome))
    (highSlot : frame.locals[11]? = some (.bytes .vector128 highHome))
    (highBound : original.nextIdentity ≤ highHome.allocation)
    (lowRead : read current lowHome 16 1 = .ok (numberBytes low.toNat 16))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (earlyRead : body.profile.advSimd = true →
      read current output 16 1 = .ok (numberBytes low.toNat 16) ∧
      read current { output with offset := output.offset + 16 } 16 1 = .ok (numberBytes high.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      (read after output 16 1 = .ok (numberBytes low.toNat 16) ∧
        read after { output with offset := output.offset + 16 } 16 1 = .ok (numberBytes high.toNat 16)) →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      (∀ id offset, OutsideOutput output id offset → after.cells id offset = current.cells id offset) →
      (∀ reference width alignment bytes, original.nextIdentity ≤ reference.allocation →
        read current reference width alignment = .ok bytes → read after reference width alignment = .ok bytes) →
      current.nextIdentity ≤ after.nextIdentity →
      ∃ fuel result returned,
        run program fuel method 215 args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (vector128FastOutputStart body) args frame [] current =
        .ok (result, returned) ∧ post result returned := by
  cases selected : body.profile.advSimd
  case true =>
    have disabled : body.profile.advSimd = true := selected
    simp only [vector128FastOutputStart, selected, ite_true]
    exact continuation current (earlyRead disabled)
      currentCall authority (by intros; rfl) (by intros; assumption) (Nat.le_refl _)
  case false =>
    obtain ⟨middle, after, firstWrite, secondWrite, firstRead, secondRead, middleCall, afterCall,
        afterAuthority, outside, privateReads, advanced⟩ :=
      output_halves_update program original entered current inputs outputs output low high
        call currentCall member authority
    have done := continuation after ⟨firstRead, secondRead⟩ afterCall afterAuthority outside
      (fun reference width alignment bytes bound loaded => (privateReads reference width alignment bytes bound loaded).2) advanced
    have loadLow := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 low) low.toNat rfl lowSlot lowRead
    have loadHigh := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 high) high.toNat rfl highSlot
      (privateReads highHome 16 1 _ highBound highRead).1
    have formed := currentCall.output_formed member
    have address := middleCall.output_half_address member 1
    simp only [Fin.val_one, Nat.mul_one] at address
    simp only [vector128FastOutputStart, selected, Bool.false_eq_true, ite_false]
    all_goals repeat' first
      | exact done
      | (apply run_next_exists post found (by simp [code, List.getElem?_append, leadingLength, fastOutputCode, selected]; rfl)
         first
         | exact loadLow _ _
         | exact loadHigh _ _
         | (simp (config := { implicitDefEqProofs := false })
             [localResult, step, cil_guard, observerCount, argument, checkedValue, formValue, formed, staticInstruction, memoryInstruction,
               storeValue, referenceAt, firstWrite, secondWrite, address, CIL.offsetValue,
               checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

/-- Follow the actual fast-path feature guard before selecting output stores. -/
theorem vector128_fast_output_dispatch (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (leadingLength : leading.length = 204)
    (code : body.code = leading ++ fastOutputCode body.profile.advSimd ++ tail) (memory : Memory) (frame : Frame) (args : List Value)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method (vector128FastOutputStart body) args frame [] memory =
        .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 204 args frame [] memory =
        .ok (result, returned) ∧ post result returned := by
  cases selected : body.profile.advSimd <;> simp only [vector128FastOutputStart, selected, Bool.false_eq_true, ite_false, ite_true] at continuation ⊢
  all_goals repeat' first
    | exact continuation
    | (apply run_next_exists post found (by simp [code, List.getElem?_append, leadingLength, fastOutputCode, selected]; rfl)
       simp (config := { implicitDefEqProofs := false })
         [localResult, checkedIntrinsic, step, cil_guard, observerCount, selected, pureArity, scalars, CIL.step.eq_def, CIL.FeatureProfile.evaluate,
           numericValue, checkedValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

#print axioms vector128_fast_output
#print axioms vector128_fast_output_dispatch
end UInt256Proof.Add.Safety
