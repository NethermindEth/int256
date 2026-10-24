import UInt256.Methods.Multiply.LeftTwoSafety
import UInt256.Methods.Multiply.FullSafety
import UInt256.Methods.Multiply.ScalarSafety
import UInt256.Methods.Multiply.SingleWord
import CIL.Safety.ScalarBranch

namespace UInt256Proof.Multiply.Entry
variable {alternative : Bool}
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls
structure Indices where
  entry : Nat
  full : Nat
  leftTwo : Nat
  bothTwo : Nat
  count : Nat
  single : Nat
  storage : Nat
  limbs : Nat
  word : Nat
def multiplyBody (profile : CIL.FeatureProfile) (indices : Indices) : CIL.Method := { profile := profile, returnsValue := false, locals := [.unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled], localKinds := [.word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64], parameterHomes := [], staticSites := [], code := [
  .arg 0,
  .fieldAt 0 8,
  .setLocal 0,
  .arg 1,
  .fieldAt 0 8,
  .setLocal 1,
  .arg 0,
  .fieldAt 16 8,
  .arg 0,
  .fieldAt 24 8,
  .bor,
  .setLocal 2,
  .arg 1,
  .fieldAt 16 8,
  .arg 1,
  .fieldAt 24 8,
  .bor,
  .setLocal 3,
  .arg 0,
  .fieldAt 8 8,
  .local 2,
  .bor,
  .setLocal 4,
  .arg 1,
  .fieldAt 8 8,
  .local 3,
  .bor,
  .setLocal 5,
  .local 4,
  .local 5,
  .bor,
  .brnonzero 46,
  .local 0,
  .local 1,
  .localAddr 7,
  .call indices.word 3,
  .setLocal 6,
  .arg 2,
  .local 7,
  .local 6,
  .const32 0,
  .convI8,
  .const32 0,
  .convI8,
  .call indices.storage 5,
  .ret,
  .local 5,
  .brnonzero 53,
  .arg 0,
  .local 1,
  .arg 2,
  .call indices.single 3,
  .ret,
  .local 4,
  .brnonzero 60,
  .arg 1,
  .local 0,
  .arg 2,
  .call indices.single 3,
  .ret,
  .local 2,
  .local 3,
  .bor,
  .brnonzero 69,
  .arg 0,
  .arg 1,
  .arg 2,
  .call indices.bothTwo 3,
  .ret,
  .local 2,
  .brnonzero 76,
  .arg 0,
  .arg 1,
  .arg 2,
  .call indices.leftTwo 3,
  .ret,
  .local 3,
  .brnonzero 83,
  .arg 1,
  .arg 0,
  .arg 2,
  .call indices.leftTwo 3,
  .ret,
  .arg 0,
  .arg 1,
  .arg 2,
  .call indices.full 3,
  .ret] }
structure Context (alternative : Bool := false) where
  indices : Indices
  profile : CIL.FeatureProfile
  program : CIL.Program
  entry : program[indices.entry]? = some (multiplyBody profile indices)
  full : program[indices.full]? = some (Full.fullBody profile indices.word indices.count indices.storage alternative)
  leftTwo : program[indices.leftTwo]? = some (LeftTwo.leftTwoBody profile indices.word indices.count indices.storage)
  bothTwo : program[indices.bothTwo]? = some (BothTwo.bothTwoBody profile indices.word indices.count indices.storage)
  count : program[indices.count]? = some (CountSafety.body profile)
  single : program[indices.single]? = some (ScalarSafety.scalarBody profile indices.word indices.storage)
  storage : ProductStorage.Contract program indices.storage
/-- Bind the scalar storage implementation without constraining shared execution proofs. -/
def scalarContext (indices : Indices) (profile : CIL.FeatureProfile) (program : CIL.Program)
    (scalar : profile.vector256Accelerated = false)
    (entry : program[indices.entry]? = some (multiplyBody profile indices))
    (full : program[indices.full]? = some (Full.fullBody profile indices.word indices.count indices.storage alternative))
    (leftTwo : program[indices.leftTwo]? = some (LeftTwo.leftTwoBody profile indices.word indices.count indices.storage))
    (bothTwo : program[indices.bothTwo]? = some (BothTwo.bothTwoBody profile indices.word indices.count indices.storage))
    (count : program[indices.count]? = some (CountSafety.body profile))
    (single : program[indices.single]? = some (ScalarSafety.scalarBody profile indices.word indices.storage))
    (storage : program[indices.storage]? = some (ProductStorage.body profile indices.limbs))
    (limbs : program[indices.limbs]? = some (LimbStorage.body profile)) : Context alternative :=
  ⟨indices, profile, program, entry, full, leftTwo, bothTwo, count, single,
    ProductStorage.scalar_contract profile scalar program indices.storage indices.limbs storage limbs⟩
def productArgs (left right output : Reference) : List Value :=
  [.reference (.address left), .reference (.address right), .reference (.address output)]
abbrev ProductResult := BothTwo.ProductResult
end UInt256Proof.Multiply.Entry
namespace UInt256Proof.Multiply.Entry
variable {alternative : Bool}
open CIL.Safety UInt256Model.Safety
theorem multiply_frame_setup (ctx : Context alternative) (memory : Memory) (left right output : Reference)
    (call : CallingConditions ctx.program memory [left, right] [output]) :
    ∃ frame entered,
      enterFrame (multiplyBody ctx.profile ctx.indices) (productArgs left right output) memory = .ok (frame, entered) ∧
      WritableHomes entered memory.nextIdentity (multiplyBody ctx.profile ctx.indices).localKinds frame.locals ∧
      entered.WellFormed ∧
      PrivateWords ctx.program memory entered entered [left, right] [output] frame (fun _ => none) := by
  have kinds : (multiplyBody ctx.profile ctx.indices).localKinds = List.replicate 8 CIL.LocalKind.word64 := by rfl
  obtain ⟨frame, entered, setup, homes, _, wf⟩ := unknown_frame_setup (multiplyBody ctx.profile ctx.indices)
    (by rfl) (by simp [kinds]) (by rfl) (by rfl) (by rfl) memory (productArgs left right output) call.1.1
  exact ⟨frame, entered, setup, homes, wf, PrivateWords.initial call setup⟩

def multiplyLowInputs (original : Memory) (left right : Reference) :=
  rememberWord (rememberWord (fun _ => none) 0 (inputLimb original left 0)) 1 (inputLimb original right 0)

theorem multiply_low_inputs (ctx : Context alternative) (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions ctx.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (multiplyBody ctx.profile ctx.indices).localKinds frame.locals)
    (state : PrivateWords ctx.program original entered current [left, right] [output] frame (fun _ => none))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords ctx.program original entered after [left, right] [output] frame
        (multiplyLowInputs original left right) →
      ∃ fuel final returned,
        run ctx.program fuel ctx.indices.entry 6 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run ctx.program fuel ctx.indices.entry 0 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have found : ctx.program[ctx.indices.entry]? = some (multiplyBody ctx.profile ctx.indices) := ctx.entry
  apply run_input_to_local (argument := 0) (target := 0) state originalCall enteredWF homes left (by simp) 0
    (by rfl) (by rfl) found (by rfl) (by rfl) (by rfl) post
  intro after afterState
  apply run_input_to_local (argument := 1) (target := 1) afterState originalCall enteredWF homes right (by simp) 0
    (by rfl) (by rfl) found (by rfl) (by rfl) (by rfl) post
  exact continuation

#print axioms multiply_frame_setup
#print axioms multiply_low_inputs
end UInt256Proof.Multiply.Entry

namespace UInt256Proof.Multiply.Entry
variable {alternative : Bool}
open CIL.Safety UInt256Model.Safety

def inputUpper (memory : Memory) (input : Reference) :=
  inputLimb memory input 2 ||| inputLimb memory input 3

theorem multiply_upper_mask (ctx : Context alternative) (rightSide : Bool)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (known : Nat → Option (BitVec 64))
    (originalCall : CallingConditions ctx.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (multiplyBody ctx.profile ctx.indices).localKinds frame.locals)
    (state : PrivateWords ctx.program original entered current [left, right] [output] frame known)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords ctx.program original entered after [left, right] [output] frame
        (rememberWord known (if rightSide then 3 else 2) (inputUpper original (if rightSide then right else left))) →
      ∃ fuel final returned,
        run ctx.program fuel ctx.indices.entry (if rightSide then 18 else 12)
          (productArgs left right output) frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run ctx.program fuel ctx.indices.entry (if rightSide then 12 else 6)
        (productArgs left right output) frame [] current = .ok (final, returned) ∧ post final returned := by
  let input := if rightSide then right else left
  let pc := if rightSide then 12 else 6
  let index := if rightSide then 3 else 2
  have member : input ∈ [left, right] := by cases rightSide <;> simp [input]
  have found : ctx.program[ctx.indices.entry]? = some (multiplyBody ctx.profile ctx.indices) := ctx.entry
  have formed := state.call.input_formed member
  have reading2 := state.input_field originalCall input member 2
  have reading3 := state.input_field originalCall input member 3
  simp only [CIL.fin_val_three, Nat.reduceMul] at reading3
  obtain ⟨after, stored, next⟩ := state.store enteredWF homes index (by cases rightSide <;> rfl)
    (inputUpper original input) (pc + 5) (productArgs left right output) [] (body := (multiplyBody ctx.profile ctx.indices))
  cases rightSide <;> dsimp [input, pc, index] at formed reading2 reading3 stored next continuation ⊢
  all_goals
    iterate 5
      apply run_next_exists post found (by rfl)
      simp (config := { implicitDefEqProofs := false })
        [step, cil_guard, observerCount, pureArity, productArgs, checkedValue, numericValue, formValue, formed, reading2, reading3,
          checkedAt, scalars, CIL.step.eq_def, CIL.binary, Except.mapError,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    exact run_next_exists post found (by rfl) stored (continuation after next)

def inputTail (memory : Memory) (input : Reference) :=
  inputLimb memory input 1 ||| inputUpper memory input

theorem multiply_tail_mask (ctx : Context alternative) (rightSide : Bool)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (known : Nat → Option (BitVec 64))
    (originalCall : CallingConditions ctx.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (multiplyBody ctx.profile ctx.indices).localKinds frame.locals)
    (state : PrivateWords ctx.program original entered current [left, right] [output] frame known)
    (knownUpper : known (if rightSide then 3 else 2) = some (inputUpper original (if rightSide then right else left)))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords ctx.program original entered after [left, right] [output] frame
        (rememberWord known (if rightSide then 5 else 4) (inputTail original (if rightSide then right else left))) →
      ∃ fuel final returned,
        run ctx.program fuel ctx.indices.entry (if rightSide then 28 else 23)
          (productArgs left right output) frame [] after = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run ctx.program fuel ctx.indices.entry (if rightSide then 23 else 18)
        (productArgs left right output) frame [] current = .ok (final, returned) ∧ post final returned := by
  let input := if rightSide then right else left
  let pc := if rightSide then 23 else 18
  let index := if rightSide then 5 else 4
  have member : input ∈ [left, right] := by cases rightSide <;> simp [input]
  have found : ctx.program[ctx.indices.entry]? = some (multiplyBody ctx.profile ctx.indices) := ctx.entry
  have formed := state.call.input_formed member
  have reading := state.input_field originalCall input member 1
  have loadUpper := fun (pc : Nat) (stack : List Value) => state.snapshots.load
    (body := (multiplyBody ctx.profile ctx.indices)) (args := productArgs left right output) (pc := pc) (stack := stack)
    (inputUpper original input) knownUpper
  obtain ⟨after, stored, next⟩ := state.store enteredWF homes index (by cases rightSide <;> rfl)
    (inputTail original input) (pc + 4) (productArgs left right output) [] (body := (multiplyBody ctx.profile ctx.indices))
  cases rightSide <;> dsimp [input, pc, index] at formed reading loadUpper stored next continuation ⊢
  all_goals
    iterate 4
      apply run_next_exists post found (by rfl)
      first
      | exact loadUpper _ _
      | simp (config := { implicitDefEqProofs := false })
          [step, cil_guard, observerCount, pureArity, productArgs, checkedValue, numericValue, formValue, formed, reading,
            checkedAt, scalars, CIL.step.eq_def, CIL.binary, Except.mapError,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    exact run_next_exists post found (by rfl) stored (continuation after next)

#print axioms multiply_upper_mask
#print axioms multiply_tail_mask
end UInt256Proof.Multiply.Entry

namespace UInt256Proof.Multiply.Entry
variable {alternative : Bool}
open CIL.Safety UInt256Model.Safety

def multiplyUpperInputs (original : Memory) (left right : Reference) :=
  rememberWord (rememberWord (multiplyLowInputs original left right)
    2 (inputUpper original left)) 3 (inputUpper original right)

def multiplyInputs (original : Memory) (left right : Reference) :=
  rememberWord (rememberWord (multiplyUpperInputs original left right)
    4 (inputTail original left)) 5 (inputTail original right)

theorem multiply_prepare (ctx : Context alternative) (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions ctx.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity (multiplyBody ctx.profile ctx.indices).localKinds frame.locals)
    (state : PrivateWords ctx.program original entered current [left, right] [output] frame (fun _ => none))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords ctx.program original entered after [left, right] [output] frame
        (multiplyInputs original left right) →
      ∃ fuel final returned,
        run ctx.program fuel ctx.indices.entry 28 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run ctx.program fuel ctx.indices.entry 0 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  apply multiply_low_inputs ctx original entered current left right output frame originalCall enteredWF homes state post
  intro m0 state0
  apply multiply_upper_mask ctx false original entered m0 left right output frame _ originalCall enteredWF homes state0 post
  intro m1 state1
  apply multiply_upper_mask ctx true original entered m1 left right output frame _ originalCall enteredWF homes state1 post
  intro m2 state2
  apply multiply_tail_mask ctx false original entered m2 left right output frame _ originalCall enteredWF homes state2 (by rfl) post
  intro m3 state3
  apply multiply_tail_mask ctx true original entered m3 left right output frame _ originalCall enteredWF homes state3 (by rfl) post
  exact continuation

#print axioms multiply_prepare
end UInt256Proof.Multiply.Entry

namespace UInt256Proof.Multiply.Entry
variable {alternative : Bool}
open CIL.Safety UInt256Model.Safety

theorem input_upper_zero (memory : Memory) (input : Reference)
    (zero : inputUpper memory input = 0) :
    inputLimb memory input 2 = 0 ∧ inputLimb memory input 3 = 0 :=
  BitVec.or_eq_zero_iff.mp zero

theorem input_tail_single (memory : Memory) (input : Reference)
    (zero : inputTail memory input = 0) :
    inputValue memory input = BitVec.ofNat 256 (inputLimb memory input 0).toNat := by
  have limbs := singleWord_eq (inputLimb memory input) zero
  exact (input_limbs_value memory input).symm.trans
    ((congrArg UInt256Model.value limbs.symm).trans (singleWord_value (inputLimb memory input 0)))

theorem small_product_value (memory : Memory) (left right : Reference)
    (leftSmall : inputTail memory left = 0) (rightSmall : inputTail memory right = 0) :
    BitVec.ofNat 256 ((lowProduct (inputLimb memory left 0) (inputLimb memory right 0)).toNat +
      (highProduct (inputLimb memory left 0) (inputLimb memory right 0)).toNat * 2^64) =
      inputValue memory left * inputValue memory right := by
  rw [input_tail_single memory left leftSmall, input_tail_single memory right rightSmall]
  rw [← BitVec.ofNat_mul]
  apply congrArg (BitVec.ofNat 256)
  rw [Nat.mul_comm (highProduct (inputLimb memory left 0) (inputLimb memory right 0)).toNat]
  exact product_decomposition (inputLimb memory left 0) (inputLimb memory right 0)

#print axioms input_upper_zero
#print axioms input_tail_single
#print axioms small_product_value
end UInt256Proof.Multiply.Entry



