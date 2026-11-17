import UInt256.Methods.Multiply.BothTwoSafety
import UInt256.Safety.InputLocalSafety
import CIL.Safety.LocalSnapshotSteps

/-! Checked full multiplication with shared private-home transitions and path composition. -/

namespace UInt256Proof.Multiply.Full
variable {alternative : Bool}
open CIL.Safety UInt256Model.Safety UInt256Proof.Multiply.Calls UInt256Proof.Multiply.BothTwo

def fullBody (profile : CIL.FeatureProfile) (wordIndex countIndex storageIndex : Nat) (alternative : Bool := false) : CIL.Method := { profile := profile, returnsValue := false, locals := [.unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled, .unmodeled], localKinds := [.word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .word64, .vector256, .vector256, .vector256, .vector256], parameterHomes := [], staticSites := [], code := [
  .arg 0,
  .fieldAt 0 8,
  .setLocal 0,
  .arg 1,
  .fieldAt 0 8,
  .setLocal 1,
  .arg 0,
  .fieldAt 8 8,
  .setLocal 2,
  .arg 1,
  .fieldAt 8 8,
  .setLocal 3,
  .arg 0,
  .fieldAt 16 8,
  .setLocal 4,
  .arg 1,
  .fieldAt 16 8,
  .setLocal 5,
  .feature .avx512DQVL,
  (if profile.avx512DQVL then .brzero 42 else .brzero 36),
  (if profile.avx512DQVL then .nop else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .nop else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .nop else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .nop else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .const32 1 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .brzero 42 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .arg 0 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .memory .asRef else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .memory .asRef else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .memory .load256 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .arg 1 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .memory .asRef else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .memory .asRef else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .memory .load256 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .setLocal 22 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .local 22 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .const32 (BitVec.ofInt 32 (27)) else .feature .avx2),
  (if profile.avx512DQVL then .intrinsic (.avx2 .permute4x64) 2 else if profile.avx2 then .brzero 84 else .brzero 78),
  (if profile.avx512DQVL then .intrinsic (.avx512DQ .mul64) 2 else if profile.avx2 then .nop else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .intrinsic (.vector (.sum64 256)) 1 else if profile.avx2 then .nop else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .setLocal 6 else if profile.avx2 then .nop else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .branch 96 else if profile.avx2 then .nop else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .const32 1 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .brzero 84 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .arg 0 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .memory .asRef else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .memory .asRef else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .memory .load256 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .setLocal 23 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .arg 1 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .memory .asRef else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .memory .asRef else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .memory .load256 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .const32 (BitVec.ofInt 32 (27)) else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .intrinsic (.avx2 .permute4x64) 2 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .setLocal 24 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .local 23 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .intrinsic (.vector (.reinterpret 256)) 1 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .local 24 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .const32 (BitVec.ofInt 32 (32)) else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .intrinsic (.avx2 .shr64) 2 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .intrinsic (.vector (.reinterpret 256)) 1 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .intrinsic (.avx2 .multiplyEven32) 2 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .local 23 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .const32 (BitVec.ofInt 32 (32)) else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .intrinsic (.avx2 .shr64) 2 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .intrinsic (.vector (.reinterpret 256)) 1 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .local 24 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .intrinsic (.vector (.reinterpret 256)) 1 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .intrinsic (.avx2 .multiplyEven32) 2 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .intrinsic (.avx2 .add64) 2 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .setLocal 25 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .local 23 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .intrinsic (.vector (.reinterpret 256)) 1 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .local 24 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .intrinsic (.vector (.reinterpret 256)) 1 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .intrinsic (.avx2 .multiplyEven32) 2 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .local 25 else .unsupported "Unreachable under selected profile"),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .const32 (BitVec.ofInt 32 (32)) else .local 0),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .intrinsic (.avx2 .shl64) 2 else .arg 1),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .intrinsic (.avx2 .add64) 2 else .fieldAt 24 8),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .intrinsic (.vector (.sum64 256)) 1 else .mul),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .setLocal 6 else .local 2),
  (if profile.avx512DQVL then .unsupported "Unreachable under selected profile" else if profile.avx2 then .branch 96 else .local 5),
  (if profile.avx512DQVL || profile.avx2 then .unsupported "Unreachable under selected profile" else .mul),
  (if profile.avx512DQVL || profile.avx2 then .unsupported "Unreachable under selected profile" else .add),
  (if profile.avx512DQVL || profile.avx2 then .unsupported "Unreachable under selected profile" else .local 4),
  (if profile.avx512DQVL || profile.avx2 then .unsupported "Unreachable under selected profile" else .local 3),
  (if profile.avx512DQVL || profile.avx2 then .unsupported "Unreachable under selected profile" else .mul),
  (if profile.avx512DQVL || profile.avx2 then .unsupported "Unreachable under selected profile" else .add),
  (if profile.avx512DQVL || profile.avx2 then .unsupported "Unreachable under selected profile" else .arg 0),
  (if profile.avx512DQVL || profile.avx2 then .unsupported "Unreachable under selected profile" else .fieldAt 24 8),
  (if profile.avx512DQVL || profile.avx2 then .unsupported "Unreachable under selected profile" else .local 1),
  (if profile.avx512DQVL || profile.avx2 then .unsupported "Unreachable under selected profile" else .mul),
  (if profile.avx512DQVL || profile.avx2 then .unsupported "Unreachable under selected profile" else .add),
  (if profile.avx512DQVL || profile.avx2 then .unsupported "Unreachable under selected profile" else .setLocal 6),
  .local 0,
  .local 1,
  .localAddr 8,
  .call wordIndex 3,
  .setLocal 7,
  .local 0,
  .local 3,
  .localAddr 10,
  .call wordIndex 3,
  .setLocal 9,
  .local 2,
  .local 1,
  .localAddr 12,
  .call wordIndex 3,
  .setLocal 11,
  .const32 0,
  .convI8,
  .setLocal 13,
  .local 7,
  .local (if alternative then 12 else 10),
  .localAddr 13,
  .call countIndex 3,
  .setLocal 14,
  .local 14,
  .local (if alternative then 10 else 12),
  .localAddr 13,
  .call countIndex 3,
  .setLocal 14,
  .local 13,
  .setLocal 15,
  .const32 0,
  .convI8,
  .setLocal 13,
  .local 15,
  .local 9,
  .localAddr 13,
  .call countIndex 3,
  .setLocal 15,
  .local 15,
  .local 11,
  .localAddr 13,
  .call countIndex 3,
  .setLocal 15,
  .local 0,
  .local 5,
  .localAddr 17,
  .call wordIndex 3,
  .setLocal 16,
  .local 15,
  .local 17,
  .localAddr 13,
  .call countIndex 3,
  .setLocal 15,
  .local 6,
  .local 16,
  .add,
  .setLocal 6,
  .local 2,
  .local 3,
  .localAddr 19,
  .call wordIndex 3,
  .setLocal 18,
  .local 15,
  .local 19,
  .localAddr 13,
  .call countIndex 3,
  .setLocal 15,
  .local 6,
  .local 18,
  .add,
  .setLocal 6,
  .local 4,
  .local 1,
  .localAddr 21,
  .call wordIndex 3,
  .setLocal 20,
  .local 15,
  .local 21,
  .localAddr 13,
  .call countIndex 3,
  .setLocal 15,
  .local 6,
  .local 20,
  .local 13,
  .add,
  .add,
  .setLocal 6,
  .arg 2,
  .local 8,
  .local 14,
  .local 15,
  .local 6,
  .call storageIndex 5,
  .ret
] }
theorem full_frame_setup (profile : CIL.FeatureProfile) (program : CIL.Program) (methodIndex wordIndex countIndex storageIndex : Nat)
    (_found : program[methodIndex]? = some (fullBody profile wordIndex countIndex storageIndex alternative)) (memory : Memory) (left right output : Reference)
    (call : CallingConditions program memory [left, right] [output]) :
    ∃ frame entered,
      enterFrame (fullBody profile wordIndex countIndex storageIndex alternative) (productArgs left right output) memory = .ok (frame, entered) ∧
      CompleteWritableHomes entered memory.nextIdentity (fullBody profile wordIndex countIndex storageIndex alternative).localKinds frame.locals ∧
      entered.WellFormed ∧
      PrivateWords program memory entered entered [left, right] [output] frame (fun _ => none) := by
  have kinds : (fullBody profile wordIndex countIndex storageIndex alternative).localKinds = (List.replicate 22 CIL.LocalKind.word64 ++ List.replicate 4 CIL.LocalKind.vector256) := by rfl
  obtain ⟨frame, entered, setup, homes, _, wf⟩ := unknown_frame_setup (fullBody profile wordIndex countIndex storageIndex alternative)
    (by rfl) (by simp [kinds]) (by simp [kinds]) (by simp [kinds])
    (by simp [kinds]) (by simp [kinds]) (by simp [kinds]) (by rfl) (by rfl) (by rfl) memory (productArgs left right output) call.1.1
  exact ⟨frame, entered, setup, homes, wf, PrivateWords.initial call setup⟩

def fullInputs (original : Memory) (left right : Reference) :=
  rememberWord (rememberWord (rememberWord (rememberWord (rememberWord (rememberWord (fun _ => none)
    0 (inputLimb original left 0)) 1 (inputLimb original right 0))
    2 (inputLimb original left 1)) 3 (inputLimb original right 1))
    4 (inputLimb original left 2)) 5 (inputLimb original right 2)

def fullTop (original : Memory) (left right : Reference) :=
  ((inputLimb original left 0 * inputLimb original right 3 + inputLimb original left 1 * inputLimb original right 2) +
    inputLimb original left 2 * inputLimb original right 1) + inputLimb original left 3 * inputLimb original right 0

theorem full_scalar_top (profile : CIL.FeatureProfile) (program : CIL.Program) (methodIndex wordIndex countIndex storageIndex : Nat)
    (found : program[methodIndex]? = some (fullBody profile wordIndex countIndex storageIndex alternative))
    (noAvx512 : profile.avx512DQVL = false) (noAvx2 : profile.avx2 = false)
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : CompleteWritableHomes entered original.nextIdentity (fullBody profile wordIndex countIndex storageIndex alternative).localKinds frame.locals)
    (state : PrivateWords program original entered current [left, right] [output] frame
      (fullInputs original left right))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      PrivateWords program original entered after [left, right] [output] frame
        (rememberWord (fullInputs original left right) 6 (fullTop original left right)) →
      ∃ fuel final returned,
        run program fuel methodIndex 96 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel methodIndex 18 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned := by
  have formedLeft := state.call.input_formed (by simp : left ∈ [left, right])
  have formedRight := state.call.input_formed (by simp : right ∈ [left, right])
  have readingLeft := state.input_field originalCall left (by simp) 3
  have readingRight := state.input_field originalCall right (by simp) 3
  have formed := state.call.1.1
  have retained := state.authority
  cil_contract_steps (snapshots := state.snapshots.toLocalSnapshots)
    [productArgs, fullBody, fullInputs, wordLocals, rememberWord, fullTop, formedLeft,
      formedRight, readingLeft, readingRight, noAvx512, noAvx2, Bool.or_false]
    until continuation _ (state.after_word_write homes (by assumption) localWrite)

def fullPrepared (original : Memory) (left right : Reference) :=
  rememberWord (fullInputs original left right) 6 (fullTop original left right)

def fullFirstProducts (original : Memory) (left right : Reference) :=
  widenWords (widenWords (widenWords (fullPrepared original left right) 0 1 8 7) 0 3 10 9) 2 1 12 11

def fullSecondColumn (original : Memory) (left right : Reference) :=
  countWords (countWords (rememberWord (fullFirstProducts original left right) 13 0) 7 10 13 14) 14 12 13 14

theorem countCarry_order (a b c : BitVec 64) :
    countCarry (a + b) c (countCarry a b 0) = countCarry (a + c) b (countCarry a c 0) := by
  have carry (x z : Nat) : x / 2^64 + (x % 2^64 + z) / 2^64 = (x + z) / 2^64 := by
    conv => rhs; rw [← Nat.div_add_mod x (2^64), Nat.add_assoc, Nat.mul_add_div (by decide)]
  have split (x y z : BitVec 64) :
      sumHigh x y + sumHigh (x + y) z = BitVec.ofNat 64 ((x.toNat + y.toNat + z.toNat) / 2^64) := by
    simp only [sumHigh, BitVec.ofNat_add_ofNat, BitVec.toNat_add, carry]
  simp only [countCarry, BitVec.add_assoc, split, Nat.add_right_comm a.toNat b.toNat c.toNat]

theorem second_column_order (known : Nat → Option (BitVec 64)) :
    countWords (countWords (rememberWord known 13 0) 7 12 13 14) 14 10 13 14 =
    countWords (countWords (rememberWord known 13 0) 7 10 13 14) 14 12 13 14 := by
  funext index
  by_cases out : index = 14
  · subst index
    simp only [countWords, rememberWord, localWord]
    simp only [↓reduceIte, Option.getD_some]
    congr 1
    ac_rfl
  · by_cases carry : index = 13
    · subst index
      simp only [countWords, rememberWord, localWord]
      simp only [↓reduceIte, Option.getD_some]
      exact congrArg some (countCarry_order _ _ _)
    · simp [countWords, rememberWord, out, carry]

def fullMiddleWords (original : Memory) (left right : Reference) :=
  let known := fullSecondColumn original left right
  let reset := rememberWord (rememberWord known 15 (localWord known 13)) 13 0
  countWords (countWords reset 15 9 13 15) 15 11 13 15

def FullTopContract (profile : CIL.FeatureProfile) (program : CIL.Program) (methodIndex wordIndex countIndex storageIndex : Nat) : Prop :=
  ∀
    (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (_originalCall : CallingConditions program original [left, right] [output])
    (_enteredWF : entered.WellFormed)
    (_homes : CompleteWritableHomes entered original.nextIdentity (fullBody profile wordIndex countIndex storageIndex).localKinds frame.locals)
    (_state : PrivateWords program original entered current [left, right] [output] frame
      (fullInputs original left right))
    (post : Memory → List Value → Prop)
    (_continuation : ∀ after,
      PrivateWords program original entered after [left, right] [output] frame
        (rememberWord (fullInputs original left right) 6 (fullTop original left right)) →
      ∃ fuel final returned,
        run program fuel methodIndex 96 (productArgs left right output) frame [] after =
          .ok (final, returned) ∧ post final returned),
    ∃ fuel final returned,
      run program fuel methodIndex 18 (productArgs left right output) frame [] current =
        .ok (final, returned) ∧ post final returned

def fullFirstUpperWords (original : Memory) (left right : Reference) :=
  let known := countWords (widenWords (fullMiddleWords original left right) 0 5 17 16) 15 17 13 15
  rememberWord known 6 (localWord known 6 + localWord known 16)

def fullUpperWords (original : Memory) (left right : Reference) :=
  let known := countWords (widenWords (fullFirstUpperWords original left right) 2 3 19 18) 15 19 13 15
  rememberWord known 6 (localWord known 6 + localWord known 18)

def fullFinalWords (original : Memory) (left right : Reference) :=
  let known := countWords (widenWords (fullUpperWords original left right) 4 1 21 20) 15 21 13 15
  rememberWord known 6 (localWord known 6 + (localWord known 20 + localWord known 13))

def fullResultWords (original : Memory) (left right : Reference) : UInt256Model.Limbs := fun index =>
  let known := fullFinalWords original left right
  localWord known (if index.val = 0 then 8 else if index.val = 1 then 14 else if index.val = 2 then 15 else 6)

theorem full_words_correct (original : Memory) (left right : Reference) :
    UInt256Model.value (fullResultWords original left right) = inputValue original left * inputValue original right := by
  have words : fullResultWords original left right = productLimbs (inputLimb original left) (inputLimb original right) := by
    funext ⟨index, bound⟩
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · rfl
    · rfl
    · rfl
    · have top : fullResultWords original left right ⟨3, bound⟩ =
          (((((lowProduct (inputLimb original left 0) (inputLimb original right 3) +
            lowProduct (inputLimb original left 1) (inputLimb original right 2)) +
            lowProduct (inputLimb original left 2) (inputLimb original right 1)) +
            lowProduct (inputLimb original left 3) (inputLimb original right 0)) +
            highProduct (inputLimb original left 0) (inputLimb original right 2)) +
            highProduct (inputLimb original left 1) (inputLimb original right 1)) +
            (highProduct (inputLimb original left 2) (inputLimb original right 0) +
              (secondColumn (inputLimb original left) (inputLimb original right)).2) := rfl
      rw [top]
      show _ = (topWords _ _).sum
      simp only [topWords, List.sum_cons, List.sum_nil, BitVec.add_assoc]
      exact congrArg _ (congrArg _ (congrArg _ (congrArg _ (congrArg _ (congrArg _
        (congrArg _ (BitVec.add_zero _).symm))))))
  rw [words, product_limbs_correct, input_limbs_value, input_limbs_value]

/-- The full path composes actual local-writing helpers under one execution predicate. -/
theorem full_invoke_with_storage (profile : CIL.FeatureProfile) (program : CIL.Program) (methodIndex wordIndex countIndex storageIndex : Nat)
    (storage : ProductStorage.Contract program storageIndex)
    (found : program[methodIndex]? = some (fullBody profile wordIndex countIndex storageIndex alternative))
    (countFound : program[countIndex]? = some (CountSafety.body profile)) (contract : WordContract program wordIndex) (top : FullTopContract profile program methodIndex wordIndex countIndex storageIndex) (memory : Memory) (left right output : Reference)
    (call : CallingConditions program memory [left, right] [output]) :
    ∃ fuel final,
      invoke program fuel methodIndex (productArgs left right output) memory = .ok (final, []) ∧
      ProductResult memory final left right output [] := by
  obtain ⟨frame, entered, setup, homes, enteredWF, state⟩ := full_frame_setup profile program
    methodIndex wordIndex countIndex storageIndex found memory left right output call
  have owned : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id :=
    fun id member => ((enterFrame_fresh _ _ _ _ _ setup).2 id member).1
  let post := fun final returned => ProductResult memory final left right output returned
  have upper : ∀ current, PrivateWords program memory entered current [left, right] [output]
      frame (fullSecondColumn memory left right) →
      WP (Execution (fun fuel => run program fuel methodIndex 124
        (productArgs left right output) frame [] current)) (Function.uncurry post) := by
    intro current middle
    apply WP.step found (by rfl) (middle.snapshots.load _ (localWord_remembered (by rfl)))
    apply run_store_local middle enteredWF homes 15 (by rfl) _ found (by rfl)
    intro _ copied
    iterate 2 (apply WP.step found (by rfl); rfl)
    apply run_store_local copied enteredWF homes 13 (by rfl) 0 found (by rfl)
    intro _ reset
    apply run_count_locals countFound reset call enteredWF homes 15 9 13 15
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro _ m0
    apply run_count_locals countFound m0 call enteredWF homes 15 11 13 15
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro _ m1
    apply run_widen_locals contract m1 call enteredWF homes 0 5 17 16
      (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro _ m2
    apply run_count_locals countFound m2 call enteredWF homes 15 17 13 15
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro _ m3
    apply WP.step found (by rfl) (m3.snapshots.load _ (localWord_remembered (by rfl)))
    apply WP.step found (by rfl) (m3.snapshots.load _ (localWord_remembered (by rfl)))
    iterate 1 (apply WP.step found (by rfl); rfl)
    apply run_store_local m3 enteredWF homes 6 (by rfl) _ found (by rfl)
    intro _ m4
    apply run_widen_locals contract m4 call enteredWF homes 2 3 19 18
      (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro _ m5
    apply run_count_locals countFound m5 call enteredWF homes 15 19 13 15
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro _ m6
    apply WP.step found (by rfl) (m6.snapshots.load _ (localWord_remembered (by rfl)))
    apply WP.step found (by rfl) (m6.snapshots.load _ (localWord_remembered (by rfl)))
    iterate 1 (apply WP.step found (by rfl); rfl)
    apply run_store_local m6 enteredWF homes 6 (by rfl) _ found (by rfl)
    intro _ m7
    apply run_widen_locals contract m7 call enteredWF homes 4 1 21 20
      (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro _ m8
    apply run_count_locals countFound m8 call enteredWF homes 15 21 13 15
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro _ m9
    have formed := m9.call.1.1
    have retained := m9.authority
    have valid := m9.call.1
    cil_contract_steps (snapshots := m9.snapshots.toLocalSnapshots) [productArgs]
    apply WP.exists_execution
    exact run_product_storage storage (m9.after_word_write homes (by assumption) localWrite)
      call owned (fullResultWords memory left right) (full_words_correct memory left right)
      found (by rfl) (by rfl)
  have body : ∃ fuel final returned, run program fuel methodIndex 0
      (productArgs left right output) frame [] entered = .ok (final, returned) ∧
        post final returned := by
    apply run_input_to_local (argument := 0) (target := 0) state call enteredWF homes left
      (by simp) 0 (by rfl) (by rfl) found (by rfl) post
    intro _ saved0
    apply run_input_to_local (argument := 1) (target := 1) saved0 call enteredWF homes right
      (by simp) 0 (by rfl) (by rfl) found (by rfl) post
    intro _ saved1
    apply run_input_to_local (argument := 0) (target := 2) saved1 call enteredWF homes left
      (by simp) 1 (by rfl) (by rfl) found (by rfl) post
    intro _ saved2
    apply run_input_to_local (argument := 1) (target := 3) saved2 call enteredWF homes right
      (by simp) 1 (by rfl) (by rfl) found (by rfl) post
    intro _ saved3
    apply run_input_to_local (argument := 0) (target := 4) saved3 call enteredWF homes left
      (by simp) 2 (by rfl) (by rfl) found (by rfl) post
    intro _ saved4
    apply run_input_to_local (argument := 1) (target := 5) saved4 call enteredWF homes right
      (by simp) 2 (by rfl) (by rfl) found (by rfl) post
    intro _ saved5
    apply top memory entered _ left right output frame call enteredWF homes saved5 post
    intro _ prepared
    apply WP.exists_execution
    apply run_widen_locals contract prepared call enteredWF homes 0 1 8 7
      (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro _ p0
    apply run_widen_locals contract p0 call enteredWF homes 0 3 10 9
      (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro _ p1
    apply run_widen_locals contract p1 call enteredWF homes 2 1 12 11
      (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
    intro _ p2
    iterate 2 (apply WP.step found (by rfl); rfl)
    apply run_store_local p2 enteredWF homes 13 (by rfl) 0 found (by rfl)
    intro _ p3
    cases alternative with
    | false =>
      apply run_count_locals countFound p3 call enteredWF homes 7 10 13 14
        (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
      intro _ p4
      apply run_count_locals countFound p4 call enteredWF homes 14 12 13 14
        (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
      intro _ p5
      exact upper _ p5
    | true =>
      apply run_count_locals countFound p3 call enteredWF homes 7 12 13 14
        (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
      intro _ p4
      apply run_count_locals countFound p4 call enteredWF homes 14 10 13 14
        (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) found (by rfl)
      intro _ p5
      apply upper
      change PrivateWords _ _ _ _ _ _ _ (countWords (countWords (rememberWord
        (fullFirstProducts memory left right) 13 0) 7 12 13 14) 14 10 13 14) at p5
      rw [second_column_order] at p5
      exact p5
  obtain ⟨fuel, final, returned, ran, result⟩ := body
  have returns : returned = [] := result.returns
  subst returned
  have leftFormed := call.input_formed (by simp : left ∈ [left, right])
  have rightFormed := call.input_formed (by simp : right ∈ [left, right])
  have outputFormed := call.output_formed (by simp : output ∈ [output])
  have checked : (productArgs left right output).mapM (checkedValue memory) = .ok (productArgs left right output) := by
    simp [productArgs, checkedValue, formValue, leftFormed, rightFormed, outputFormed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  refine ⟨fuel, final, ?_, result⟩
  exact invoke_of_run found checked setup ran

theorem full_invoke (profile : CIL.FeatureProfile) (program : CIL.Program) (methodIndex wordIndex countIndex storageIndex : Nat)
    (limbIndex : Nat) (scalar : profile.vector256Accelerated = false)
    (storageFound : program[storageIndex]? = some (ProductStorage.body profile limbIndex))
    (limbsFound : program[limbIndex]? = some (LimbStorage.body profile))
    (found : program[methodIndex]? = some (fullBody profile wordIndex countIndex storageIndex alternative))
    (countFound : program[countIndex]? = some (CountSafety.body profile)) (contract : WordContract program wordIndex) (top : FullTopContract profile program methodIndex wordIndex countIndex storageIndex) (memory : Memory) (left right output : Reference)
    (call : CallingConditions program memory [left, right] [output]) :
    ∃ fuel final,
      invoke program fuel methodIndex (productArgs left right output) memory = .ok (final, []) ∧
      ProductResult memory final left right output [] :=
  full_invoke_with_storage profile program methodIndex wordIndex countIndex storageIndex (ProductStorage.scalar_contract profile scalar program storageIndex limbIndex storageFound limbsFound) found countFound contract top memory left right output call
end UInt256Proof.Multiply.Full
namespace UInt256Proof.Multiply.Full
variable {alternative : Bool}
 theorem scalar_top_contract_order (profile : CIL.FeatureProfile) (program : CIL.Program)
    (methodIndex wordIndex countIndex storageIndex : Nat)
    (found : program[methodIndex]? = some (fullBody profile wordIndex countIndex storageIndex alternative))
    (noAvx512 : profile.avx512DQVL = false) (noAvx2 : profile.avx2 = false) :
    FullTopContract profile program methodIndex wordIndex countIndex storageIndex :=
  full_scalar_top (alternative := alternative) profile program methodIndex wordIndex countIndex storageIndex found noAvx512 noAvx2
end UInt256Proof.Multiply.Full
namespace UInt256Proof.Multiply.Full
theorem scalar_top_contract (profile : CIL.FeatureProfile) (program : CIL.Program)
    (methodIndex wordIndex countIndex storageIndex : Nat)
    (found : program[methodIndex]? = some (fullBody profile wordIndex countIndex storageIndex))
    (noAvx512 : profile.avx512DQVL = false) (noAvx2 : profile.avx2 = false) :
    FullTopContract profile program methodIndex wordIndex countIndex storageIndex :=
  scalar_top_contract_order profile program methodIndex wordIndex countIndex storageIndex found noAvx512 noAvx2
end UInt256Proof.Multiply.Full
