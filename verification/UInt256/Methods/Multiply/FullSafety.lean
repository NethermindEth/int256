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

set_option maxRecDepth 4096 in
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
  simp only [CIL.fin_val_three, Nat.reduceMul] at readingLeft readingRight
  obtain ⟨after, stored, next⟩ := state.store enteredWF homes 6 (by rfl)
    (fullTop original left right) 95 (productArgs left right output) []
    (body := fullBody profile wordIndex countIndex storageIndex alternative)
  have suffix := continuation after next
  let scalarBody := fullBody profile wordIndex countIndex storageIndex alternative
  have noAvx512Feature : profile.evaluate .avx512DQVL = false := noAvx512
  have noAvx2Feature : profile.evaluate .avx2 = false := noAvx2
  obtain ⟨architecture, nativeWidth, littleEndian, advSimd, sse2, ssse3, sse42, avx, avx2,
    avx512F, avx512FVL, bmi1, sse41, avx512DQ, avx512DQVL, bmi2, armBase64,
    vector256Accelerated⟩ := profile
  change avx512DQVL = false at noAvx512
  change avx2 = false at noAvx2
  subst noAvx512 noAvx2
  have fetched91 : scalarBody.code[91]? = some (.fieldAt 24 8) := by rfl
  have fetched95 : scalarBody.code[95]? = some (.setLocal 6) := by rfl
  cil_contract_steps (snapshots := state.snapshots.toLocalSnapshots)
    [productArgs, fullBody, fullInputs, wordLocals, rememberWord, fullTop, fetched91, fetched95,
      formedLeft, formedRight, readingLeft, readingRight, stored,
      noAvx512Feature, noAvx2Feature] until suffix
  exact run_next_exists post found fetched95 stored suffix

theorem localWord_known (known : Nat → Option (BitVec 64)) (index : Nat)
    (present : (known index).isSome = true) : known index = some (localWord known index) := by
  cases found : known index <;> simp_all [localWord]

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
  obtain ⟨frame, entered, setup, homes, enteredWF, state⟩ := full_frame_setup profile program methodIndex wordIndex countIndex storageIndex found memory left right output call
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have owned : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id := fun id member => (fresh.2 id member).1
  let post := fun final returned => ProductResult memory final left right output returned
  let execute (pc : Nat) (known : Nat → Option (BitVec 64)) :=
    ∀ current, PrivateWords program memory entered current [left, right] [output] frame known →
    WP (Execution (fun fuel => run program fuel methodIndex pc
        (productArgs left right output) frame [] current)) (Function.uncurry post)
  have finish : execute 183 (fullFinalWords memory left right) := by
    intro current state
    apply WP.adequate.mpr
    let known := fullFinalWords memory left right
    let words := fullResultWords memory left right
    let post := fun final returned => ProductResult memory final left right output returned
    have formed := state.call.output_formed (by simp : output ∈ [output])
    have load (index : Nat) (value : BitVec 64) (present : known index = some value)
        (pc : Nat) (stack : List Value) := state.snapshots.load
      (body := fullBody profile wordIndex countIndex storageIndex alternative)
      (args := productArgs left right output) (pc := pc) (stack := stack) value present
    have saved0 := load 8 (words 0) (localWord_known _ _ (by rfl))
    have saved1 := load 14 (words 1) (localWord_known _ _ (by rfl))
    have saved2 := load 15 (words 2) (localWord_known _ _ (by rfl))
    have saved3 := load 6 (words 3) (localWord_known _ _ (by rfl))
    cil_contract_steps 5 [productArgs, formed, saved0, saved1, saved2, saved3]
    obtain ⟨childFuel, result, invoked, valid, outside, _, value, readable⟩ :=
      storage current [left, right] output (words 0) (words 1) (words 2) (words 3) state.call
    have packed : inputValue result output = UInt256Model.value words := value
    have stepped (w0 w1 w2 w3 : BitVec 64) : step (fullBody profile wordIndex countIndex storageIndex alternative)
        (.call storageIndex 5) 188 (productArgs left right output) frame
        [.scalar (.i64 w3), .scalar (.i64 w2), .scalar (.i64 w1),
          .scalar (.i64 w0), .reference (.address output)] current =
        .ok (.call storageIndex [.reference (.address output), .scalar (.i64 w0),
          .scalar (.i64 w1), .scalar (.i64 w2), .scalar (.i64 w3)] [] current) := by
      cil_checked_step [formed]
    apply WP.exists_execution
    apply WP.call (helperPost := fun after => after.1 = result ∧ after.2 = [])
      found (by rfl) (stepped (words 0) (words 1) (words 2) (words 3)) ⟨childFuel, (result, []), invoked, rfl, rfl⟩
    rintro final returned ⟨same, rfl⟩
    change final = result at same
    subst final
    apply WP.returned found (by rfl) (by rfl) (by rfl)
    exact output_result_of_storage memory current result [left, right]
      output _ frame call valid owned state.caller
      (packed.trans (full_words_correct memory left right)) readable outside
  have finalColumn : execute 167 (fullUpperWords memory left right) := by
    intro current state
    let continuation := finish
    let k0 := fullUpperWords memory left right
    apply run_local_word_call state call enteredWF homes 4 1 21 20
      (localWord k0 4) (localWord k0 1) (lowProduct (localWord k0 4) (localWord k0 1))
      (highProduct (localWord k0 4) (localWord k0 1)) (localWord_known _ _ (by rfl)) (localWord_known _ _ (by rfl)) (by rfl) (by rfl)
      found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (fun reference _ ready => widening_local_effect contract current _ _ state.call.1.1 reference ready) post
    intro m1 state1
    let k1 := widenWords k0 4 1 21 20
    apply run_local_word_call state1 call enteredWF homes 15 21 13 15
      (localWord k1 15) (localWord k1 21) (countCarry (localWord k1 15) (localWord k1 21) (localWord k1 13))
      (localWord k1 15 + localWord k1 21) (localWord_known _ _ (by rfl)) (localWord_known _ _ (by rfl)) (by rfl) (by rfl)
      found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (counting_local_effect profile program countIndex countFound state1.snapshots state1.call.1.1 13 _ _ (localWord k1 13) (localWord_known _ _ (by rfl))) post
    intro m2 state2
    let k2 := countWords k1 15 21 13 15
    apply WP.step found (by rfl) (state2.snapshots.load (localWord k2 6) (localWord_known _ _ (by rfl)))
    apply WP.step found (by rfl) (state2.snapshots.load (localWord k2 20) (localWord_known _ _ (by rfl)))
    apply WP.step found (by rfl) (state2.snapshots.load (localWord k2 13) (localWord_known _ _ (by rfl)))
    iterate 2
      apply WP.step found (by rfl)
      rfl
    obtain ⟨after, stored, next⟩ := state2.store enteredWF homes 6 (by rfl)
      (localWord k2 6 + (localWord k2 20 + localWord k2 13)) 182 (productArgs left right output) [] (body := (fullBody profile wordIndex countIndex storageIndex alternative))
    exact WP.step found (by rfl) stored (continuation after next)
  have upperColumn : execute 153 (fullFirstUpperWords memory left right) := by
    intro current state
    let continuation := finalColumn
    let k0 := fullFirstUpperWords memory left right
    apply run_local_word_call state call enteredWF homes 2 3 19 18
      (localWord k0 2) (localWord k0 3) (lowProduct (localWord k0 2) (localWord k0 3))
      (highProduct (localWord k0 2) (localWord k0 3))
      (localWord_known _ _ (by rfl)) (localWord_known _ _ (by rfl)) (by rfl) (by rfl)
      found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (fun reference _ ready => widening_local_effect contract current _ _ state.call.1.1 reference ready) post
    intro m1 state1
    let k1 := widenWords k0 2 3 19 18
    apply run_local_word_call state1 call enteredWF homes 15 19 13 15
      (localWord k1 15) (localWord k1 19) (countCarry (localWord k1 15) (localWord k1 19) (localWord k1 13))
      (localWord k1 15 + localWord k1 19)
      (localWord_known _ _ (by rfl)) (localWord_known _ _ (by rfl)) (by rfl) (by rfl)
      found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (counting_local_effect profile program countIndex countFound state1.snapshots state1.call.1.1 13 _ _ (localWord k1 13) (localWord_known _ _ (by rfl))) post
    intro m2 state2
    let k2 := countWords k1 15 19 13 15
    apply WP.step found (by rfl) (state2.snapshots.load (localWord k2 6) (localWord_known _ _ (by rfl)))
    apply WP.step found (by rfl) (state2.snapshots.load (localWord k2 18) (localWord_known _ _ (by rfl)))
    apply WP.step found (by rfl)
    · rfl
    obtain ⟨after, stored, next⟩ := state2.store enteredWF homes 6 (by rfl)
      (localWord k2 6 + localWord k2 18) 166 (productArgs left right output) [] (body := (fullBody profile wordIndex countIndex storageIndex alternative))
    exact WP.step found (by rfl) stored (continuation after next)
  have firstUpper : execute 139 (fullMiddleWords memory left right) := by
    intro current state
    let continuation := upperColumn
    let k0 := fullMiddleWords memory left right
    apply run_local_word_call state call enteredWF homes 0 5 17 16
      (localWord k0 0) (localWord k0 5) (lowProduct (localWord k0 0) (localWord k0 5))
      (highProduct (localWord k0 0) (localWord k0 5))
      (localWord_known _ _ (by rfl)) (localWord_known _ _ (by rfl)) (by rfl) (by rfl)
      found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (fun reference _ ready => widening_local_effect contract current _ _ state.call.1.1 reference ready) post
    intro m1 state1
    let k1 := widenWords k0 0 5 17 16
    apply run_local_word_call state1 call enteredWF homes 15 17 13 15
      (localWord k1 15) (localWord k1 17) (countCarry (localWord k1 15) (localWord k1 17) (localWord k1 13))
      (localWord k1 15 + localWord k1 17)
      (localWord_known _ _ (by rfl)) (localWord_known _ _ (by rfl)) (by rfl) (by rfl)
      found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (counting_local_effect profile program countIndex countFound state1.snapshots state1.call.1.1 13 _ _ (localWord k1 13) (localWord_known _ _ (by rfl))) post
    intro m2 state2
    let k2 := countWords k1 15 17 13 15
    apply WP.step found (by rfl) (state2.snapshots.load (localWord k2 6) (localWord_known _ _ (by rfl)))
    apply WP.step found (by rfl) (state2.snapshots.load (localWord k2 16) (localWord_known _ _ (by rfl)))
    apply WP.step found (by rfl)
    · rfl
    obtain ⟨after, stored, next⟩ := state2.store enteredWF homes 6 (by rfl)
      (localWord k2 6 + localWord k2 16) 152 (productArgs left right output) [] (body := (fullBody profile wordIndex countIndex storageIndex alternative))
    exact WP.step found (by rfl) stored (continuation after next)
  have middleColumn : execute 124 (fullSecondColumn memory left right) := by
    intro current state
    let continuation := firstUpper
    let known := fullSecondColumn memory left right
    apply WP.step found (by rfl)
      (state.snapshots.load (localWord known 13) (localWord_known _ _ (by rfl)))
    obtain ⟨copied, copiedStep, copiedState⟩ := state.store enteredWF homes 15 (by rfl) (localWord known 13)
      125 (productArgs left right output) [] (body := (fullBody profile wordIndex countIndex storageIndex alternative))
    apply WP.step found (by rfl) copiedStep
    iterate 2
      apply WP.step found (by rfl)
      rfl
    obtain ⟨m0, resetStep, state0⟩ := copiedState.store enteredWF homes 13 (by rfl) 0
      128 (productArgs left right output) [] (body := (fullBody profile wordIndex countIndex storageIndex alternative))
    apply WP.step found (by rfl) resetStep
    let k0 := rememberWord (rememberWord known 15 (localWord known 13)) 13 0
    apply run_local_word_call state0 call enteredWF homes 15 9 13 15
      (localWord k0 15) (localWord k0 9) (countCarry (localWord k0 15) (localWord k0 9) 0)
      (localWord k0 15 + localWord k0 9) (localWord_known _ _ (by rfl)) (localWord_known _ _ (by rfl)) (by rfl) (by rfl)
      found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (counting_local_effect profile program countIndex countFound state0.snapshots state0.call.1.1 13 _ _ 0 (by rfl)) post
    intro m1 state1
    let k1 := countWords k0 15 9 13 15
    apply run_local_word_call state1 call enteredWF homes 15 11 13 15
      (localWord k1 15) (localWord k1 11) (countCarry (localWord k1 15) (localWord k1 11) (localWord k1 13))
      (localWord k1 15 + localWord k1 11) (localWord_known _ _ (by rfl)) (localWord_known _ _ (by rfl)) (by rfl) (by rfl)
      found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (counting_local_effect profile program countIndex countFound state1.snapshots state1.call.1.1 13 _ _ (localWord k1 13) (by rfl)) post
    exact continuation
  have secondColumn : execute 96 (fullPrepared memory left right) := by
    intro current state
    let continuation := middleColumn
    let k0 := fullPrepared memory left right
    apply run_local_word_call state call enteredWF homes 0 1 8 7
      (localWord k0 0) (localWord k0 1) (lowProduct (localWord k0 0) (localWord k0 1))
      (highProduct (localWord k0 0) (localWord k0 1)) (by rfl) (by rfl) (by rfl) (by rfl)
      found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (fun reference _ ready => widening_local_effect contract current _ _ state.call.1.1 reference ready) post
    intro m1 state1
    let k1 := widenWords k0 0 1 8 7
    apply run_local_word_call state1 call enteredWF homes 0 3 10 9
      (localWord k1 0) (localWord k1 3) (lowProduct (localWord k1 0) (localWord k1 3))
      (highProduct (localWord k1 0) (localWord k1 3)) (by rfl) (by rfl) (by rfl) (by rfl)
      found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (fun reference _ ready => widening_local_effect contract m1 _ _ state1.call.1.1 reference ready) post
    intro m2 state2
    let k2 := widenWords k1 0 3 10 9
    apply run_local_word_call state2 call enteredWF homes 2 1 12 11
      (localWord k2 2) (localWord k2 1) (lowProduct (localWord k2 2) (localWord k2 1))
      (highProduct (localWord k2 2) (localWord k2 1)) (by rfl) (by rfl) (by rfl) (by rfl)
      found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (fun reference _ ready => widening_local_effect contract m2 _ _ state2.call.1.1 reference ready) post
    intro m3 state3
    iterate 2
      apply WP.step found (by rfl)
      rfl
    obtain ⟨m4, reset, state4⟩ := state3.store enteredWF homes 13 (by rfl) 0
      113 (productArgs left right output) [] (body := (fullBody profile wordIndex countIndex storageIndex alternative))
    apply WP.step found (by rfl) reset
    cases alternative with
    | false =>
        let k4 := rememberWord (fullFirstProducts memory left right) 13 0
        apply run_local_word_call state4 call enteredWF homes 7 10 13 14
          (localWord k4 7) (localWord k4 10) (countCarry (localWord k4 7) (localWord k4 10) 0)
          (localWord k4 7 + localWord k4 10) (by rfl) (by rfl) (by rfl) (by rfl)
          found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
          (counting_local_effect profile program countIndex countFound state4.snapshots state4.call.1.1 13 _ _ 0 (by rfl)) post
        intro m5 state5
        let k5 := countWords k4 7 10 13 14
        apply run_local_word_call state5 call enteredWF homes 14 12 13 14
          (localWord k5 14) (localWord k5 12) (countCarry (localWord k5 14) (localWord k5 12) (localWord k5 13))
          (localWord k5 14 + localWord k5 12) (by rfl) (by rfl) (by rfl) (by rfl)
          found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
          (counting_local_effect profile program countIndex countFound state5.snapshots state5.call.1.1 13 _ _ (localWord k5 13) (by rfl)) post
        exact continuation
    | true =>
        let k4 := rememberWord (fullFirstProducts memory left right) 13 0
        apply run_local_word_call state4 call enteredWF homes 7 12 13 14
          (localWord k4 7) (localWord k4 12) (countCarry (localWord k4 7) (localWord k4 12) 0)
          (localWord k4 7 + localWord k4 12) (by rfl) (by rfl) (by rfl) (by rfl)
          found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
          (counting_local_effect profile program countIndex countFound state4.snapshots state4.call.1.1 13 _ _ 0 (by rfl)) post
        intro m5 state5
        let k5 := countWords k4 7 12 13 14
        apply run_local_word_call state5 call enteredWF homes 14 10 13 14
          (localWord k5 14) (localWord k5 10) (countCarry (localWord k5 14) (localWord k5 10) (localWord k5 13))
          (localWord k5 14 + localWord k5 10) (by rfl) (by rfl) (by rfl) (by rfl)
          found (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
          (counting_local_effect profile program countIndex countFound state5.snapshots state5.call.1.1 13 _ _ (localWord k5 13) (by rfl)) post
        intro after stateAfter
        apply continuation after
        change PrivateWords _ _ _ _ _ _ _ (countWords (countWords (rememberWord (fullFirstProducts memory left right) 13 0) 7 12 13 14) 14 10 13 14) at stateAfter
        rw [second_column_order] at stateAfter
        exact stateAfter
  have prepared : execute 18 (fullInputs memory left right) := by
    intro current saved
    apply WP.adequate.mpr
    apply top memory entered current left right output frame call enteredWF homes saved post
    intro current ready
    exact WP.adequate.mp (secondColumn current ready)
  have body : WP (Execution (fun fuel => run program fuel methodIndex 0
      (productArgs left right output) frame [] entered)) (Function.uncurry post) := by
    apply WP.adequate.mpr
    let continuation := fun current saved => WP.adequate.mp (prepared current saved)
    apply run_input_to_local (argument := 0) (target := 0) state call enteredWF homes left (by simp) 0
      (by rfl) (by rfl) found (by rfl) post
    intro m0 state0
    apply run_input_to_local (argument := 1) (target := 1) state0 call enteredWF homes right (by simp) 0
      (by rfl) (by rfl) found (by rfl) post
    intro m1 state1
    apply run_input_to_local (argument := 0) (target := 2) state1 call enteredWF homes left (by simp) 1
      (by rfl) (by rfl) found (by rfl) post
    intro m2 state2
    apply run_input_to_local (argument := 1) (target := 3) state2 call enteredWF homes right (by simp) 1
      (by rfl) (by rfl) found (by rfl) post
    intro m3 state3
    apply run_input_to_local (argument := 0) (target := 4) state3 call enteredWF homes left (by simp) 2
      (by rfl) (by rfl) found (by rfl) post
    intro m4 state4
    apply run_input_to_local (argument := 1) (target := 5) state4 call enteredWF homes right (by simp) 2
      (by rfl) (by rfl) found (by rfl) post
    exact continuation
  obtain ⟨fuel, final, returned, ran, result⟩ := WP.adequate.mp body
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
