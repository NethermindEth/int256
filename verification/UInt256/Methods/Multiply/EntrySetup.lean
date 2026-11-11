import UInt256.Generated.MethodTemplates
import UInt256.Methods.Multiply.LeftTwoSafety
import UInt256.Methods.Multiply.FullSafety
import UInt256.Methods.Multiply.ScalarSafety
import UInt256.Methods.Multiply.SingleWord
import CIL.Safety.ScalarBranch

/-! The multiplication entry point: its callee layout, private frame and the input words and
    zero masks it saves before dispatching on operand size. -/

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
def multiplyBody (profile : CIL.FeatureProfile) (indices : Indices) : CIL.Method := by_elab
  let body ← Lean.Elab.Term.elabTermAndSynthesize
    (← `(UInt256Proof.Generated.Method.method16 $(Lean.mkIdent `profile) $(Lean.mkIdent `indices).word $(Lean.mkIdent `indices).single $(Lean.mkIdent `indices).bothTwo $(Lean.mkIdent `indices).leftTwo $(Lean.mkIdent `indices).full $(Lean.mkIdent `indices).storage)) none
  let some unfolded ← Lean.Meta.unfoldDefinition? body
    | throwError "Expected generated template application"
  return ← Lean.Meta.withTransparency .default (Lean.Meta.reduce unfolded)
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
      CompleteWritableHomes entered memory.nextIdentity (multiplyBody ctx.profile ctx.indices).localKinds frame.locals ∧
      entered.WellFormed ∧
      PrivateWords ctx.program memory entered entered [left, right] [output] frame (fun _ => none) := by
  have kinds : (multiplyBody ctx.profile ctx.indices).localKinds = List.replicate 8 CIL.LocalKind.word64 := by rfl
  obtain ⟨frame, entered, setup, homes, _, wf⟩ := unknown_frame_setup (multiplyBody ctx.profile ctx.indices)
    (by rfl) (by simp [kinds]) (by simp [kinds]) (by simp [kinds])
    (by simp [kinds]) (by simp [kinds]) (by simp [kinds]) (by rfl) (by rfl) (by rfl) memory (productArgs left right output) call.1.1
  exact ⟨frame, entered, setup, homes, wf, PrivateWords.initial call setup⟩
def inputUpper (memory : Memory) (input : Reference) :=
  inputLimb memory input 2 ||| inputLimb memory input 3

def inputTail (memory : Memory) (input : Reference) :=
  inputLimb memory input 1 ||| inputUpper memory input

def multiplyInputs (original : Memory) (left right : Reference) :=
  rememberWord (rememberWord (rememberWord (rememberWord (rememberWord (rememberWord
    (fun _ => none) 0 (inputLimb original left 0)) 1 (inputLimb original right 0))
    2 (inputUpper original left)) 3 (inputUpper original right))
    4 (inputTail original left)) 5 (inputTail original right)

theorem multiply_prepare (ctx : Context alternative) (original entered current : Memory) (left right output : Reference) (frame : Frame)
    (originalCall : CallingConditions ctx.program original [left, right] [output])
    (enteredWF : entered.WellFormed)
    (homes : CompleteWritableHomes entered original.nextIdentity (multiplyBody ctx.profile ctx.indices).localKinds frame.locals)
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
  have found : ctx.program[ctx.indices.entry]? = some (multiplyBody ctx.profile ctx.indices) :=
    ctx.entry
  apply run_input_to_local (argument := 0) (target := 0) state originalCall enteredWF homes left
    (by simp) 0 (by rfl) (by rfl) found (by rfl) post
  intro _ low0
  apply run_input_to_local (argument := 1) (target := 1) low0 originalCall enteredWF homes right
    (by simp) 0 (by rfl) (by rfl) found (by rfl) post
  intro _ low1
  have formed := low1.call.1.1
  have retained := low1.authority
  have formedLeft := low1.call.input_formed (by simp : left ∈ [left, right])
  have upperLeft := low1.input_field originalCall left (by simp) 2
  have topLeft := low1.input_field originalCall left (by simp) 3
  cil_contract_steps (snapshots := low1.snapshots.toLocalSnapshots)
    [productArgs, formedLeft, upperLeft, topLeft]
  have upper0 := low1.after_word_write homes (by assumption) localWrite
  have formedRight := upper0.call.input_formed (by simp : right ∈ [left, right])
  have upperRight := upper0.input_field originalCall right (by simp) 2
  have topRight := upper0.input_field originalCall right (by simp) 3
  cil_contract_steps (snapshots := localSnapshots) [productArgs, formedRight, upperRight, topRight]
  have upper1 := upper0.after_word_write homes (by assumption) localWrite_1
  have formedLeft := upper1.call.input_formed (by simp : left ∈ [left, right])
  have secondLeft := upper1.input_field originalCall left (by simp) 1
  cil_contract_steps (snapshots := localSnapshots_1) [productArgs, formedLeft, secondLeft]
  have tail0 := upper1.after_word_write homes (by assumption) localWrite_2
  have formedRight := tail0.call.input_formed (by simp : right ∈ [left, right])
  have secondRight := tail0.input_field originalCall right (by simp) 1
  cil_contract_steps (snapshots := localSnapshots_2) [productArgs, formedRight, secondRight]
    until continuation _ (tail0.after_word_write homes (by assumption) localWrite_3)

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

end UInt256Proof.Multiply.Entry
