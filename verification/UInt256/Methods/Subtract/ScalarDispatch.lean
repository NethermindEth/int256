import CIL.StepEquations
import CIL.Safety.Equations
import UInt256.Methods.Subtract.Vector128Entry
import UInt256.Methods.Subtract.SmallHelper
import CIL.Safety.WordLocals
import CIL.Safety.Forwarders

/-! The scalar Subtract dispatcher saves the right low limb, then forwards a small right
    operand to the small-word helper and any other to the 128-bit vector helper. -/

namespace UInt256Proof.Subtract.Profile
open CIL.Safety

def subtractScalarUnreachable : CIL.Op := .unsupported "Unreachable under selected profile"

/-- AdvSimd skips the SSE4.2 guard; both ISAs share the right-small test and the vector call. -/
def subtractScalarGuard (adv : Bool) : List CIL.Op :=
  [if adv then subtractScalarUnreachable else .feature .sse42,
   if adv then subtractScalarUnreachable else .brzero 26]

def subtractScalarBody (profile : CIL.FeatureProfile) (vectorIndex smallIndex : Nat) : CIL.Method :=
  { profile := profile, returnsValue := true,
    locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
    localKinds := [.word64, .word64, .word64, .word64, .word64, .word64],
    parameterHomes := [], staticSites := [],
    code := [.arg 1, .fieldAt 0 8, .setLocal 0, .arg 1, .fieldAt 8 8, .arg 1, .fieldAt 16 8, .bor,
      .arg 1, .fieldAt 24 8, .bor, .brnonzero 17, .arg 0, .local 0, .arg 2, .call smallIndex 3,
      .ret (some .unsigned8), .feature .advSimd, .brnonzero 21] ++ subtractScalarGuard profile.advSimd ++
      [.arg 0, .arg 1, .arg 2, .call vectorIndex 3, .ret (some .unsigned8)] ++
      List.replicate 41 subtractScalarUnreachable }

end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.Subtract.Safety

/-- Certify the dispatcher and every visited state from ordinary caller views: a right
    operand of one limb takes the small helper, any other the 128-bit vector helper. -/
theorem checked_subtract_scalar_contract (program : CIL.Program) (method vectorIndex smallIndex borrow storage : Nat)
    (profile : CIL.FeatureProfile) (found : program[method]? = some (subtractScalarBody profile vectorIndex smallIndex))
    (vectorFound : program[vectorIndex]? = some (subtractVectorBody profile borrow storage))
    (smallFound : program[smallIndex]? = some (subtractSmallBody profile storage))
    (borrowFound : program[borrow]? = some (borrowBody profile))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (sse : profile.advSimd = false → profile.sse2 = true)
    (ssse : profile.advSimd = false → profile.ssse3 = true)
    (sse42 : profile.advSimd = false → profile.sse42 = true)
    (memory : Memory) (left right output : Reference)
    (call : CallingConditions program memory [left, right] [output]) :
    ∃ fuel final returned,
      InvocationCertificate program method (binaryArguments left right output) memory fuel final returned ∧
      SubtractResult memory final returned left right output := by
  let post := fun final returned => SubtractResult memory final returned left right output
  obtain ⟨frame, entered, setup, numeric, _, enteredFormed⟩ :=
    numeric_frame_setup (subtractScalarBody profile vectorIndex smallIndex)
      (List.replicate 6 ⟨.word64, .i64 0, 0, rfl⟩) rfl rfl rfl rfl rfl memory
      (binaryArguments left right output) call.1.1
  have owned : ∀ id ∈ frame.owned, memory.nextIdentity ≤ id :=
    fun id member => ((enterFrame_fresh _ _ _ _ _ setup).2 id member).1
  suffices executed : ∃ fuel final returned,
      run program fuel method 0 (binaryArguments left right output) frame [] entered =
        .ok (final, returned) ∧ post final returned by
    obtain ⟨fuel, final, returned, ran, result⟩ := executed
    exact ⟨fuel, final, returned, .of_run call.1.wellFormed call.2 found
      (checkedValues_of_valid call.binary_arguments_valid) setup ran, result⟩
  have enteredCall := call.after_frame_setup setup
  have valid := enteredCall.1
  have preserved := enterFrame_preserves_caller_memory _ _ _ _ _ setup
  cil_contract_steps (snapshots := LocalSnapshots.empty entered frame.locals) 11
    [found, binaryArguments, call.input_words_kept preserved right (by simp)]
  have currentCall : CallingConditions program storedLocal [left, right] [output] :=
    ⟨valid, write_preserves_static_world _ _ _ _ _ _ enteredCall.2 localWrite⟩
  have next := Nat.le_trans (enterFrame_fresh _ _ _ _ _ setup).1.next
    (write_extends_allocations _ _ _ _ _ localWrite).next
  have fl := currentCall.input_formed (reference := left) (by simp)
  have fr := currentCall.input_formed (reference := right) (by simp)
  have fo := currentCall.output_formed (reference := output) (by simp)
  by_cases small : inputLimb memory right 1 ||| inputLimb memory right 2 |||
    inputLimb memory right 3 = 0#64
  · obtain ⟨childFuel, after, values, certified, result⟩ :=
      small_checked program smallIndex storage profile smallFound storageFound storedLocal left
        output (inputLimb memory right 0)
        ⟨currentCall.1.mono (by simp) (fun _ member => member), currentCall.2⟩
    obtain rfl := result.underflow
    have keptRight : inputValue storedLocal right = inputValue memory right := by
      simp only [inputValue,
        call.input_bytes_of_memory_below preserved (reference := right) (by simp)]
    have finish : ∃ fuel final returned,
        run program fuel method 15 (binaryArguments left right output) frame
          [.reference (.address output), .scalar (.i64 (inputLimb memory right 0)),
            .reference (.address left)] storedLocal = .ok (final, returned) ∧
          post final returned :=
      run_call_post found (by rfl) (by cil_checked_step [smallArguments, fl, fo])
        ⟨childFuel, certified.1⟩
        (run_return_exists found (by rfl)
          (step_return_unchanged (narrow := some .unsigned8) rfl rfl rfl
            ⟨_, rfl, CIL.NarrowKind.extend_ite_one_zero _ _⟩) rfl
          (subtract_result_retire call preserved.cells next owned
            (result.as_subtract keptRight small)))
    cil_contract_steps (snapshots := localSnapshots)
      [small, binaryArguments, fl, fo] until finish
  · obtain ⟨childFuel, final, returned, certified, result⟩ :=
      checked_subtract_vector_contract program vectorIndex borrow storage profile vectorFound
        borrowFound storageFound sse ssse storedLocal left right output currentCall
    obtain rfl := result.flag
    have finish := run_call_post (post := post) found (pc := 24)
      (args := binaryArguments left right output) (by rfl)
      (step_call_loaded currentCall.binary_arguments_valid rfl) ⟨childFuel, certified.1⟩
      (run_return_exists found (by rfl)
        (step_return_unchanged (narrow := some .unsigned8) rfl rfl rfl
          ⟨_, rfl, CIL.NarrowKind.extend_ite_one_zero _ _⟩) rfl
        (subtract_result_retire call preserved.cells next owned result))
    cases adv : profile.advSimd
    · cil_contract_steps [small, adv, sse42 adv, binaryArguments, fl, fr, fo] until finish
    · cil_contract_steps [small, adv, binaryArguments, fl, fr, fo] until finish

end UInt256Proof.Subtract.Profile
