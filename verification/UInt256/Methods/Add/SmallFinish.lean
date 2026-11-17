import UInt256.Methods.Add.SmallMemory
import UInt256.Safety.CallerSetup
import CIL.Safety.StepComposition
import UInt256.Safety.StorageSelection
import UInt256.Arithmetic.Carry
import CIL.Safety.ReturnMemory

namespace UInt256Proof.Safety

open CIL.Safety

theorem small_storage_word_order : storageWordOrder =
    Extracted.storeLimbsBody.code.filterMap fun op =>
      match op with | .arg (index + 1) => some index | _ => none :=
  storageWordOrder_of_found (index := Extracted.storeLimbsIndex) (by rfl) (by rfl)

def smallStoreCall : Nat → Nat
  | 0 => Extracted.addScalarUInt64Body.code.findIdx fun op => match op with
      | .call callee _ => callee == Extracted.storeLimbsIndex
      | _ => false
  | n + 1 =>
      let start := smallStoreCall n + 1
      start + (Extracted.addScalarUInt64Body.code.drop start).findIdx fun op => match op with
        | .call callee _ => callee == Extracted.storeLimbsIndex
        | _ => false

def smallBranchFlag (branch : Fin 5) : BitVec 32 := if branch.val = 4 then 1 else 0

theorem small_return (branch : Fin 5) (args : List Value) (frame : Frame) (memory : Memory) :
    run Extracted.program (Extracted.addScalarUInt64Body.code.length + 1)
      Extracted.addScalarUInt64Index (smallStoreCall branch.val + 1) args frame [] memory =
        .ok (leaveFrame frame memory, [.scalar (.i32 (smallBranchFlag branch))]) := by
  conv in Extracted.addScalarUInt64Body.code.length => cbv
  obtain ⟨branch, bound⟩ := branch
  have cases : branch = 0 ∨ branch = 1 ∨ branch = 2 ∨ branch = 3 ∨ branch = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  all_goals conv in (smallStoreCall _) => cbv
  all_goals
    simp only [cil_code, Nat.reduceAdd]
    apply Eq.trans
    · apply run_next
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [step, cil_guard, observerCount, pureArity,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    · simp [run, cil_code, step, cil_guard, observerCount, CIL.NarrowKind.extend, smallBranchFlag, checkedValue, numericValue,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

end UInt256Proof.Safety

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

structure SmallResult (original final : CIL.Safety.Memory) (values : List Value)
    (input output : Reference) (word : BitVec 64) (flag : BitVec 32) : Prop where
  wellFormed : final.WellFormed
  value : inputValue final output = inputValue original input + BitVec.ofNat 256 word.toNat
  flagValue : values = [.scalar (.i32 flag)]
  writable : access final output 32 1 true = .ok ()
  footprint : ∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset →
    final.cells id offset = original.cells id offset

theorem small_store_finish (branch : Fin 5) (original entered current : CIL.Safety.Memory)
    (frame : Frame) (input output : Reference) (word : BitVec 64) (words : Fin 4 → BitVec 64)
    (call : CallingConditions Extracted.program original [input] [output])
    (setup : enterFrame Extracted.addScalarUInt64Body (smallArguments input output word) original =
      .ok (frame, entered))
    (currentCall : CallingConditions Extracted.program current [input] [output])
    (preserved : ∀ id, id < original.nextIdentity → ∀ offset,
      current.cells id offset = original.cells id offset)
    (math : UInt256Model.value words = inputValue original input + BitVec.ofNat 256 word.toNat) :
    ∃ fuel final values,
      run Extracted.program fuel Extracted.addScalarUInt64Index (smallStoreCall branch.val)
        (smallArguments input output word) frame
        (storageArguments output (words 0) (words 1) (words 2) (words 3)).reverse current = .ok (final, values) ∧
      SmallResult original final values input output word (smallBranchFlag branch) := by
  have formed := currentCall.output_formed (by simp : output ∈ [output])
  apply run_store_limbs storage_contract [input] output (words 0) (words 1) (words 2) (words 3)
    (fun final values => SmallResult original final values input output word (smallBranchFlag branch))
    (body := Extracted.addScalarUInt64Body) (op := .call Extracted.storeLimbsIndex 5)
  · simp only [cil_code]
  · obtain ⟨branch, bound⟩ := branch
    have cases : branch = 0 ∨ branch = 1 ∨ branch = 2 ∨ branch = 3 ∨ branch = 4 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl
    all_goals conv in (smallStoreCall _) => cbv
    all_goals simp only [cil_code]
  · unfold storageArguments
    rw [small_storage_word_order]
    repeat' (conv in (List.filterMap _ Extracted.storeLimbsBody.code) => cbv)
    simp [List.range_succ, List.findIdx, step, cil_guard, observerCount, checkedValue, numericValue, formValue, formed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl, rfl⟩
  · exact currentCall
  · intro stored valid outside _ value
    obtain ⟨outputAllocation, outputPresent, _, _⟩ := formed_reference_live _ _ _
      (call.output_formed (by simp : output ∈ [output]))
    have outputOld := (call.1.1.1 _ _ outputPresent).1
    have fresh := enterFrame_fresh _ _ _ _ _ setup
    have retained := leaveFrame_preserves_memory_below frame stored original.nextIdentity
      (fun id member => (fresh.2 id member).1)
    refine ⟨Extracted.addScalarUInt64Body.code.length + 1, leaveFrame frame stored,
      [.scalar (.i32 (smallBranchFlag branch))], small_return branch _ _ _, ?_⟩
    have bytes : (fun offset => ((leaveFrame frame stored).cells output.allocation offset).bits) =
        (fun offset => (stored.cells output.allocation offset).bits) := by
      funext offset
      rw [retained.cells output.allocation outputOld offset]
    refine ⟨leaveFrame_preserves_wellFormed _ _ valid.1.1, ?_, rfl, ?_, ?_⟩
    · have packed : inputValue (leaveFrame frame stored) output = UInt256Model.value words := by
        simpa only [inputValue, bytes, UInt256Model.value] using value
      exact packed.trans math
    · exact (retained.access output outputOld 32 1 true).trans
        (valid.1.writable (wordView output) (by simp))
    · intro id old offset untouched
      exact (retained.cells id old offset).trans ((outside id offset untouched).trans (preserved id old offset))

end UInt256Proof.Safety
