import UInt256.Methods.Add.SmallSum
import UInt256.Methods.Add.StorageCall
import UInt256.Arithmetic.Carry
import CIL.Safety.ReturnMemory

namespace UInt256Proof.Safety

open CIL.Safety

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
          [step, pureArity,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    · rw [run]
      simp [cil_code, step, smallBranchFlag, checkedValue, numericValue,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem small_no_carry_prefix (input output sumHome : Reference) (word : BitVec 64)
    (frame : Frame) (memory : Memory) (homes : Fin 4 → Reference) (words : Fin 4 → BitVec 64)
    (noCarry : ¬ words 0 + word < words 0)
    (formed : form memory output = .ok output)
    (slots : ∀ i : Fin 4, frame.locals[i.val]? = some (.bytes .word64 (homes i)))
    (reads : ∀ i, read memory (homes i) 8 1 = .ok (numberBytes (words i).toNat 8))
    (sumSlot : frame.locals[4]? = some (.bytes .word64 sumHome))
    (sumRead : read memory sumHome 8 1 = .ok (numberBytes (words 0 + word).toNat 8))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index (smallStoreCall 0)
        (smallArguments input output word) frame
        (storageArguments output (words 0 + word) (words 1) (words 2) (words 3)).reverse memory = .ok (result, returned) ∧
      post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index smallCarryDecision
        (smallArguments input output word) frame
        [.scalar (.i64 (words 0)), .scalar (.i64 (words 0 + word))] memory = .ok (result, returned) ∧
      post result returned := by
  unfold storageArguments at continuation
  conv at continuation in storageWordOrder => cbv
  simp [List.range_succ, List.findIdx] at continuation
  conv in smallCarryDecision => cbv
  conv at continuation in (smallStoreCall _) => cbv
  have s1 := slots 1
  have s2 := slots 2
  have s3 := slots 3
  dsimp at s1 s2 s3
  simp only [show (3 : Fin 4).val = 3 from rfl] at s3
  have r1 := load_local_word64_of_read (reads 1)
  have r2 := load_local_word64_of_read (reads 2)
  have r3 := load_local_word64_of_read (reads 3)
  have r4 := load_local_word64_of_read sumRead
  repeat'
    first
    | exact continuation
    | simp (config := { failIfUnchanged := false }) [noCarry]
      apply run_next_exists post
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [cil_code, smallArguments, step, checkedValue, numericValue, formValue, formed,
            s1, s2, s3, sumSlot, r1, r2, r3, r4, pureArity, scalars, CIL.step,
            checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩

#print axioms small_return
#print axioms small_no_carry_prefix

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
  apply run_store_limbs [input] output (words 0) (words 1) (words 2) (words 3)
    (fun final values => SmallResult original final values input output word (smallBranchFlag branch))
    (body := Extracted.addScalarUInt64Body) (op := .call Extracted.storeLimbsIndex 5)
  · simp only [cil_code]
  · obtain ⟨branch, bound⟩ := branch
    have cases : branch = 0 ∨ branch = 1 ∨ branch = 2 ∨ branch = 3 ∨ branch = 4 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl
    all_goals conv in (smallStoreCall _) => cbv
    all_goals simp only [cil_code]
  · unfold storageArguments
    repeat' (conv in storageWordOrder => cbv)
    simp [List.range_succ, List.findIdx, step, checkedValue, numericValue, formValue, formed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl⟩
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
        (valid.1.2.2 (wordView output) (by simp))
    · intro id old offset untouched
      exact (retained.cells id old offset).trans ((outside id offset untouched).trans (preserved id old offset))

theorem small_no_carry_value (memory : CIL.Safety.Memory) (input : Reference) (word : BitVec 64)
    (noCarry : ¬ inputLimb memory input 0 + word < inputLimb memory input 0) :
    UInt256Model.value (fun i : Fin 4 => if i.val = 0 then inputLimb memory input 0 + word else inputLimb memory input i) =
      inputValue memory input + BitVec.ofNat 256 word.toNat := by
  have sum := UInt256Proof.small_result_sum (inputLimb memory input) word
  have initial : UInt256Model.value (inputLimb memory input) = inputValue memory input :=
    UInt256Proof.input_value (fun offset => (memory.cells input.allocation offset).bits) input.offset
  rw [initial] at sum
  simpa [UInt256Model.value, UInt256Proof.smallResult, UInt256Proof.singleLimb,
    show (3 : Fin 4).val = 3 from rfl, noCarry] using sum

#print axioms small_store_finish
#print axioms small_no_carry_value

theorem small_no_carry_checked (memory : CIL.Safety.Memory)
    (input output : Reference) (word : BitVec 64)
    (call : CallingConditions Extracted.program memory [input] [output])
    (noCarry : ¬ inputLimb memory input 0 + word < inputLimb memory input 0) :
    ∃ fuel final values,
      invoke Extracted.program fuel Extracted.addScalarUInt64Index (smallArguments input output word)
        memory = .ok (final, values) ∧ SmallResult memory final values input output word 0 := by
  let post := fun final values => SmallResult memory final values input output word 0
  apply small_sum_invocation memory input output word call post
  intro frame entered slots tailSlots sumHome after setup layout _ saved sumSlot sumRead
  have candidates := fun i : Fin 4 => saved.completed i i.isLt
  let homes : Fin 4 → Reference := fun i => Classical.choose (candidates i)
  have facts := fun i : Fin 4 => Classical.choose_spec (candidates i)
  have fullSlots : ∀ i : Fin 4, frame.locals[i.val]? = some (.bytes .word64 (homes i)) := by
    intro i
    have inside := (List.getElem?_eq_some_iff.mp (facts i).1).1
    rw [layout, List.getElem?_append_left inside]
    exact (facts i).1
  apply small_no_carry_prefix input output sumHome word frame after homes (inputLimb memory input)
    noCarry (saved.call.output_formed (by simp)) fullSlots (fun i => (facts i).2.2) sumSlot sumRead post
  let words := fun i : Fin 4 => if i.val = 0 then inputLimb memory input 0 + word else inputLimb memory input i
  exact small_store_finish 0 memory entered after frame input output word words call setup saved.call
    saved.preserved.cells (small_no_carry_value memory input word noCarry)

#print axioms small_no_carry_checked

end UInt256Proof.Safety
