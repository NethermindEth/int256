import UInt256.Methods.Add.SmallSum
import UInt256.Methods.Add.StorageCall

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
