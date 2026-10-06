import UInt256.Methods.Subtract.SmallSafetySaved
import UInt256.Arithmetic.Borrow
import UInt256.Methods.Add.StorageCall

namespace UInt256Proof.Subtract.Safety

open CIL.Safety

def smallStoreCall : Nat → Nat
  | 0 => Extracted.subtractScalarUInt64Body.code.findIdx fun op => match op with
      | .call callee _ => callee == Extracted.storeLimbsIndex
      | _ => false
  | n + 1 =>
      let start := smallStoreCall n + 1
      start + (Extracted.subtractScalarUInt64Body.code.drop start).findIdx fun op => match op with
        | .call callee _ => callee == Extracted.storeLimbsIndex
        | _ => false

def smallBranchFlag (branch : Fin 5) : BitVec 32 := if branch.val = 4 then 1 else 0

theorem small_return (branch : Fin 5) (args : List Value) (frame : Frame) (memory : Memory) :
    run Extracted.program (Extracted.subtractScalarUInt64Body.code.length + 1)
      Extracted.subtractScalarUInt64Index (smallStoreCall branch.val + 1) args frame [] memory =
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

def smallSelectedBranch (words : Fin 4 → BitVec 64) (word : BitVec 64) : Fin 5 :=
  if ¬ words 0 < word then 0 else if words 1 ≠ 0 then 1 else
    if words 2 ≠ 0 then 2 else if words 3 ≠ 0 then 3 else 4

/-- Follow all five actual branch endings from saved input words to the
    extracted store call with the independently specified difference limbs. -/
theorem small_branch_prefix (input output : Reference) (word : BitVec 64)
    (frame : Frame) (memory : Memory) (homes : Fin 4 → Reference) (words : Fin 4 → BitVec 64)
    (formed : form memory output = .ok output)
    (slots : ∀ i : Fin 4, frame.locals[i.val]? = some (.bytes .word64 (homes i)))
    (reads : ∀ i, read memory (homes i) 8 1 = .ok (numberBytes
      (if h : i.val < 3 then words ⟨i.val + 1, by omega⟩ else words 0 - word).toNat 8))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel Extracted.subtractScalarUInt64Index
        (smallStoreCall (smallSelectedBranch words word).val) (smallArguments input output word) frame
        [.scalar (.i64 (smallDifference words word 3)), .scalar (.i64 (smallDifference words word 2)),
         .scalar (.i64 (smallDifference words word 1)), .scalar (.i64 (smallDifference words word 0)),
         .reference (.address output)] memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.subtractScalarUInt64Index smallFirstDecision
        (smallArguments input output word) frame [.scalar (.i64 word), .scalar (.i64 (words 0))]
        memory = .ok (result, returned) ∧ post result returned := by
  have s0 := slots 0
  have s1 := slots 1
  have s2 := slots 2
  have s3 := slots 3
  have r0 := load_local_word64_of_read (reads 0)
  have r1 := load_local_word64_of_read (reads 1)
  have r2 := load_local_word64_of_read (reads 2)
  have r3 := load_local_word64_of_read (reads 3)
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, CIL.fin_val_three,
    Nat.reduceLT, ↓reduceDIte, Nat.reduceAdd] at s0 s1 s2 s3 r0 r1 r2 r3
  conv in smallFirstDecision => cbv
  by_cases h0 : words 0 < word <;> by_cases h1 : words 1 = BitVec.ofNat 64 0 <;>
    by_cases h2 : words 2 = BitVec.ofNat 64 0 <;> by_cases h3 : words 3 = BitVec.ofNat 64 0
  all_goals
    simp [BitVec.ofNat_eq_ofNat, smallSelectedBranch, smallDifference, h0, h1, h2, h3, not_true_eq_false,
      not_false_eq_true, ↓reduceIte, Fin.val_zero, Fin.val_one, Fin.val_two, CIL.fin_val_three,
      Nat.reduceEqDiff, and_true, and_false] at continuation
    conv at continuation in (smallStoreCall _) => cbv
    repeat' first
      | exact continuation
      | (solve | simpa [h0, h1, h2, h3] using continuation)
      | (simp (config := { failIfUnchanged := false }) [h0, h1, h2, h3]
         apply run_next_exists post
         · simp only [cil_code]; rfl
         · simp only [cil_code]; rfl
         · simp (config := { implicitDefEqProofs := false })
             [h0, h1, h2, h3, cil_code, smallArguments, step, checkedValue, numericValue, formValue, formed,
               s0, s1, s2, s3, r0, r1, r2, r3, pureArity, scalars, CIL.step, CIL.binary,
               checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
           first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

theorem small_selected_flag (words : Fin 4 → BitVec 64) (word : BitVec 64) :
    smallBranchFlag (smallSelectedBranch words word) =
      (if words 0 < word ∧ words 1 = 0 ∧ words 2 = 0 ∧ words 3 = 0 then 1 else 0) := by
  by_cases h0 : words 0 < word <;> by_cases h1 : words 1 = BitVec.ofNat 64 0 <;>
    by_cases h2 : words 2 = BitVec.ofNat 64 0 <;> by_cases h3 : words 3 = BitVec.ofNat 64 0 <;>
    simp [BitVec.ofNat_eq_ofNat, smallBranchFlag, smallSelectedBranch, h0, h1, h2, h3,
      show (3 : Fin 5).val = 3 from rfl, show (4 : Fin 5).val = 4 from rfl]

#print axioms small_selected_flag
#print axioms small_return
#print axioms small_branch_prefix
end UInt256Proof.Subtract.Safety
