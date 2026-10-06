import UInt256.Methods.Add.ScalarCarrySegments
import UInt256.Methods.Add.StorageCall
import UInt256.Methods.Add.CarryArithmetic

namespace UInt256Proof.Safety

open CIL.Safety

def scalarStoreCall : Nat :=
  Extracted.addScalarBody.code.findIdx fun op => match op with
    | .call callee _ => callee == Extracted.storeLimbsIndex
    | _ => false

theorem scalar_store_prefix (left right output : Reference) (extra : List Value)
    (frame : Frame) (memory : Memory) (results : Fin 4 → Reference) (words : Fin 4 → BitVec 64)
    (outputFormed : form memory output = .ok output)
    (slots : ∀ i, frame.locals[i.val + 3]? = some (.bytes .word64 (results i)))
    (reads : ∀ i, read memory (results i) 8 1 = .ok (numberBytes (words i).toNat 8))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex scalarStoreCall
        ([.reference (.address left), .reference (.address right), .reference (.address output)] ++ extra)
        frame (storageArguments output (words 0) (words 1) (words 2) (words 3)).reverse memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall 3 + 1)
        ([.reference (.address left), .reference (.address right), .reference (.address output)] ++ extra)
        frame [] memory = .ok (result, returned) ∧ post result returned := by
  unfold storageArguments at continuation
  conv at continuation in storageWordOrder => cbv
  simp [List.range_succ, List.findIdx] at continuation
  conv in (scalarCarryCall _) => cbv
  simp only [Nat.reduceAdd]
  have s0 := slots 0
  have s1 := slots 1
  have s2 := slots 2
  have s3 := slots 3
  dsimp at s0 s1 s2 s3
  simp only [CIL.fin_val_three, Nat.reduceAdd] at s3
  have r0 := load_local_word64_of_read (reads 0)
  have r1 := load_local_word64_of_read (reads 1)
  have r2 := load_local_word64_of_read (reads 2)
  have r3 := load_local_word64_of_read (reads 3)
  repeat'
    first
    | exact continuation
    | apply run_next_exists post
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · simp (config := { implicitDefEqProofs := false })
          [cil_code, step, checkedValue, formValue, outputFormed, s0, s1, s2, s3, r0, r1, r2, r3,
            checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩

theorem scalar_return (args : List Value) (frame : Frame) (memory : Memory)
    (carryHome : Reference) (carry : BitVec 64)
    (slot : frame.locals[2]? = some (.bytes .word64 carryHome))
    (loaded : read memory carryHome 8 1 = .ok (numberBytes carry.toNat 8)) :
    run Extracted.program (Extracted.addScalarBody.code.length + 1) Extracted.addScalarIndex
      (scalarStoreCall + 1) args frame [] memory =
        .ok (leaveFrame frame memory, [.scalar (.i32 (scalarOverflowFlag carry))]) := by
  conv in scalarStoreCall => cbv
  have reading := load_local_word64_of_read loaded
  simp only [cil_code]
  simp only [Nat.reduceAdd]
  repeat'
    first
    | apply Eq.trans
      · apply run_next
        · simp only [cil_code]; rfl
        · simp only [cil_code]; rfl
        · simp (config := { implicitDefEqProofs := false })
            [cil_code, step, slot, reading, checkedValue, numericValue,
              pureArity, scalars, CIL.step, CIL.binary, instruction,
              Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    | solve
      | rw [run]
        simp (config := { implicitDefEqProofs := false })
          [cil_code, step, checkedValue, numericValue, scalarOverflowFlag,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms scalar_store_prefix
#print axioms scalar_return

end UInt256Proof.Safety
