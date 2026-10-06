import UInt256.Methods.Subtract.ScalarBorrowSegments
import UInt256.Methods.Subtract.BorrowArithmetic

namespace UInt256Proof.Subtract.Safety

open CIL.Safety

def scalarStoreCall : Nat :=
  scalarBody.code.findIdx fun op => match op with
    | .call callee _ => callee == Extracted.storeLimbsIndex
    | _ => false

theorem scalar_store_prefix (left right output : Reference)
    (frame : Frame) (memory : Memory) (results : Fin 4 → Reference) (words : Fin 4 → BitVec 64)
    (outputFormed : form memory output = .ok output)
    (slots : ∀ i, frame.locals[i.val + 2]? = some (.bytes .word64 (results i)))
    (reads : ∀ i, read memory (results i) 8 1 = .ok (numberBytes (words i).toNat 8))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel scalarIndex scalarStoreCall
        (UInt256Model.Safety.binaryArguments left right output)
        frame [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
          .scalar (.i64 (words 0)), .reference (.address output)] memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel scalarIndex (scalarBorrowCall 3 + 1)
        (UInt256Model.Safety.binaryArguments left right output)
        frame [] memory = .ok (result, returned) ∧ post result returned := by
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  conv in (scalarBorrowCall _) => cbv
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
      · exact found
      · rfl
      · simp (config := { implicitDefEqProofs := false })
          [UInt256Model.Safety.binaryArguments, step, checkedValue, formValue, outputFormed, s0, s1, s2, s3, r0, r1, r2, r3,
            checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩


theorem scalar_return (args : List Value) (frame : Frame) (memory : Memory)
    (borrowHome : Reference) (borrow : BitVec 64)
    (slot : frame.locals[1]? = some (.bytes .word64 borrowHome))
    (loaded : read memory borrowHome 8 1 = .ok (numberBytes borrow.toNat 8)) :
    run Extracted.program (scalarBody.code.length + 1) scalarIndex
      (scalarStoreCall + 1) args frame [] memory =
        .ok (leaveFrame frame memory, [.scalar (.i32 (scalarUnderflowFlag borrow))]) := by
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  conv in scalarBody.code.length => cbv
  conv in scalarStoreCall => cbv
  have tailMetadata : scalarBody.code[scalarStoreCall + 5]? = some .ret ∧ scalarBody.returnsValue = true := by
    constructor <;> rfl
  conv at tailMetadata in scalarStoreCall => cbv
  simp only [Nat.reduceAdd] at tailMetadata
  have reading := load_local_word64_of_read loaded
  simp only [Nat.reduceAdd]
  repeat'
    first
    | apply Eq.trans
      · apply run_next
        · exact found
        · rfl
        · simp (config := { implicitDefEqProofs := false })
            [found, step, slot, reading, checkedValue, numericValue,
              pureArity, scalars, CIL.step, CIL.binary, instruction,
              Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    | solve
      | rw [run]
        simp (config := { implicitDefEqProofs := false })
          [found, tailMetadata.1, tailMetadata.2, step, checkedValue, numericValue, scalarUnderflowFlag,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms scalar_return
#print axioms scalar_store_prefix
end UInt256Proof.Subtract.Safety
