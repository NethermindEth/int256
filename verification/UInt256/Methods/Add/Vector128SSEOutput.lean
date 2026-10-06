import UInt256.Methods.Add.Vector128SSECarrySetup
import UInt256.Methods.Add.StorageCall

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety UInt256Proof.AddSubtract.Safety

theorem vector128_sse_store_prefix (left right output : Reference) (extra : List Value)
    (frame : Frame) (memory : Memory) (results : Fin 4 → Reference) (words : Fin 4 → BitVec 64)
    (outputFormed : form memory output = .ok output)
    (slots : ∀ i, frame.locals[i.val + 16]? = some (.bytes .word64 (results i)))
    (reads : ∀ i, read memory (results i) 8 1 = .ok (numberBytes (words i).toNat 8))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel vector128Index 198
        ([.reference (.address left), .reference (.address right), .reference (.address output)] ++ extra)
        frame [.scalar (.i64 (words 3)), .scalar (.i64 (words 2)), .scalar (.i64 (words 1)),
          .scalar (.i64 (words 0)), .reference (.address output)] memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 193
        ([.reference (.address left), .reference (.address right), .reference (.address output)] ++ extra)
        frame [] memory = .ok (result, returned) ∧ post result returned := by
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
    | apply run_next_exists post (by rfl : Extracted.program[vector128Index]? = some vector128Body) (by rfl)
      simp (config := { implicitDefEqProofs := false })
          [cil_code, step, checkedValue, formValue, outputFormed, s0, s1, s2, s3, r0, r1, r2, r3,
            checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩

theorem vector128_sse_return (args : List Value) (frame : Frame) (memory : Memory)
    (carryHome : Reference) (carry : BitVec 64)
    (slot : frame.locals[15]? = some (.bytes .word64 carryHome))
    (loaded : read memory carryHome 8 1 = .ok (numberBytes carry.toNat 8)) :
    run Extracted.program 5 vector128Index 199 args frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if BitVec.ofNat 64 0 < carry then 1 else 0))]) := by
  have reading := load_local_word64_of_read loaded
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  repeat'
    first
    | apply Eq.trans
      · apply run_next found (by rfl)
        simp (config := { implicitDefEqProofs := false })
          [step, slot, reading, checkedValue, numericValue, pureArity, scalars,
            CIL.step, CIL.binary, instruction, Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    | solve
      | rw [run]
        simp (config := { implicitDefEqProofs := false })
          [found, show vector128Body.code[203]? = some .ret from rfl,
            show vector128Body.returnsValue = true from rfl, step, checkedValue, numericValue,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms vector128_sse_store_prefix
#print axioms vector128_sse_return
end UInt256Proof.Add.Safety
