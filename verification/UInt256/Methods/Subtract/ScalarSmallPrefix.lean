import UInt256.Methods.Subtract.ScalarSafetyPrefix
import UInt256.Methods.Subtract.SmallSafetyFinish

namespace UInt256Proof.Subtract.Safety

open CIL.Safety

def scalarSmallCall : Nat := scalarBody.code.findIdx fun op => match op with
  | .call callee _ => callee == Extracted.subtractScalarUInt64Index | _ => false

theorem scalar_small_prefix (left right output home : Reference) (word : BitVec 64)
    (frame : Frame) (memory : Memory)
    (formed : form memory left = .ok left)
    (outputFormed : form memory output = .ok output)
    (slot : frame.locals[0]? = some (.bytes .word64 home))
    (loaded : read memory home 8 1 = .ok (numberBytes word.toNat 8))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel scalarIndex scalarSmallCall
        (UInt256Model.Safety.binaryArguments left right output) frame
        [.reference (.address output), .scalar (.i64 word),
          .reference (.address left)] memory = .ok (result, returned) ∧
      post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel scalarIndex scalarFirstDecision
        (UInt256Model.Safety.binaryArguments left right output) frame [.scalar (.i64 0)] memory = .ok (result, returned) ∧
      post result returned := by
  have reading := load_local_word64_of_read loaded
  conv in scalarFirstDecision => cbv
  conv at continuation in scalarSmallCall => cbv
  repeat'
    first
    | exact continuation
    | simp (config := { failIfUnchanged := false })
      apply run_next_exists post
      · rfl
      · rfl
      · simp (config := { implicitDefEqProofs := false })
          [cil_code, UInt256Model.Safety.binaryArguments, UInt256Model.Safety.binaryArguments, step,
            checkedValue, numericValue, formValue, formed, outputFormed, slot, reading,
            pureArity, scalars, CIL.step, CIL.truth, checkedAt, Except.mapError,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩

theorem scalar_small_return (args : List Value) (flag : BitVec 32)
    (frame : Frame) (memory : Memory) :
    run Extracted.program 1 scalarIndex (scalarSmallCall + 1)
      args frame [.scalar (.i32 flag)] memory =
        .ok (leaveFrame frame memory, [.scalar (.i32 flag)]) := by
  have found : Extracted.program[scalarIndex]? = some scalarBody := by rfl
  have fetched : scalarBody.code[scalarSmallCall + 1]? = some .ret := by rfl
  have returning : scalarBody.returnsValue = true := by rfl
  rw [run]
  simp [found, fetched, returning, step, checkedValue, numericValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms scalar_small_prefix
#print axioms scalar_small_return

end UInt256Proof.Subtract.Safety
