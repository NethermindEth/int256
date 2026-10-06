import UInt256.Methods.Add.ScalarLeftMemory
import UInt256.Methods.Add.SmallChecked

namespace UInt256Proof.Safety

open CIL.Safety

def scalarSmallDecision (swapped : Bool) : Nat :=
  if swapped then scalarSecondDecision else scalarFirstDecision

def scalarSmallCall (swapped : Bool) : Nat :=
  let first := Extracted.addScalarBody.code.findIdx fun op => match op with
    | .call callee _ => callee == Extracted.addScalarUInt64Index
    | _ => false
  if swapped then first + 1 + (Extracted.addScalarBody.code.drop (first + 1)).findIdx (fun op =>
    match op with | .call callee _ => callee == Extracted.addScalarUInt64Index | _ => false)
  else first

def scalarSmallSource (swapped : Bool) (left right : Reference) : Reference :=
  if swapped then right else left

theorem scalar_small_prefix (swapped : Bool) (left right output home : Reference) (word : BitVec 64)
    (frame : Frame) (memory : Memory) {flag : BitVec 32}
    (formed : form memory (scalarSmallSource swapped left right) = .ok (scalarSmallSource swapped left right))
    (outputFormed : form memory output = .ok output)
    (slot : frame.locals[if swapped then 1 else 0]? = some (.bytes .word64 home))
    (loaded : read memory home 8 1 = .ok (numberBytes word.toNat 8))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex (scalarSmallCall swapped)
        (UInt256Model.Safety.binaryArguments left right output ++ [.scalar (.i32 flag)]) frame
        [.reference (.address output), .scalar (.i64 word),
          .reference (.address (scalarSmallSource swapped left right))] memory = .ok (result, returned) ∧
      post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex (scalarSmallDecision swapped)
        (UInt256Model.Safety.binaryArguments left right output ++ [.scalar (.i32 flag)]) frame [.scalar (.i64 0)] memory = .ok (result, returned) ∧
      post result returned := by
  have reading := load_local_word64_of_read loaded
  cases swapped
  all_goals
    conv in (scalarSmallDecision _) => cbv
    conv at continuation in (scalarSmallCall _) => cbv
    dsimp [scalarSmallSource] at formed continuation
    dsimp at slot
    repeat'
      first
      | exact continuation
      | simp (config := { failIfUnchanged := false })
        apply run_next_exists post
        · simp only [cil_code]; rfl
        · simp only [cil_code]; rfl
        · simp (config := { implicitDefEqProofs := false })
            [cil_code, scalarArguments, UInt256Model.Safety.binaryArguments, step,
              checkedValue, numericValue, formValue, formed, outputFormed, slot, reading,
              pureArity, scalars, CIL.step, CIL.truth, checkedAt, Except.mapError,
              Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩

theorem scalar_small_return (swapped : Bool) (args : List Value) (flag : BitVec 32)
    (frame : Frame) (memory : Memory) :
    run Extracted.program 1 Extracted.addScalarIndex (scalarSmallCall swapped + 1)
      args frame [.scalar (.i32 flag)] memory =
        .ok (leaveFrame frame memory, [.scalar (.i32 flag)]) := by
  cases swapped
  all_goals
    conv in (scalarSmallCall _) => cbv
    simp only [Nat.reduceAdd]
    rw [run]
    simp [cil_code, step, checkedValue, numericValue,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms scalar_small_prefix
#print axioms scalar_small_return

end UInt256Proof.Safety
