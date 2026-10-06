import UInt256.Methods.Equality.WrapperSafetyContract

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

def negationCall : Nat := Extracted.entryBody.code.findIdx fun op =>
  match op with | .call _ _ => true | _ => false

theorem negation_prefix (left right : Reference) (frame : Frame) (memory : Memory)
    (call : CallingConditions Extracted.program memory [left, right] [])
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final values,
      run Extracted.program fuel Extracted.entryIndex negationCall
        (readOnlyArguments [left, right]) frame
        [.reference (.address right), .reference (.address left)] memory = .ok (final, values) ∧
      post final values) :
    ∃ fuel final values, run Extracted.program fuel Extracted.entryIndex 0
      (readOnlyArguments [left, right]) frame [] memory = .ok (final, values) ∧ post final values := by
  have fl := call.input_formed (reference := left) (by simp)
  have fr := call.input_formed (reference := right) (by simp)
  conv at continuation in negationCall => cbv
  repeat' first
    | exact continuation
    | (apply run_next_exists post
       · simp only [cil_code]; rfl
       · simp only [cil_code]; rfl
       · simp [readOnlyArguments, step, checkedValue, formValue, fl, fr,
           checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
         try (exact ⟨rfl, rfl, rfl, rfl⟩))

theorem negation_return (args : List Value) (flag : BitVec 32) (frame : Frame) (memory : Memory) :
    run Extracted.program 3 Extracted.entryIndex (negationCall + 1) args frame
      [.scalar (.i32 flag)] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (if flag = 0 then 1 else 0))]) := by
  conv in negationCall => cbv
  simp only [Nat.reduceAdd]
  simp [run, cil_code, step, pureArity, scalars, CIL.step, CIL.binary, instruction,
    checkedValue, numericValue, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms negation_return

end UInt256Proof.Equality.Safety
