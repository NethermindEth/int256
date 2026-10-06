import UInt256.Methods.Compare.PrimitiveSafetyWrapper

namespace UInt256Proof.Compare.PrimitiveSafety
open CIL.Safety UInt256Model.Safety

def wrapperSigned32 : Bool := Extracted.entryBody.code.any fun op =>
  match op with | .convI8 => true | _ => false

def widen32 (word : BitVec 32) : BitVec 64 :=
  if wrapperSigned32 then word.signExtend 64 else word.zeroExtend 64

theorem prefix32 : Prefix CIL.Value.i32 widen32 := by
  intro memory input word frame call post continuation
  have formed := call.input_formed (reference := input) (by simp)
  have pc : wrapperCall = 3 := by rfl
  conv in wrapperScalarFirst => cbv
  conv at continuation in wrapperScalarFirst => cbv
  conv at continuation in leafScalarFirst => cbv
  have signed : wrapperSigned32 = wrapperSigned32 := rfl
  conv at signed => rhs; cbv
  simp only [pc, widen32, signed, ite_true, ite_false, Bool.false_eq_true] at continuation
  iterate 3
    apply run_next_exists post
    · simp only [cil_code]; rfl
    · simp only [cil_code]; rfl
    · simp (config := { implicitDefEqProofs := false })
        [step, pureArity, scalars, CIL.step, scalarOperatorArguments, scalarArguments, checkedValue, numericValue, formValue, formed,
          checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      try (exact ⟨rfl, rfl, rfl, rfl⟩)
      done
  simpa only [scalarOperatorArguments, scalarArguments, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, ite_true, ite_false, Bool.false_eq_true] using continuation

theorem checked32 : ScalarOperatorContract wrapperScalarFirst wrapperNegate CIL.Value.i32
    (fun input word => predicate leafSigned leafScalarFirst input (widen32 word))
    Extracted.program Extracted.entryIndex :=
  wrapper_checked CIL.Value.i32 widen32 (fun _ => rfl) prefix32

#print axioms prefix32
#print axioms checked32
end UInt256Proof.Compare.PrimitiveSafety
