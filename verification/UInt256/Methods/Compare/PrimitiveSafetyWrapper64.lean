import UInt256.Methods.Compare.PrimitiveSafetyWrapper

namespace UInt256Proof.Compare.PrimitiveSafety
open CIL.Safety UInt256Model.Safety

theorem prefix64 : Prefix CIL.Value.i64 id := by
  intro memory input word frame call post continuation
  have formed := call.input_formed (reference := input) (by simp)
  have pc : wrapperCall = 2 := by rfl
  conv in wrapperScalarFirst => cbv
  conv at continuation in wrapperScalarFirst => cbv
  conv at continuation in leafScalarFirst => cbv
  simp only [pc, id_eq] at continuation
  iterate 2
    apply run_next_exists post
    · simp only [cil_code]; rfl
    · simp only [cil_code]; rfl
    · simp (config := { implicitDefEqProofs := false })
        [step, scalarOperatorArguments, scalarArguments, checkedValue, numericValue, formValue, formed,
          checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      try (exact ⟨rfl, rfl, rfl, rfl⟩)
      done
  simpa only [scalarOperatorArguments, scalarArguments, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, ite_true, ite_false, Bool.false_eq_true] using continuation

theorem checked64 : ScalarOperatorContract wrapperScalarFirst wrapperNegate CIL.Value.i64
    (predicate leafSigned leafScalarFirst) Extracted.program Extracted.entryIndex :=
  wrapper_checked CIL.Value.i64 id (fun _ => rfl) prefix64

#print axioms prefix64
#print axioms checked64
end UInt256Proof.Compare.PrimitiveSafety
