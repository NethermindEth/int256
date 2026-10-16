import UInt256.Methods.Compare.PrimitiveWrapper

namespace UInt256Proof.Compare.PrimitiveWrapper
open CIL.Safety UInt256Model.Safety UInt256Proof.Compare.PrimitiveSafety

theorem prefix64 (scalarFirst reversed negate : Bool) (program : CIL.Program) (entry callee : Nat)
    (found : program[entry]? = some (method false false scalarFirst reversed negate callee)) :
    Prefix CIL.Value.i64 id program entry (callPC false) scalarFirst reversed := by
  cases scalarFirst <;> cases reversed
  all_goals
    intro memory input word frame call post continuation
    have formed := call.input_formed (reference := input) (by simp)
    iterate 2
      apply run_next_exists post
      · exact found
      · rfl
      · simp (config := { implicitDefEqProofs := false })
          [step, scalarOperatorArguments, scalarArguments, checkedValue, numericValue, formValue, formed,
            checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try (exact ⟨rfl, rfl, rfl, rfl⟩)
        done
    simpa only [callPC, scalarOperatorArguments, scalarArguments, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, ite_true, ite_false, Bool.false_eq_true, id_eq] using continuation

theorem checked64 (leafSigned scalarFirst reversed negate : Bool) (program : CIL.Program) (entry callee : Nat)
    (found : program[entry]? = some (method false false scalarFirst reversed negate callee))
    (leafFound : program[callee]? = some (PrimitiveLeaf.method leafSigned scalarFirst)) :
    ScalarOperatorContract (scalarFirst != reversed) negate CIL.Value.i64
      (predicate leafSigned scalarFirst) program entry :=
  checked CIL.Value.i64 id false false leafSigned scalarFirst reversed negate program entry callee
    found leafFound (fun _ => rfl) (prefix64 scalarFirst reversed negate program entry callee found)

#print axioms prefix64
#print axioms checked64
end UInt256Proof.Compare.PrimitiveWrapper
