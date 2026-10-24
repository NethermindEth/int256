import UInt256.Methods.Compare.PrimitiveWrapper

namespace UInt256Proof.Compare.PrimitiveWrapper
open CIL.Safety UInt256Model.Safety UInt256Proof.Compare.PrimitiveSafety

def widen32 (signed : Bool) (word : BitVec 32) : BitVec 64 :=
  if signed then word.signExtend 64 else word.zeroExtend 64

theorem prefix32 (signed scalarFirst reversed negate : Bool) (program : CIL.Program) (entry callee : Nat)
    (found : program[entry]? = some (method true signed scalarFirst reversed negate callee)) :
    Prefix CIL.Value.i32 (widen32 signed) program entry (callPC true) scalarFirst reversed := by
  cases signed <;> cases scalarFirst <;> cases reversed
  all_goals
    intro memory input word frame call post continuation
    have formed := call.input_formed (reference := input) (by simp)
    iterate 3
      apply run_next_exists post
      · exact found
      · rfl
      · simp (config := { implicitDefEqProofs := false })
          [step, cil_guard, observerCount, pureArity, scalars, CIL.step, CIL.unary, scalarOperatorArguments, scalarArguments,
            checkedValue, numericValue, formValue, formed, checkedAt,
            Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try (exact ⟨rfl, rfl, rfl, rfl⟩)
        done
    simpa only [callPC, scalarOperatorArguments, scalarArguments, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, ite_true, ite_false, Bool.false_eq_true, widen32] using continuation

theorem checked32 (signed leafSigned scalarFirst reversed negate : Bool) (program : CIL.Program) (entry callee : Nat)
    (found : program[entry]? = some (method true signed scalarFirst reversed negate callee))
    (leafFound : program[callee]? = some (PrimitiveLeaf.method leafSigned scalarFirst)) :
    ScalarOperatorContract (scalarFirst != reversed) negate CIL.Value.i32
      (fun input word => predicate leafSigned scalarFirst input (widen32 signed word)) program entry :=
  checked CIL.Value.i32 (widen32 signed) true signed leafSigned scalarFirst reversed negate program entry callee
    found leafFound (fun _ => rfl) (prefix32 signed scalarFirst reversed negate program entry callee found)

#print axioms prefix32
#print axioms checked32
end UInt256Proof.Compare.PrimitiveWrapper
