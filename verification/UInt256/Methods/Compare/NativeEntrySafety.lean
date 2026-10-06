import UInt256.Methods.Compare.NativeSafetyContract

namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety

def nativeEntryBody : CIL.Method := Extracted.program[Extracted.entryIndex]?.getD
  { code := [], locals := [], returnsValue := false }

theorem native_entry_checked : BinaryReadOnlyInvocation
    (fun left right => .i32 (if nativePredicate right left then 1 else 0))
    Extracted.program Extracted.entryIndex := by
  apply forward_readOnly_binary Extracted.program Extracted.entryIndex 2 nativeIndex nativeEntryBody
    (fun left right => .i32 (if nativePredicate right left then 1 else 0))
    (fun left right => readOnlyArguments [right, left])
  · rfl
  · rfl
  · rfl
  · rfl
  · intro left right
    simp [FrameSetupFits, InitializersFit, InitializerFits, AggregateArgumentsFit, nativeEntryBody, cil_code]
  · intros; rfl
  · intros; rfl
  · intro memory left right call
    exact native_checked memory right left call.swap_binary_inputs
  · intro memory left right frame call post continuation
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    simp only [readOnlyArguments, List.map_cons, List.map_nil, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append] at continuation
    repeat' first
      | exact continuation
      | (apply run_next_exists post
         · simp only [cil_code]; rfl
         · simp only [cil_code]; rfl
         · simp (config := { implicitDefEqProofs := false })
             [cil_code, readOnlyArguments, step, checkedValue, numericValue, formValue,
               fl, fr, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
           try (exact ⟨rfl, rfl, rfl, rfl⟩))


#print axioms native_entry_checked
end UInt256Proof.Compare.Safety
