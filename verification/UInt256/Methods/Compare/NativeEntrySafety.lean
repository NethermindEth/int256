import UInt256.Methods.Compare.NativeSafetyContract
namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety

def nativeEntryBody (profile : CIL.FeatureProfile) (callee : Nat) : CIL.Method :=
  { profile := profile, returnsValue := true, locals := [], code := [.arg 1, .arg 0, .call callee 2, .ret (some .unsigned8)] }

theorem native_entry_checked (profile : CIL.FeatureProfile) (usesLess inclusive : Bool)
    (program : CIL.Program) (index callee : Nat)
    (found : program[index]? = some (nativeEntryBody profile callee))
    (childFound : program[callee]? = some (nativeBody profile usesLess inclusive))
    (native : profile.avx512FVL = true) (nativeF : profile.avx512F = true)
    (avx2 : profile.avx2 = true) (avx : profile.avx = true) : BinaryReadOnlyInvocation
    (fun left right => .i32 (if nativePredicate usesLess inclusive right left then 1 else 0)) program index := by
  apply forward_readOnly_binary program index 2 callee (nativeEntryBody profile callee)
    (fun left right => .i32 (if nativePredicate usesLess inclusive right left then 1 else 0))
    (fun left right => readOnlyArguments [right, left])
  · exact found
  · rfl
  · rfl
  · rfl
  · intro left right
    simp [FrameSetupFits, InitializersFit, AggregateArgumentsFit, ParameterArgumentsFit, SelectedKindsFit, nativeEntryBody]
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro left right
    split <;> exact ⟨_, rfl, rfl⟩
  · intro memory left right call
    exact native_checked profile usesLess inclusive program callee childFound native nativeF avx2 avx memory right left call.swap_binary_inputs
  · intro memory left right frame call post continuation
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    simp only [readOnlyArguments, List.map_cons, List.map_nil, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append] at continuation
    repeat' first
      | exact continuation
      | (apply run_next_exists post found
         · simp only [nativeEntryBody]; rfl
         · simp (config := { implicitDefEqProofs := false })
             [readOnlyArguments, step, cil_guard, observerCount, checkedValue, formValue,
               fl, fr, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
           try (exact ⟨rfl, rfl, rfl, rfl⟩))
#print axioms native_entry_checked
end UInt256Proof.Compare.Safety
