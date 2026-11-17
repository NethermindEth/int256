import UInt256.Methods.Compare.NativeSafetyContract

/-! Native comparison wrappers forward reversed arguments through checked shared loading rules. -/

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
    apply run_load_arguments found call.readOnly_arguments_valid (plainLoads [1, 0]) 0 []
      (readOnlyArguments [right, left])
    · intro position load selected
      match position with
      | 0 => cases selected; rfl
      | 1 => cases selected; rfl
      | _ + 2 => simp [plainLoads] at selected
    · rfl
    · exact plainLoads_unchanged _ _
    · exact continuation
end UInt256Proof.Compare.Safety
