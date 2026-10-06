import UInt256.Methods.Compare.WrapperSafety

namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety

def lessValue (left right : BitVec 256) : CIL.Value :=
  .i32 (if left.toNat < right.toNat then 1 else 0)

theorem wrapper_checked (wrapper : Wrapper)
    (operation : BitVec 256 → BitVec 256 → CIL.Value)
    (numeric : ∀ left right, numericValue (operation left right) = true)
    (child : ∀ memory left right, CallingConditions Extracted.program memory [left, right] [] →
      ∃ fuel final,
        InvocationCertificate Extracted.program (wrapperChild wrapper)
          (childArguments wrapper left right) memory fuel final
          [.scalar (operation (inputValue memory left) (inputValue memory right))] ∧
        ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset) :
    BinaryReadOnlyInvocation operation Extracted.program (wrapperIndex wrapper) := by
  apply forward_readOnly_binary Extracted.program (wrapperIndex wrapper) (wrapperCall wrapper)
    (wrapperChild wrapper) (wrapperBody wrapper) operation (childArguments wrapper)
  · cases wrapper <;> rfl
  · cases wrapper <;> rfl
  · cases wrapper <;> rfl
  · cases wrapper <;> rfl
  · intro left right
    cases wrapper
    all_goals
      conv in (wrapperBody _) => cbv
      simp [FrameSetupFits, InitializersFit, InitializerFits, AggregateArgumentsFit]
  · intro left right
    cases wrapper <;> simp only [childArguments]
    all_goals first | rfl | (split <;> rfl)
  · exact numeric
  · exact child
  · intro memory left right frame call post continuation
    exact wrapper_prefix wrapper left right frame memory call post continuation

theorem less_checked (leaf : BinaryReadOnlyInvocation lessValue Extracted.program wrapperLeafIndex) : BinaryReadOnlyInvocation lessValue Extracted.program (wrapperIndex .less) := by
  apply wrapper_checked .less lessValue (by intros; rfl)
  exact leaf

def middleValue (left right : BitVec 256) : CIL.Value :=
  if middleSwaps then lessValue right left else lessValue left right

theorem greater_checked (leaf : BinaryReadOnlyInvocation lessValue Extracted.program wrapperLeafIndex) : BinaryReadOnlyInvocation middleValue
    Extracted.program (wrapperIndex .greater) := by
  apply wrapper_checked .greater middleValue (by intros; unfold middleValue; split <;> rfl)
  intro memory left right call
  by_cases swapped : middleSwaps = true
  · simpa [childArguments, middleValue, swapped, wrapperIndex, wrapperChild] using
      less_checked leaf memory right left call.swap_binary_inputs
  · simpa [childArguments, middleValue, swapped, wrapperIndex, wrapperChild] using
      less_checked leaf memory left right call

theorem entry_checked (leaf : BinaryReadOnlyInvocation lessValue Extracted.program wrapperLeafIndex) : BinaryReadOnlyInvocation (fun left right => middleValue right left) Extracted.program (wrapperIndex .entry) := by
  apply wrapper_checked .entry (fun left right => middleValue right left) (by intros; unfold middleValue; split <;> rfl)
  intro memory left right call
  exact greater_checked leaf memory right left call.swap_binary_inputs

#print axioms less_checked
#print axioms greater_checked
#print axioms entry_checked
end UInt256Proof.Compare.Safety
