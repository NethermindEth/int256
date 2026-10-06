import UInt256.Methods.Compare.WrapperSafety
import CIL.Safety.NegationReturn

namespace UInt256Proof.Compare.Safety
open CIL.Safety UInt256Model.Safety

theorem wrapper_compose (wrapper : Wrapper)
    (operation childOperation : BitVec 256 → BitVec 256 → CIL.Value)
    (child : ∀ memory left right, CallingConditions Extracted.program memory [left, right] [] →
      ∃ fuel final,
        InvocationCertificate Extracted.program (wrapperChild wrapper)
          (childArguments wrapper left right) memory fuel final
          [.scalar (childOperation (inputValue memory left) (inputValue memory right))] ∧
        ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset)
    (suffix : ∀ memory left right frame x y,
      ∃ fuel, run Extracted.program fuel (wrapperIndex wrapper) (wrapperCall wrapper + 1)
        (readOnlyArguments [left, right]) frame [.scalar (childOperation x y)] memory =
          .ok (leaveFrame frame memory, [.scalar (operation x y)])) :
    BinaryReadOnlyInvocation operation Extracted.program (wrapperIndex wrapper) := by
  apply compose_readOnly_binary Extracted.program (wrapperIndex wrapper) (wrapperCall wrapper)
    (wrapperChild wrapper) (wrapperBody wrapper) operation childOperation (childArguments wrapper)
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
  · exact child
  · exact suffix
  · intro memory left right frame call post continuation
    exact wrapper_prefix wrapper left right frame memory call post continuation

def strictFlag (left right : BitVec 256) : BitVec 32 :=
  if left.toNat < right.toNat then 1 else 0

theorem inclusive_inner_checked (leaf : BinaryReadOnlyInvocation (fun x y => .i32 (strictFlag x y)) Extracted.program wrapperLeafIndex) : BinaryReadOnlyInvocation (fun x y => .i32 (strictFlag x y))
    Extracted.program (wrapperIndex .less) := by
  apply wrapper_compose .less (fun x y => .i32 (strictFlag x y)) (fun x y => .i32 (strictFlag x y))
  · exact leaf
  · intro memory left right frame x y
    refine ⟨1, ?_⟩
    have lookup : Extracted.program[wrapperIndex .less]? = some (wrapperBody .less) := by rfl
    have returned : (wrapperBody .less).code[wrapperCall .less + 1]? = some .ret := by rfl
    have returns : (wrapperBody .less).returnsValue = true := by rfl
    simp [run, lookup, returned, returns, step, checkedValue, numericValue,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

def middleFlag (left right : BitVec 256) : BitVec 32 :=
  if middleSwaps then strictFlag right left else strictFlag left right

def inclusiveValue (left right : BitVec 256) : CIL.Value :=
  .i32 (if middleFlag left right = 0 then 1 else 0)

theorem inclusive_middle_checked (leaf : BinaryReadOnlyInvocation (fun x y => .i32 (strictFlag x y)) Extracted.program wrapperLeafIndex) : BinaryReadOnlyInvocation inclusiveValue
    Extracted.program (wrapperIndex .greater) := by
  apply wrapper_compose .greater inclusiveValue (fun x y => .i32 (middleFlag x y))
  · intro memory left right call
    by_cases swapped : middleSwaps = true
    · simpa [childArguments, middleFlag, swapped, wrapperIndex, wrapperChild] using
        inclusive_inner_checked leaf memory right left call.swap_binary_inputs
    · simpa [childArguments, middleFlag, swapped, wrapperIndex, wrapperChild] using
        inclusive_inner_checked leaf memory left right call
  · intro memory left right frame x y
    exact ⟨3, run_negation_return Extracted.program (wrapperIndex .greater)
      (wrapperCall .greater + 1) (wrapperBody .greater)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) _ frame memory (middleFlag x y)⟩

theorem inclusive_entry_checked (leaf : BinaryReadOnlyInvocation (fun x y => .i32 (strictFlag x y)) Extracted.program wrapperLeafIndex) : BinaryReadOnlyInvocation (fun x y => inclusiveValue y x)
    Extracted.program (wrapperIndex .entry) := by
  apply wrapper_compose .entry (fun x y => inclusiveValue y x) (fun x y => inclusiveValue y x)
  · intro memory left right call
    exact inclusive_middle_checked leaf memory right left call.swap_binary_inputs
  · intro memory left right frame x y
    refine ⟨1, ?_⟩
    have lookup : Extracted.program[wrapperIndex .entry]? = some (wrapperBody .entry) := by rfl
    have returned : (wrapperBody .entry).code[wrapperCall .entry + 1]? = some .ret := by rfl
    have returns : (wrapperBody .entry).returnsValue = true := by rfl
    simp [run, lookup, returned, returns, step, inclusiveValue, checkedValue, numericValue,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms inclusive_entry_checked
end UInt256Proof.Compare.Safety
