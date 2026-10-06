import UInt256.Methods.Compare.NativeEntrySafety

namespace UInt256Proof.Compare.Safety
open UInt256Model.Safety

/-- Bind the discovered comparison chain to the extracted public entry and the
independent unsigned ordering of its two initial inputs. -/
theorem checked_less_equal_contract :
    ReadOnlyContract
      (fun values => .i32 (if (values[0]?.getD 0).toNat ≤ (values[1]?.getD 0).toNat then 1 else 0))
      Extracted.program Extracted.entryIndex 2 := by
  have entry : BinaryReadOnlyInvocation (fun left right => .i32 (if left.toNat ≤ right.toNat then 1 else 0)) Extracted.program Extracted.entryIndex :=
    native_entry_checked
  intro memory inputs arity call
  cases inputs with
  | nil => simp at arity
  | cons left rest =>
    cases rest with
    | nil => simp at arity
    | cons right tail =>
      cases tail with
      | cons _ _ => simp at arity
      | nil =>
        simpa only [List.map_cons, List.map_nil, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some] using entry memory left right call

theorem checked_less_equal_binding :
    ReadOnlyContract
      (fun values => .i32 (if (values[0]?.getD 0).toNat ≤ (values[1]?.getD 0).toNat then 1 else 0))
      Extracted.program Extracted.entryIndex 2 := checked_less_equal_contract

#print axioms checked_less_equal_contract
#print axioms checked_less_equal_binding
end UInt256Proof.Compare.Safety
