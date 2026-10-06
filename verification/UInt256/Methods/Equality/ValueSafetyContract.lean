import UInt256.Methods.Equality.ValueSafetyExecution

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

theorem value_entry_checked (child : EqualityInvocation (wrapperIndex false))
    (memory : Memory) (left : Reference) (right : BitVec 256)
    (call : CallingConditions Extracted.program memory [left] []) :
    ∃ fuel final,
      InvocationCertificate Extracted.program Extracted.entryIndex (valueArguments left right) memory fuel final
        [.scalar (.i32 (if inputValue memory left = right then 1 else 0))] ∧
      ∀ id, id < memory.nextIdentity → ∀ offset, final.cells id offset = memory.cells id offset :=
  UInt256Proof.ValueSafety.value_entry_checked (wrapperIndex false)
    (fun x y => if x = y then 1 else 0) (by rfl) child memory left right call

#print axioms value_entry_checked
end UInt256Proof.Equality.Safety
