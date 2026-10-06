import UInt256.Methods.Add.ARMContract

/-- Bind the public ARM Add safety proof to the existing exact wrapping contract. -/
theorem UInt256Proof.Add.Safety.checked_arm_add_binding :
    UInt256Model.Safety.WrappingBinaryContract (fun left right => left + right)
      Extracted.program Extracted.entryIndex :=
  UInt256Proof.Add.Safety.checked_arm_add_contract (by rfl)

#print axioms UInt256Proof.Add.Safety.checked_arm_add_binding
