import UInt256.Methods.Add.ARMOverflowSafety

theorem UInt256Proof.Add.Safety.checked_arm_overflow_binding :
    UInt256Model.Safety.ReportingBinaryContract (fun left right => left + right)
      (fun left right => decide (2^256 ≤ left.toNat + right.toNat))
      Extracted.program Extracted.entryIndex :=
  UInt256Proof.Add.Safety.checked_arm_overflow_contract

#print axioms UInt256Proof.Add.Safety.checked_arm_overflow_binding
