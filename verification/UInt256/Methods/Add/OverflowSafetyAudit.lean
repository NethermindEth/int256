import UInt256.Methods.Add.OverflowSafety

theorem UInt256Proof.Safety.checked_overflow_binding :
    UInt256Model.Safety.ReportingBinaryContract (fun left right => left + right)
      (fun left right => decide (2^256 ≤ left.toNat + right.toNat))
      Extracted.program Extracted.entryIndex := by
  with_reducible exact UInt256Proof.Safety.checked_overflow_contract

#print axioms UInt256Proof.Safety.checked_overflow_binding
