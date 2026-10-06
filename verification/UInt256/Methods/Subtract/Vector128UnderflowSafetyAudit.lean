import UInt256.Methods.Subtract.Vector128UnderflowSafety

theorem UInt256Proof.Subtract.Safety.checked_vector128_underflow_binding :
    UInt256Model.Safety.ReportingBinaryContract (fun left right => left - right)
      (fun left right => decide (left.toNat < right.toNat))
      Extracted.program Extracted.entryIndex := by
  with_reducible exact UInt256Proof.Subtract.Safety.checked_vector128_underflow_contract

#print axioms UInt256Proof.Subtract.Safety.checked_vector128_underflow_binding
