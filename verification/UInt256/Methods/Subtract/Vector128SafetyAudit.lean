import UInt256.Methods.Subtract.Vector128WrappingSafety

theorem UInt256Proof.Subtract.Safety.checked_vector128_wrapping_binding :
    UInt256Model.Safety.WrappingBinaryContract (fun left right => left - right)
      Extracted.program Extracted.entryIndex := by
  with_reducible exact UInt256Proof.Subtract.Safety.checked_vector128_wrapping_contract

#print axioms UInt256Proof.Subtract.Safety.checked_vector128_wrapping_binding
