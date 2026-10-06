import UInt256.Methods.Add.EntrySafety

-- Bind the exact public contract independently of inferred theorem types.
theorem UInt256Proof.Safety.checked_add_binding :
    UInt256Model.Safety.WrappingBinaryContract (fun left right => left + right)
    Extracted.program Extracted.entryIndex := UInt256Proof.Safety.checked_add_contract

#print axioms UInt256Proof.Safety.checked_add_binding
