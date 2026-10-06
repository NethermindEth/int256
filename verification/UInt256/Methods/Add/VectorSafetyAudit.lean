import UInt256.Methods.Add.VectorParentContract

/-- Bind the full safety and arithmetic contract to the actual public entry. -/
theorem UInt256Proof.Add.Safety.checked_vector_add_binding :
    UInt256Model.Safety.WrappingBinaryContract (fun left right => left + right)
      Extracted.program Extracted.entryIndex :=
  UInt256Proof.Add.Safety.checked_vector_parent_contract

#print axioms UInt256Proof.Add.Safety.checked_vector_add_binding
