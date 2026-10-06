import UInt256.Methods.Add.SSEContract

/-- Exact public binding for the extracted SSE Add program. -/
theorem UInt256Proof.Add.Safety.checked_sse_add_binding :
    UInt256Model.Safety.WrappingBinaryContract (fun left right => left + right)
      Extracted.program Extracted.entryIndex :=
  UInt256Proof.Add.Safety.checked_sse_add_contract

#print axioms UInt256Proof.Add.Safety.checked_sse_add_binding
