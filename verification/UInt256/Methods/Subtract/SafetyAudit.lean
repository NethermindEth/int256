import UInt256.Methods.Subtract.WrappingSafety
import UInt256.Methods.Subtract.BorrowCaller

theorem UInt256Proof.Subtract.Safety.checked_wrapping_binding :
    UInt256Model.Safety.WrappingBinaryContract (fun left right => left - right)
      Extracted.program Extracted.entryIndex := by
  with_reducible exact
    (UInt256Proof.Subtract.Safety.checked_wrapping_contract UInt256Proof.Subtract.Safety.borrow_checked_contract)

#print axioms UInt256Proof.Subtract.Safety.checked_wrapping_binding
