import UInt256.Methods.Subtract.Bindings
import UInt256.Safety.ReportingForwarder

/-! The extracted public Subtract entry forwards its three references to SubtractImpl and
    discards the returned flag. -/

namespace UInt256Proof.Subtract.Safety
open UInt256Model.Safety

/-- Public Subtract keeps the forwarded wrapping difference and caller footprint. -/
theorem wrapping_contract_of_reporting
    (reporting : ReportingBinaryContract (· - ·)
      (fun a b => decide (a.toNat < b.toNat)) Extracted.program Extracted.subtractVector256Index) :
    WrappingBinaryContract (· - ·) Extracted.program Extracted.entryIndex :=
  forward_reporting_pop Extracted.program Extracted.entryIndex Extracted.subtractVector256Index
    Extracted.entryBody _ _ rfl rfl rfl rfl rfl rfl rfl reporting

end UInt256Proof.Subtract.Safety
