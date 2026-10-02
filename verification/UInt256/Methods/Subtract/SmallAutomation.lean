import UInt256.Methods.Subtract.Small

open Lean Meta Elab Tactic CIL UInt256Model

namespace UInt256Proof

elab "cil_subtract_small_call" : tactic => withMainContext do
  smallHelperCall `Extracted.subtractScalarUInt64Index `UInt256Proof.execute_subtract_small_at "small-subtraction"

end UInt256Proof
