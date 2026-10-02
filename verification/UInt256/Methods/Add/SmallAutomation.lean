import UInt256.Methods.Add.Automation
import UInt256.Methods.Add.Small

open Lean Meta Elab Tactic CIL UInt256Model

namespace UInt256Proof

elab "cil_small_call" : tactic => withMainContext do
  smallHelperCall `Extracted.addScalarUInt64Index `UInt256Proof.execute_small_words_at "small-add"

end UInt256Proof
