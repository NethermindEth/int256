import UInt256.LookupContracts
import UInt256.ExecutionAutomation

open Lean Meta Elab Tactic CIL

namespace UInt256Proof

elab "cil_lookup_call" : tactic => withMainContext do
  let (call, _) ← provedCall `Extracted.broadcastLookupIndex
    `UInt256Proof.SIMD.execute_lookup_at "extracted lookup getter" 0
  let memory ← PrettyPrinter.delab call[7]!
  let frame ← PrettyPrinter.delab call[5]!
  let fuel ← PrettyPrinter.delab call[1]!
  let hr := mkIdent (← mkFreshUserName `lookupRun)
  evalTactic (← `(tactic|
    have $hr:ident := SIMD.execute_lookup_at $memory $frame $fuel
      (by simp [cil_code]; all_goals omega)))
  rewriteHelperRun hr

end UInt256Proof
