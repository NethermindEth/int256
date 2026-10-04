import UInt256.ExecutionAutomation
import UInt256.Methods.Bitwise.Contract
import UInt256.Methods.Bitwise.Lemmas
import UInt256.Methods.Bitwise.Aggregate
open CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Bitwise
theorem not_correct (initial : Bytes) (input out : Nat) :
 UInt256Model.Bitwise.NotContract Extracted.program Extracted.entryIndex initial input out := by
  first
  | (solve |
    have vectorBody : (Extracted.program.any fun method => method.code.any fun op =>
      match op with | .intrinsic (.vector _) _ => true | _ => false) = true := by decide
    refine ⟨executionBound Extracted.program Extracted.entryIndex, ?_⟩
    simp only [invoke,cil_code,Option.bind_eq_bind,Option.bind_some]
    cil_execute_core read256_initial,intrinsic_not256,evalMemory,write256,unsafeAdd with fail
    all_goals first | (solve | rfl) | (solve | refine ⟨_,rfl,?_⟩; intro address; rfl))
  | (
    obtain ⟨ha0,ha1,ha2,ha3⟩ := limb_reads (byteMemory initial) input (inputLimbs initial input) (read64_initial initial input)
    refine ⟨executionBound Extracted.program Extracted.entryIndex, ?_⟩
    simp only [invoke, cil_code, Option.bind_eq_bind, Option.bind_some]
    rw [←input_value initial input, ←value_not]
    cil_execute_core ha0,ha1,ha2,ha3,aggregate_fourWrites,evalMemory,write256,unsafeAdd with fail
    try (simp only [word_not_number, aggregate_fourWrites, Option.bind_some])
    cil_execute_core evalMemory,write256,unsafeAdd with fail
    all_goals intro address
    all_goals apply writeBytes_equal
    all_goals try rfl
    all_goals try (solve | intro location; simp only [writeAggregate,writeHomeBytes_caller,clearHome_caller])
    all_goals intro location
  )
end UInt256Proof.Bitwise
