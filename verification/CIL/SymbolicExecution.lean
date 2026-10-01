import Lean
import CIL.ExecutionLemmas

-- Only definitions emitted from the current extracted assembly belong here.
-- Registering a definition supplies its kernel-checked unfolding equations;
-- it does not assign a behavioral contract to the method.
register_simp_attr cil_code

namespace CIL

-- Complete Std's numeral projection rules (which cover zero, one and two).
theorem fin_val_three (n : Nat) : (3 : Fin (n + 4)).val = 3 := rfl

-- A conservative candidate budget for the selected method and later callees.
-- Sufficiency is established by each execution proof, not assumed here.
def executionBound (program : Program) (method : Nat) : Nat :=
  (program.drop method).foldl (fun total body => total +
    (body.code.filter fun op => match op with | .unsupported _ => false | _ => true).length) 0 + 1

-- Summary candidates are transactions: failed elaboration, kernel checking,
-- or admitted proofs leave neither declarations nor simp registrations behind.
-- Subsequent execution then uses instructions directly.
open Lean Elab Command in
elab "if_extracted " name:ident " {" commands:command* "}" : command => do
  unless (← getEnv).contains name.getId do return
  let saved ← get
  try
    for command in commands do
      elabCommand (← `(command| set_option Elab.async false in $command))
    if (← get).messages.hasErrors then
      throwError "Summary proof failed"
    let env ← getEnv
    for (declName, info) in env.constants.toList do
      if saved.env.contains declName then continue
      if info.isAxiom || (info.value? true).any Expr.hasSorry then
        throwError "Summary contains an admitted declaration"
      if (env.checked.get.find? declName).isNone then
        throwError "Summary declaration was not kernel checked"
  catch _ =>
    set saved
    logInfo m!"Optional summary candidate {name.getId} was not proved; using raw execution"

-- Execute instructions until execution finishes or a symbolic obligation
-- prevents further reduction. Facts are ordinary proved hypotheses/lemmas.
-- There is no instruction trace, method identity, or local layout in this
-- procedure. Lean's heartbeat/depth limits remain explicit failure limits.
macro "cil_steps" facts:term,+ : tactic =>
  `(tactic| ((try (simp only [cil_code])); repeat
    (rw [run];
     -- Resolve the method and instruction before unfolding the selected step.
     -- Otherwise simp explores instruction cases under unresolved bind lambdas.
     simp only [cil_code, Option.pure_def, Option.bind_eq_bind, Option.bind_some];
     -- Retain checked rewrite proofs instead of making the kernel repeat large
     -- definitional reductions when checking the resulting execution proof.
     simp (config := { implicitDefEqProofs := false })
      [cil_code, step, binary, truth, write64, initLocals,
      fin_val_three, $[$facts:term],*])))

macro "cil_steps" : tactic => `(tactic| cil_steps Nat.add_zero)

end CIL
