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

-- Optional summaries are elaborated only when the corresponding candidate
-- exists. Skipping one does not establish its behavior; callers use raw steps.
open Lean Elab Command in
elab "if_extracted " name:ident " {" commands:command* "}" : command => do
  if (← getEnv).contains name.getId then
    for command in commands do elabCommand command

-- Execute instructions until execution finishes or a symbolic obligation
-- prevents further reduction. Facts are ordinary proved hypotheses/lemmas.
-- There is no instruction trace, method identity, or local layout in this
-- procedure. Lean's heartbeat/depth limits remain explicit failure limits.
macro "cil_steps" facts:term,+ : tactic =>
  `(tactic| ((try (simp only [cil_code])); repeat
    (rw [run]; simp [cil_code, step, binary, truth, write64, initLocals,
      fin_val_three, $[$facts:term],*])))

macro "cil_steps" : tactic => `(tactic| cil_steps Nat.add_zero)

end CIL
