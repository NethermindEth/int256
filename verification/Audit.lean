import UInt256
import Lean

open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if (name.toString.startsWith "UInt256Model." ||
        name.toString.startsWith "UInt256Proof.") && info.isTheorem then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless axiomName == ``propext || axiomName == ``Quot.sound ||
            axiomName == ``Classical.choice do
          throwError "Unapproved axiom {axiomName} in {name}"
      count := count + 1
  if count == 0 then throwError "No UInt256 theorems audited"
  logInfo m!"Audited {count} UInt256 supporting theorems; no compiled-method certificate."
