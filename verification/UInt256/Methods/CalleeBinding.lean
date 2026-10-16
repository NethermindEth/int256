import Lean
import CIL.Instructions
import CIL.SymbolicExecution

namespace UInt256Proof

open Lean Meta in
/-- First call with `arity` arguments as (callee, pc), found by walking the code list one
    cell at a time, so the cost is linear in the parent body and never normalizes it. -/
def calleeWithArity (code : Expr) (arity : Nat) : MetaM (Option (Nat × Nat)) := do
  let mut current := code
  let mut pc := 0
  repeat
    let cell ← whnf current
    match cell.getAppFnArgs with
    | (``List.cons, #[_, op, tail]) =>
      let op ← whnf op
      if let (``CIL.Op.call, #[callee, count]) := op.getAppFnArgs then
        if (← (evalNat count).run) == some arity then
          if let some callee ← (evalNat callee).run then
            return some (callee, pc)
      current := tail
      pc := pc + 1
    | _ => return none
  return none

open Lean Elab Command Meta in
/-- Name the extracted method that `parent` calls with `arity` arguments, so inserted
    helpers do not shift bindings. Proofs still execute every fetched instruction. -/
elab "bind_callee " index:ident body:ident " := " parent:term " with " arity:num : command => do
  let found ← liftTermElabM do
    let e ← instantiateMVars (← Term.elabTermEnsuringType parent (some (mkConst ``CIL.Method)))
    calleeWithArity (mkApp (mkConst ``CIL.Method.code) e) arity.getNat
  let some (n, _) := found | throwError "no callee with arity {arity.getNat}"
  let method := mkIdent (Name.mkSimple s!"method{n}")
  elabCommand (← `(@[cil_code] def $index : Nat := $(quote n)))
  elabCommand (← `(abbrev $body := $method))

open Lean Elab Command Meta in
/-- Name the pc of the first call in `parent` with `arity` arguments; proofs still fetch
    and check the instruction there. -/
elab "bind_call_site " site:ident " := " parent:term " with " arity:num : command => do
  let found ← liftTermElabM do
    let e ← instantiateMVars (← Term.elabTermEnsuringType parent (some (mkConst ``CIL.Method)))
    calleeWithArity (mkApp (mkConst ``CIL.Method.code) e) arity.getNat
  let some (_, pc) := found | throwError "no call with arity {arity.getNat}"
  elabCommand (← `(@[cil_code] def $site : Nat := $(quote pc)))

end UInt256Proof
