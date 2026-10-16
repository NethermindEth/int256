import Lean
import CIL.Instructions
import CIL.SymbolicExecution

namespace UInt256Proof

/-- First callee invoked with `arity` arguments. This only selects proof data. -/
def calleeWithArity (body : CIL.Method) (arity : Nat) : Option Nat :=
  body.code.findSome? fun op => match op with
    | .call callee count => if count = arity then some callee else none
    | _ => none

open Lean Elab Command Meta in
/-- Name the extracted method that `parent` calls with `arity` arguments, so inserted
    helpers do not shift bindings. Proofs still execute every fetched instruction. -/
elab "bind_callee " index:ident body:ident " := " parent:term " with " arity:num : command => do
  let found ← liftTermElabM do
    let term ← `(UInt256Proof.calleeWithArity $parent $arity)
    let e ← instantiateMVars (← Term.elabTermEnsuringType term (some (mkApp (mkConst ``Option [0]) (mkConst ``Nat))))
    let reduced ← withTransparency .all <| reduce e
    match reduced.getAppFnArgs with
    | (``Option.some, #[_, n]) => (evalNat n).run
    | _ => pure none
  let some n := found | throwError "no callee with arity {arity.getNat}"
  let method := mkIdent (Name.mkSimple s!"method{n}")
  elabCommand (← `(@[cil_code] def $index : Nat := $(quote n)))
  elabCommand (← `(abbrev $body := $method))

end UInt256Proof
