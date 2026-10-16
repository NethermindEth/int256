import UInt256.Methods.Bindings

namespace UInt256Proof.Compare.PrimitiveSafety

def leafIndex : Nat := Extracted.program.findIdx fun body =>
  body.code.any fun op => match op with | .fieldAt _ _ => true | _ => false

def leafBody : CIL.Method := Extracted.program[leafIndex]?.getD
  { code := [], locals := [], returnsValue := false }

def leafSigned : Bool := leafBody.code.any fun op => match op with | .blt _ => true | _ => false

def leafScalarFirst : Bool :=
  let field := leafBody.code.findIdx fun op => match op with | .fieldAt _ _ => true | _ => false
  match leafBody.code[field - 1]? with | some (.arg 1) => true | _ => false

def wrapperCall : Nat := Extracted.entryBody.code.findIdx fun op =>
  match op with | .call _ _ => true | _ => false

def wrapperNegate : Bool := Extracted.entryBody.code.any fun op =>
  match op with | .eq => true | _ => false

def wrapperReversed : Bool := match (Extracted.entryBody.code[0]? : Option CIL.Op) with
  | some (.arg 1) => true | _ => false

def wrapperScalarFirst : Bool := leafScalarFirst != wrapperReversed

end UInt256Proof.Compare.PrimitiveSafety
