import UInt256.Methods.Compare.PrimitiveLeaf
import UInt256.Methods.Bindings
import UInt256.Safety.ScalarOperatorContract
import UInt256.Safety.LimbAccess
import CIL.Safety.StepComposition
import CIL.Safety.ReturnMemory

namespace UInt256Proof.Compare.PrimitiveSafety
open CIL.Safety UInt256Model.Safety

def leafIndex : Nat := Extracted.program.findIdx fun body =>
  body.code.any fun op => match op with | .fieldAt _ _ => true | _ => false

def leafBody : CIL.Method := Extracted.program[leafIndex]?.getD
  { code := [], locals := [], returnsValue := false }

def leafSigned : Bool := leafBody.code.any fun op => match op with | .blt _ => true | _ => false

def leafScalarFirst : Bool :=
  let field := leafBody.code.findIdx fun op => match op with | .fieldAt _ _ => true | _ => false
  match leafBody.code[field - 1]? with | some (.arg 1) => true | _ => false

def leafResult (memory : Memory) (input : Reference) (word : BitVec 64) : BitVec 32 :=
  if leafSigned && decide (word.toInt < 0) then if leafScalarFirst then 1 else 0
  else if inputLimb memory input 1 = 0 ∧ inputLimb memory input 2 = 0 ∧ inputLimb memory input 3 = 0 then
    if (if leafScalarFirst then word.toNat < (inputLimb memory input 0).toNat
        else (inputLimb memory input 0).toNat < word.toNat) then 1 else 0
  else if leafScalarFirst then 1 else 0

theorem leaf_run (memory : Memory) (input : Reference) (word : BitVec 64) (frame : Frame)
    (call : CallingConditions Extracted.program memory [input] []) :
    run Extracted.program 22 leafIndex 0
      (scalarOperatorArguments leafScalarFirst input (.i64 word)) frame [] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 (leafResult memory input word))]) :=
  PrimitiveLeaf.run_template leafSigned leafScalarFirst Extracted.program leafIndex
    (by rfl) memory input word frame call

#print axioms leaf_run
end UInt256Proof.Compare.PrimitiveSafety
