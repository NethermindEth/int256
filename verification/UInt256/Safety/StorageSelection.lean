import Extracted
import CIL.Safety.InstructionMemory

namespace UInt256Proof.Safety

/-- Locate a leaf four-limb writer independently of operation-specific aliases.
    This only selects proof data: the storage proof checks every executed
    instruction, the frame metadata, and the complete output contract. -/
def storageIndex : Nat := Extracted.program.findIdx fun body =>
  body.locals.isEmpty &&
    (body.code.any (fun op => match op with | .memory .store256 => true | _ => false) ||
      match body.code with | .arg 0 :: .skipInit :: _ => true | _ => false)

def storageBody : CIL.Method := Extracted.program[storageIndex]?.getD
  { code := [], locals := [], returnsValue := false }

/-- Candidate argument permutation discovered from the leaf's value loads.
    This is only proof setup; each storage theorem still executes the extracted
    body and establishes the complete memory postcondition. -/
def storageWordOrder : List Nat := storageBody.code.filterMap fun op =>
  match op with | .arg (index + 1) => some index | _ => none

def storageArguments (output : CIL.Safety.Reference) (w0 w1 w2 w3 : BitVec 64) :
    List CIL.Safety.Value :=
  .reference (.address output) :: (List.range 4).map fun index =>
    .scalar (.i64 ([w0, w1, w2, w3][storageWordOrder.findIdx (· == index)]?.getD 0))

end UInt256Proof.Safety
