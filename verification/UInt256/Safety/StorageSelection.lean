import Extracted
import CIL.Safety.InstructionMemory
import UInt256.Methods.Add.StorageCall
import UInt256.Methods.Add.SSEShapes.ReversedStorage

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

/-- The word order read from a body fetched by a checked index, so evaluating it never scans
    unrelated methods. -/
theorem storageWordOrder_of_found {index : Nat} {body : CIL.Method}
    (selected : storageIndex = index) (found : Extracted.program[index]? = some body) :
    storageWordOrder = body.code.filterMap fun op =>
      match op with | .arg (index + 1) => some index | _ => none := by
  simp only [storageWordOrder, storageBody, selected, found, Option.getD_some]

def storageArguments (output : CIL.Safety.Reference) (w0 w1 w2 w3 : BitVec 64) :
    List CIL.Safety.Value :=
  .reference (.address output) :: (List.range 4).map fun index =>
    .scalar (.i64 ([w0, w1, w2, w3][storageWordOrder.findIdx (· == index)]?.getD 0))

/-- The extracted storage helper is the forward or the reversed limb body checked once by
    `LimbStorage`; the discovered argument order must agree with that body by evaluation. -/
theorem storage_contract : LimbStorageContract Extracted.program storageIndex storageArguments := by
  intro memory inputs output w0 w1 w2 w3 call
  first
  | have found : Extracted.program[storageIndex]? =
        some (UInt256Proof.Multiply.LimbStorage.body Extracted.profile) := by rfl
    have ordered : storageArguments output w0 w1 w2 w3 =
        UInt256Proof.Multiply.LimbStorage.arguments output w0 w1 w2 w3 := by rfl
    rw [ordered]
    exact UInt256Proof.Multiply.LimbStorage.store_limbs_readable_contract Extracted.profile _ _ found
      memory inputs output w0 w1 w2 w3 call
  | have found : Extracted.program[storageIndex]? =
        some (UInt256Proof.Add.SSEShapes.ReversedStorage.body Extracted.profile) := by rfl
    have ordered : storageArguments output w0 w1 w2 w3 =
        UInt256Proof.Multiply.LimbStorage.arguments output w3 w2 w1 w0 := by rfl
    rw [ordered]
    exact UInt256Proof.Add.SSEShapes.ReversedStorage.store_limbs_readable_contract Extracted.profile _ _ found
      memory inputs output w0 w1 w2 w3 call

#print axioms storage_contract

end UInt256Proof.Safety
