import Extracted
import CIL.Safety.WordFrameSetup

namespace UInt256Proof.Subtract.Safety
open CIL.Safety

def scalarIndex : Nat := Extracted.program.findIdx fun body =>
  body.code.any fun op => match op with
    | .call callee _ => callee == Extracted.subtractScalarUInt64Index | _ => false

def scalarBody : CIL.Method := Extracted.program[scalarIndex]?.getD
  { code := [], locals := [], returnsValue := false }

def scalarLocalSpecs : List (Option (BitVec 64)) :=
  scalarBody.locals.map fun value => match value with
    | .i64 word => some word | _ => none

theorem scalar_local_metadata :
    scalarBody.localKinds = wordKinds scalarLocalSpecs ∧
    scalarBody.locals = wordInitializers scalarLocalSpecs := by constructor <;> rfl

theorem scalar_frame_setup (memory : Memory) (args : List Value) (wellFormed : memory.WellFormed) :
    ∃ frame result,
      enterFrame scalarBody args memory = .ok (frame, result) ∧
      WordHomes result memory.nextIdentity scalarLocalSpecs frame.locals ∧
      MemoryBelow memory.nextIdentity memory result ∧ result.WellFormed :=
  word_frame_setup scalarBody scalarLocalSpecs scalar_local_metadata.1
    scalar_local_metadata.2 (by rfl) memory args wellFormed

#print axioms scalar_local_metadata
#print axioms scalar_frame_setup
end UInt256Proof.Subtract.Safety
