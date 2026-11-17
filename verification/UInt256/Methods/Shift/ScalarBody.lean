import UInt256.Generated.MethodTemplates
import UInt256.Methods.Shift.Contract
import CIL.Safety.NumericHomes

namespace UInt256Proof.Shift.Safety
open CIL.Safety

/-- Exact common count/read prefix; direction-dependent arithmetic follows only after all reads. -/
def scalarBody (profile : CIL.FeatureProfile) (direction : Direction) (storage : Nat) : CIL.Method :=
  let left := UInt256Proof.Generated.Method.method15 profile storage
  let right := UInt256Proof.Generated.Method.method23 profile storage
  { left with code := (by_elab
      let code ← Lean.Elab.Term.elabTermAndSynthesize
        (← `($(Lean.mkIdent `left).code.take 39)) none
      return ← Lean.Meta.withTransparency .default (Lean.Meta.reduce code)) ++ match direction with
    | .left => by_elab
      let code ← Lean.Elab.Term.elabTermAndSynthesize
        (← `($(Lean.mkIdent `left).code.drop 39)) none
      return ← Lean.Meta.withTransparency .default (Lean.Meta.reduce code)
    | .right => by_elab
      let code ← Lean.Elab.Term.elabTermAndSynthesize
        (← `($(Lean.mkIdent `right).code.drop 39)) none
      return ← Lean.Meta.withTransparency .default (Lean.Meta.reduce code) }


def shiftSpecs : List NumericLocalSpec :=
  [⟨.word32, .i32 0, 0, rfl⟩, ⟨.word32, .i32 0, 0, rfl⟩, ⟨.word32, .i32 0, 0, rfl⟩,
   ⟨.word64, .i64 0, 0, rfl⟩, ⟨.word64, .i64 0, 0, rfl⟩,
   ⟨.word64, .i64 0, 0, rfl⟩, ⟨.word64, .i64 0, 0, rfl⟩]

theorem scalar_frame_setup (profile : CIL.FeatureProfile) (direction : Direction) (storage : Nat)
    (memory : Memory) (args : List Value) (wellFormed : memory.WellFormed) :
    ∃ frame result,
      enterFrame (scalarBody profile direction storage) args memory = .ok (frame, result) ∧
      NumericHomes result memory.nextIdentity shiftSpecs frame.locals ∧
      MemoryBelow memory.nextIdentity memory result ∧ result.WellFormed :=
  numeric_frame_setup _ shiftSpecs rfl rfl rfl rfl rfl memory args wellFormed

end UInt256Proof.Shift.Safety
