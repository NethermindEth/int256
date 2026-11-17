import UInt256.Methods.Add.ARMSmallPrefix
import CIL.Safety.LocalSnapshots

/-! Numeric homes of the small-addition frame and the limbs its output holds. -/

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- Actual initialized homes, including the one-byte ARM flag. -/
def armSmallSpecs : List NumericLocalSpec :=
  List.replicate 6 armWordSpec ++ [⟨.narrow .unsigned8, .i32 0, 0, rfl⟩]

/-- Entry allocates numeric homes without changing caller memory. -/
theorem arm_small_frame_setup (profile : CIL.FeatureProfile) (storage : Nat)
    (memory : Memory) (args : List Value) (wf : memory.WellFormed) :
    ∃ frame entered,
      enterFrame (armSmallBody profile storage) args memory = .ok (frame, entered) ∧
      NumericHomes entered memory.nextIdentity armSmallSpecs frame.locals ∧
      MemoryBelow memory.nextIdentity memory entered ∧ entered.WellFormed :=
  numeric_frame_setup (armSmallBody profile storage) armSmallSpecs
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) memory args wf

/-- The output replaces the saved low input with its computed sum. -/
def armSmallOutputWords (words : Fin 4 → BitVec 64) (sum : BitVec 64) : Fin 4 → BitVec 64 :=
  fun index => if index.val = 0 then sum else words index

end UInt256Proof.Add.Safety
