import UInt256.Methods.Add.ARMSmallOutput
import UInt256.Safety.NumericStore

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety

/-- Retain every extracted numeric kind, including the ARM one-byte flag. -/
def armSmallSpecs : List NumericLocalSpec := numericSpecs Extracted.addScalarUInt64Body

theorem arm_small_local_metadata :
    Extracted.addScalarUInt64Body.localKinds = numericKinds armSmallSpecs ∧
    Extracted.addScalarUInt64Body.locals = numericInitializers armSmallSpecs := by
  constructor <;> rfl

theorem arm_small_frame_setup (memory : Memory) (args : List Value) (wf : memory.WellFormed) :
    ∃ frame entered,
      enterFrame Extracted.addScalarUInt64Body args memory = .ok (frame, entered) ∧
      NumericHomes entered memory.nextIdentity armSmallSpecs frame.locals ∧
      MemoryBelow memory.nextIdentity memory entered ∧ entered.WellFormed :=
  numeric_frame_setup Extracted.addScalarUInt64Body armSmallSpecs arm_small_local_metadata.1
    arm_small_local_metadata.2 (by rfl) memory args wf

/-- Original initialized-home evidence justifies later private writes after any
    prior checked writes, with byte width and representability checked explicitly. -/
theorem arm_small_private_store (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame)
    (call : CallingConditions Extracted.program current inputs outputs)
    (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered boundary armSmallSpecs frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (index : Nat) (spec : NumericLocalSpec) (specified : armSmallSpecs[index]? = some spec)
    (value : CIL.Value) (number : Nat) (fits : localNumber spec.kind value = .ok number) :
    ∃ reference after,
      frame.locals[index]? = some (.bytes spec.kind reference) ∧
      read after reference (localWidth spec.kind) 1 = .ok (numberBytes number (localWidth spec.kind)) ∧
      MemoryBelow boundary current after ∧
      CallingConditions Extracted.program after inputs outputs ∧
      AccessBelow entered.nextIdentity entered after ∧
      write current reference (numberBytes number (localWidth spec.kind)) 1 = .ok after ∧
      ∀ pc args rest, step Extracted.addScalarUInt64Body (.setLocal index) pc args frame
        (.scalar value :: rest) current = .ok (.next (pc + 1) rest frame after) :=
  checked_numeric_store Extracted.program Extracted.addScalarUInt64Body armSmallSpecs boundary
    entered current inputs outputs frame call enteredWF homes authority index spec specified value number fits

#print axioms arm_small_local_metadata
#print axioms arm_small_frame_setup
#print axioms arm_small_private_store
end UInt256Proof.Add.Safety
