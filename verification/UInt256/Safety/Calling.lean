import CIL.Safety.AccessRequirements
import CIL.Safety.StaticReferences
import CIL.Safety.LiveState
import CIL.Safety.FrameProgress
import UInt256.Representation

namespace UInt256Model.Safety

open CIL.Safety

/-- The consumer's four-limb footprint, not the extent of its containing object. -/
def wordView (reference : Reference) : ArgumentView := ⟨reference, 32⟩

/-- API views may overlap arbitrarily. Only inputs require initialized bytes;
    the static-world condition binds readonly data to the selected program. -/
def CallingConditions (program : CIL.Program) (memory : CIL.Safety.Memory)
    (inputs outputs : List Reference) : Prop :=
  ValidCall memory (inputs.map wordView) (outputs.map wordView) ∧
    StaticWorldValid (programStaticDescriptors program) memory

def binaryArguments (left right output : Reference) : List CIL.Safety.Value :=
  [.reference (.address left), .reference (.address right), .reference (.address output)]

/-- Uses the actual shared caller bytes. No operand copies are introduced when
    two input views, or an input and the output, overlap. -/
def inputValue (memory : CIL.Safety.Memory) (reference : Reference) : BitVec 256 :=
  byteValue (fun offset => (memory.cells reference.allocation offset).bits) reference.offset

theorem CallingConditions.of_requirements {program : CIL.Program}
    {memory : CIL.Safety.Memory} {inputs outputs : List Reference}
    (wellFormed : memory.WellFormed)
    (world : StaticWorldValid (programStaticDescriptors program) memory)
    (readable : ∀ reference ∈ inputs, ∃ allocation,
      AccessRequirements memory reference 32 1 false allocation ∧
      ∀ i < 32, (memory.cells reference.allocation (reference.offset + i)).initialized = true)
    (writable : ∀ reference ∈ outputs, ∃ allocation,
      AccessRequirements memory reference 32 1 true allocation) :
    CallingConditions program memory inputs outputs := by
  refine ⟨⟨wellFormed, ?_, ?_⟩, world⟩
  · intro view member
    obtain ⟨reference, inputMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨allocation, ready, initialized⟩ := readable reference inputMember
    exact ⟨_, read_snapshot ready initialized⟩
  · intro view member
    obtain ⟨reference, outputMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨allocation, ready⟩ := writable reference outputMember
    exact ready.access

theorem byteNumber_snapshot (bytes : Bytes) (offset width : Nat) :
    CIL.Safety.byteNumber ((List.range width).map fun i => bytes (offset + i)) =
      UInt256Model.byteNumber bytes offset width := by
  induction width generalizing offset with
  | zero => rfl
  | succ width ih =>
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map,
      CIL.Safety.byteNumber, List.foldr_cons, UInt256Model.byteNumber, Nat.add_zero]
    have shifted : (fun i => bytes (offset + Nat.succ i)) =
        (fun i => bytes (offset + 1 + i)) := by
      funext i
      congr 1
      omega
    change (bytes offset).toNat + 256 * CIL.Safety.byteNumber
      ((List.range width).map fun i => bytes (offset + Nat.succ i)) = _
    rw [shifted, ih]

theorem CallingConditions.input_snapshot {program : CIL.Program}
    {memory : CIL.Safety.Memory} {inputs outputs : List Reference}
    (call : CallingConditions program memory inputs outputs)
    {reference : Reference} (member : reference ∈ inputs) :
    read memory reference 32 1 =
      .ok ((List.range 32).map fun i => (memory.cells reference.allocation (reference.offset + i)).bits) := by
  obtain ⟨bytes, loaded⟩ := call.1.2.1 (wordView reference) (List.mem_map.mpr ⟨reference, member, rfl⟩)
  have same := read_result_snapshot loaded
  rw [same] at loaded
  exact loaded

theorem CallingConditions.input_load {program : CIL.Program}
    {memory : CIL.Safety.Memory} {inputs outputs : List Reference}
    (call : CallingConditions program memory inputs outputs)
    {reference : Reference} (member : reference ∈ inputs) :
    loadValue memory (.address reference) 32 = .ok (.v256 (inputValue memory reference)) := by
  have loaded := call.input_snapshot member
  simp only [loadValue, dereference, loaded, checkedAt, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [byteNumber_snapshot (fun offset => (memory.cells reference.allocation offset).bits) reference.offset 32]
  rfl

theorem CallingConditions.input_formed {program : CIL.Program}
    {memory : CIL.Safety.Memory} {inputs outputs : List Reference}
    (call : CallingConditions program memory inputs outputs)
    {reference : Reference} (member : reference ∈ inputs) : form memory reference = .ok reference :=
  read_reference_valid _ _ _ _ _ (call.input_snapshot member)

theorem CallingConditions.output_formed {program : CIL.Program}
    {memory : CIL.Safety.Memory} {inputs outputs : List Reference}
    (call : CallingConditions program memory inputs outputs)
    {reference : Reference} (member : reference ∈ outputs) : form memory reference = .ok reference :=
  access_reference_valid _ _ _ _ _
    (call.1.2.2 (wordView reference) (List.mem_map.mpr ⟨reference, member, rfl⟩))

theorem CallingConditions.binary_arguments_valid {program : CIL.Program}
    {memory : CIL.Safety.Memory} {left right output : Reference}
    (call : CallingConditions program memory [left, right] [output]) :
    ValuesValid memory (binaryArguments left right output) := by
  intro value member
  simp only [binaryArguments, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact call.input_formed (by simp)
  · exact call.input_formed (by simp)
  · exact call.output_formed (by simp)

theorem CallingConditions.binary_entry_live {program : CIL.Program}
    {memory entered : CIL.Safety.Memory} {left right output : Reference}
    {body : CIL.Method} {frame : Frame}
    (call : CallingConditions program memory [left, right] [output])
    (setup : enterFrame body (binaryArguments left right output) memory = .ok (frame, entered)) :
    LiveState program (binaryArguments left right output) frame [] entered :=
  enterFrame_live_state _ _ _ _ _ _ call.1.1 call.binary_arguments_valid call.2 setup

theorem CallingConditions.binary_setup_succeeds {program : CIL.Program}
    {memory : CIL.Safety.Memory} {left right output : Reference} {body : CIL.Method}
    (call : CallingConditions program memory [left, right] [output])
    (fits : FrameSetupFits body (binaryArguments left right output)) :
    ∃ frame entered, enterFrame body (binaryArguments left right output) memory = .ok (frame, entered) ∧
      LiveState program (binaryArguments left right output) frame [] entered :=
  enterFrame_live_succeeds _ _ _ _ call.1.1 call.binary_arguments_valid call.2 fits

#print axioms byteNumber_snapshot
#print axioms CallingConditions.of_requirements
#print axioms CallingConditions.input_snapshot
#print axioms CallingConditions.input_load
#print axioms CallingConditions.binary_arguments_valid
#print axioms CallingConditions.binary_entry_live
#print axioms CallingConditions.binary_setup_succeeds

end UInt256Model.Safety
