import CIL.Safety.WordSnapshots
import CIL.Safety.ExecutionLifetime
import CIL.Safety.ExecutionStaticWorld
import UInt256.Safety.PrivateCalls
import UInt256.Safety.OutputAccess

namespace UInt256Model.Safety
open CIL.Safety

/-- Initialized private words and the original caller memory remain separate.
    Allocation growth and access authority support nested checked helper calls. -/
structure PrivateWords (program : CIL.Program) (original entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (known : Nat → Option (BitVec 64)) : Prop where
  call : CallingConditions program current inputs outputs
  enteredBound : original.nextIdentity ≤ entered.nextIdentity
  next : entered.nextIdentity ≤ current.nextIdentity
  authority : AccessBelow entered.nextIdentity entered current
  snapshots : WordSnapshots current frame.locals known
  caller : ∀ id, id < original.nextIdentity → ∀ offset, current.cells id offset = original.cells id offset

theorem PrivateWords.initial {program : CIL.Program} {original entered : Memory}
    {inputs outputs : List Reference} {body : CIL.Method} {args : List Value} {frame : Frame}
    (call : CallingConditions program original inputs outputs)
    (setup : enterFrame body args original = .ok (frame, entered)) :
    PrivateWords program original entered entered inputs outputs frame (fun _ => none) :=
  ⟨call.after_frame_setup setup, (enterFrame_fresh _ _ _ _ _ setup).1.next, Nat.le_refl _,
    (MemoryBelow.refl _ _).accessBelow, WordSnapshots.empty _ _,
    (enterFrame_preserves_caller_memory _ _ _ _ _ setup).cells⟩

/-- A real local store adds one remembered value; unknown homes require no
    fabricated initializer or prior read permission. -/
theorem PrivateWords.store {program : CIL.Program} {original entered current : Memory}
    {inputs outputs : List Reference} {body : CIL.Method} {frame : Frame} {known : Nat → Option (BitVec 64)}
    {kinds : List CIL.LocalKind}
    (state : PrivateWords program original entered current inputs outputs frame known)
    (enteredWF : entered.WellFormed)
    (homes : WritableHomes entered original.nextIdentity kinds frame.locals)
    (index : Nat) (specified : kinds[index]? = some .word64) (value : BitVec 64)
    (pc : Nat) (args stack : List Value) :
    ∃ after,
      step body (.setLocal index) pc args frame (.scalar (.i64 value) :: stack) current =
        .ok (.next (pc + 1) stack frame after) ∧
      PrivateWords program original entered after inputs outputs frame (rememberWord known index value) := by
  obtain ⟨reference, slot, bound, ready⟩ := homes.home_at index .word64 specified
  obtain ⟨allocation, requirements⟩ := access_requirements ready
  have writable := state.authority.access ready (enteredWF.1 _ _ requirements.present).1
  obtain ⟨after, stepped, snapshots, wf, preserved, authority, written⟩ :=
    state.snapshots.store homes state.call.1.1 reference value slot writable
      (body := body) (pc := pc) (args := args) (stack := stack)
  refine ⟨after, stepped, state.call.after_write written, state.enteredBound,
    Nat.le_trans state.next (write_extends_allocations _ _ _ _ _ written).next,
    state.authority.trans (authority.weaken state.next), snapshots, ?_⟩
  intro id old offset
  exact (preserved.cells id old offset).trans (state.caller id old offset)

/-- Import a proved helper's one-word effect. The helper's actual invocation
    supplies lifetime/static-world preservation; its contract supplies readback,
    authority and unchanged caller bytes. -/
theorem PrivateWords.after_word_call {program : CIL.Program} {original entered current after : Memory}
    {inputs outputs : List Reference} {frame : Frame} {known : Nat → Option (BitVec 64)}
    {kinds : List CIL.LocalKind}
    (state : PrivateWords program original entered current inputs outputs frame known)
    (originalCall : CallingConditions program original inputs outputs)
    (homes : WritableHomes entered original.nextIdentity kinds frame.locals)
    (fuel method : Nat) (args returned : List Value)
    (invoked : invoke program fuel method args current = .ok (after, returned))
    (index : Nat) (reference : Reference) (value : BitVec 64)
    (slot : frame.locals[index]? = some (.bytes .word64 reference))
    (wf : after.WellFormed)
    (loaded : read after reference 8 1 = .ok (numberBytes value.toNat 8))
    (authority : AccessBelow current.nextIdentity current after)
    (outside : ∀ id, id < current.nextIdentity → id ≠ reference.allocation → ∀ offset,
      after.cells id offset = current.cells id offset) :
    PrivateWords program original entered after inputs outputs frame (rememberWord known index value) := by
  have homeBound := homes.home_bound index .word64 reference slot
  have caller (id : Nat) (old : id < original.nextIdentity) (offset : Nat) :
      after.cells id offset = original.cells id offset :=
    (outside id (Nat.lt_of_lt_of_le old (Nat.le_trans state.enteredBound state.next))
      (Nat.ne_of_lt (Nat.lt_of_lt_of_le old homeBound)) offset).trans (state.caller id old offset)
  have world := invoke_preserves_static_world program fuel method args returned current after
    state.call.1.1 state.call.2 invoked
  have call := state.call.after_preserving_inputs wf authority world (by
    intro input member offset limit
    obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (originalCall.input_formed member)
    have old := (originalCall.1.1.1 _ _ present).1
    exact (caller input.allocation old _).trans (state.caller input.allocation old _).symm)
  exact ⟨call, state.enteredBound,
    Nat.le_trans state.next (invoke_preserves_caller_allocations program fuel method args returned current after invoked).next,
    state.authority.trans (authority.weaken state.next),
    state.snapshots.after_effect homes state.call.1.1 index reference value slot loaded authority outside, caller⟩

#print axioms PrivateWords.initial
#print axioms PrivateWords.store
#print axioms PrivateWords.after_word_call
end UInt256Model.Safety
