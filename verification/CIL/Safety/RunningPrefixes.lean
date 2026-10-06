import CIL.Safety.StepLiveState

namespace CIL.Safety

theorem FrameAction.child_arguments_valid {program : CIL.Program} {args : List Value}
    {frame : Frame} {action : FrameAction} {callee : Nat} {arguments : List Value}
    (valid : action.StateValid program args frame) (call : action.child callee arguments) :
    ValuesValid action.memory arguments := by
  rcases call with ⟨rest, equal⟩ | ⟨rest, nextFrame, temporary, equal⟩
  · cases action <;> cases equal
    exact valid.2
  · cases action <;> cases equal
    exact valid.2

theorem enter_child_live_state {program : CIL.Program} {method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction}
    {callee : Nat} {arguments : List Value} {child : CIL.Method} {childFrame : Frame} {childMemory : Memory}
    (step : ProgramStep program method pc args frame stack m action)
    (state : LiveState program args frame stack m) (call : action.child callee arguments)
    (enter : enterFrame child arguments action.memory = .ok (childFrame, childMemory)) :
    LiveState program arguments childFrame [] childMemory :=
  enterFrame_live_state _ _ _ _ _ _
    (programStep_preserves_wellFormed _ _ _ _ _ _ _ _ state.memory step)
    (FrameAction.child_arguments_valid (programStep_live_state step state) call)
    (programStep_preserves_static_world step state.memory state.statics) enter

theorem constructor_resume_live_state (program : CIL.Program) (fuel method : Nat)
    (body : CIL.Method) (childArgs args rest : List Value) (child parent : Frame)
    (temporary : Reference) (value : CIL.Value) (m entered final : Memory)
    (state : LiveState program args parent rest m)
    (setup : enterFrame body childArgs m = .ok (child, entered))
    (finish : run program fuel method 0 childArgs child [] entered = .ok (final, []))
    (load : loadValue final (.address temporary) (localWidth .vector256) = .ok value) :
    LiveState program args parent (.scalar value :: rest) final := by
  have preserved := child_preserves_parent_state _ _ _ _ _ _ _ _ _ _ _ _ _ state setup finish
  exact { preserved with stack := ValuesValid.cons (loadValue_scalar_valid _ _ _ _ load) preserved.stack }

/-- Actual running and suspended frame boundaries. Returned frames are absent:
    their private storage has expired and their result is checked separately. -/
inductive RunningVisits (program : CIL.Program) : Nat → Nat → Nat → List Value → Frame →
    List Value → Memory → List Value → Frame → List Value → Memory → Prop where
  | initial {fuel method pc args frame stack m} :
      RunningVisits program fuel method pc args frame stack m args frame stack m
  | next {fuel method pc args frame stack m target values nextFrame updated oa of os om}
      (step : ProgramStep program method pc args frame stack m (.next target values nextFrame updated))
      (later : RunningVisits program fuel method target args nextFrame values updated oa of os om) :
      RunningVisits program (fuel + 1) method pc args frame stack m oa of os om
  | suspendedCall {fuel method pc args frame stack m callee arguments rest updated}
      (step : ProgramStep program method pc args frame stack m (.call callee arguments rest updated)) :
      RunningVisits program (fuel + 1) method pc args frame stack m args frame rest updated
  | suspendedConstruct {fuel method pc args frame stack m callee arguments rest nextFrame temporary updated}
      (step : ProgramStep program method pc args frame stack m
        (.construct callee arguments rest nextFrame temporary updated)) :
      RunningVisits program (fuel + 1) method pc args frame stack m args nextFrame rest updated
  | child {fuel method pc args frame stack m action callee arguments child childFrame childMemory oa of os om}
      (step : ProgramStep program method pc args frame stack m action)
      (call : action.child callee arguments) (lookup : program[callee]? = some child)
      (enter : enterFrame child arguments action.memory = .ok (childFrame, childMemory))
      (later : RunningVisits program fuel callee 0 arguments childFrame [] childMemory oa of os om) :
      RunningVisits program (fuel + 1) method pc args frame stack m oa of os om
  | callContinue {fuel method pc args frame stack m callee arguments rest updated child
        childFrame childMemory returned result oa of os om}
      (step : ProgramStep program method pc args frame stack m (.call callee arguments rest updated))
      (lookup : program[callee]? = some child)
      (enter : enterFrame child arguments updated = .ok (childFrame, childMemory))
      (finish : run program fuel callee 0 arguments childFrame [] childMemory = .ok (returned, result))
      (later : RunningVisits program fuel method (pc + 1) args frame (result ++ rest) returned oa of os om) :
      RunningVisits program (fuel + 1) method pc args frame stack m oa of os om
  | constructContinue {fuel method pc args frame stack m callee arguments rest nextFrame temporary
        updated child childFrame childMemory returned value oa of os om}
      (step : ProgramStep program method pc args frame stack m
        (.construct callee arguments rest nextFrame temporary updated))
      (lookup : program[callee]? = some child)
      (enter : enterFrame child arguments updated = .ok (childFrame, childMemory))
      (finish : run program fuel callee 0 arguments childFrame [] childMemory = .ok (returned, []))
      (load : loadValue returned (.address temporary) (localWidth .vector256) = .ok value)
      (later : RunningVisits program fuel method (pc + 1) args nextFrame (.scalar value :: rest) returned oa of os om) :
      RunningVisits program (fuel + 1) method pc args frame stack m oa of os om

theorem runningVisits_live_state {program : CIL.Program} {fuel method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m : Memory}
    {observedArgs : List Value} {observedFrame : Frame} {observedStack : List Value} {observed : Memory}
    (visit : RunningVisits program fuel method pc args frame stack m
      observedArgs observedFrame observedStack observed)
    (state : LiveState program args frame stack m) :
    LiveState program observedArgs observedFrame observedStack observed := by
  induction visit with
  | initial => exact state
  | next step later ih => exact ih (programStep_live_state step state)
  | suspendedCall step => exact (programStep_live_state step state).1
  | suspendedConstruct step => exact (programStep_live_state step state).1
  | child step call lookup enter later ih => exact ih (enter_child_live_state step state call enter)
  | callContinue step lookup enter finish later ih =>
    exact ih (child_resume_live_state _ _ _ _ _ _ _ _ _ _ _ _ _
      (programStep_live_state step state).1 enter finish)
  | constructContinue step lookup enter finish load later ih =>
    exact ih (constructor_resume_live_state _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (programStep_live_state step state).1 enter finish load)

theorem runningVisits_memory_observation {program : CIL.Program} {fuel method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m : Memory}
    {observedArgs : List Value} {observedFrame : Frame} {observedStack : List Value} {observed : Memory}
    (visit : RunningVisits program fuel method pc args frame stack m
      observedArgs observedFrame observedStack observed) :
    RunVisits program fuel method pc args frame stack m observed := by
  induction visit with
  | initial => exact .initial
  | next step later ih => exact .next step ih
  | suspendedCall step => exact .stepped step
  | suspendedConstruct step => exact .stepped step
  | child step call lookup enter later ih => exact .child step call lookup enter ih
  | callContinue step lookup enter finish later ih => exact .callContinue step lookup enter finish ih
  | constructContinue step lookup enter finish load later ih =>
    exact .constructContinue step lookup enter finish load ih

def ReturnedState (program : CIL.Program) (memory : Memory) (values : List Value) : Prop :=
  memory.WellFormed ∧ ValuesValid memory values ∧ StaticWorldValid (programStaticDescriptors program) memory

theorem run_returned_state (program : CIL.Program) (fuel method pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m final : Memory) (values : List Value)
    (state : LiveState program args frame stack m)
    (h : run program fuel method pc args frame stack m = .ok (final, values)) :
    ReturnedState program final values :=
  ⟨run_preserves_wellFormed _ _ _ _ _ _ _ _ _ _ state.memory h,
    run_result_valid _ _ _ _ _ _ _ _ _ _ h,
    run_preserves_static_world _ _ _ _ _ _ _ _ _ _ state.memory state.owned state.statics h⟩

#print axioms enter_child_live_state
#print axioms constructor_resume_live_state
#print axioms runningVisits_live_state
#print axioms runningVisits_memory_observation
#print axioms run_returned_state

end CIL.Safety
