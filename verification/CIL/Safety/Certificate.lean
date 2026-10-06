import CIL.Safety.RunReturnTrace

namespace CIL.Safety

/-- Evidence for the actual invocation, including nested running/suspended
    states. Successful execution excludes checked faults and fuel exhaustion;
    the visited-state clause additionally exposes reference/lifetime invariants. -/
def InvocationCertificate (program : CIL.Program) (method : Nat) (args : List Value)
    (initial : Memory) (fuel : Nat) (final : Memory) (values : List Value) : Prop :=
  invoke program fuel method args initial = .ok (final, values) ∧
  ∃ body frame entered,
    program[method]? = some body ∧
    args.mapM (checkedValue initial) = .ok args ∧
    enterFrame body args initial = .ok (frame, entered) ∧
    run program fuel method 0 args frame [] entered = .ok (final, values) ∧
    LiveState program args frame [] entered ∧
    (∀ observedArgs observedFrame observedStack observed,
      RunningVisits program fuel method 0 args frame [] entered
        observedArgs observedFrame observedStack observed →
      LiveState program observedArgs observedFrame observedStack observed) ∧
    ReturnedState program final values

theorem certify_invocation (program : CIL.Program) (method : Nat) (body : CIL.Method)
    (args : List Value) (initial : Memory) (frame : Frame) (entered : Memory)
    (fuel : Nat) (final : Memory) (values : List Value)
    (lookup : program[method]? = some body)
    (checked : args.mapM (checkedValue initial) = .ok args)
    (setup : enterFrame body args initial = .ok (frame, entered))
    (live : LiveState program args frame [] entered)
    (finished : run program fuel method 0 args frame [] entered = .ok (final, values)) :
    InvocationCertificate program method args initial fuel final values := by
  refine ⟨?_, body, frame, entered, lookup, checked, setup, finished, live, ?_, ?_⟩
  · simpa only [invoke, lookup, checked, setup, Except.mapError, Bind.bind, Except.bind] using finished
  · intro observedArgs observedFrame observedStack observed visit
    exact runningVisits_live_state visit live
  · exact run_returned_state _ _ _ _ _ _ _ _ _ _ live finished

#print axioms certify_invocation

end CIL.Safety
