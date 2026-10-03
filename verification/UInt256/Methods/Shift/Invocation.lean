import CIL.ExecutionLemmas

open CIL

namespace UInt256Proof.Shift

theorem invoke_plain (program : Program) (entry : Nat) (body : Method)
    (member : program[entry]? = some body)
    (locals : body.aggregateLocals = []) (arguments : body.aggregateArgs = [])
    (memory final : Memory) (args result : List Value) (fuel : Nat)
    (execution : run program fuel entry 0 args 0 [] (initLocals memory 0 body.locals) =
      some (final, result)) :
    invoke program fuel entry args memory = some (final, result) := by
  simp only [invoke, member, bind, Option.bind]
  rw [initFrame_plain memory 0 body args locals arguments]
  exact execution

theorem invoke_frame (program : Program) (entry : Nat) (body : Method)
    (member : program[entry]? = some body)
    (memory final : Memory) (args values : List Value) (fuel : Nat)
    (execution : run program fuel entry 0 args 0 [] (initFrame memory 0 body args) =
      some (final, values)) :
    invoke program fuel entry args memory = some (final, values) := by
  simpa only [invoke, member, bind, Option.bind] using execution

end UInt256Proof.Shift
