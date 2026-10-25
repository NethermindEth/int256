import CIL.Safety.AggregateHomeValues
import UInt256.Safety.ArgumentValues
import UInt256.Safety.CallerSetup

namespace UInt256Model.Safety
open CIL.Safety

def aggregate256 (value : BitVec 256) : Value :=
  .scalar (.aggregate (numberBytes value.toNat 32))

def parameterFrame32 (memory : Memory) (copy : Reference) : Frame :=
  {
        activation := memory.nextIdentity
        locals := [.bytes (.aggregate 32) copy]
        owned := [copy.allocation]
        arguments := []
        stackBytes := 0 }

/-- Address-taking creates a private initialized copy of the passed UInt256. -/
theorem parameter_setup32 (body : CIL.Method) (args : List Value) (value : BitVec 256)
    (kinds : body.localKinds = []) (initializers : body.locals = [])
    (vectors : body.vectorArgs = []) (parameters : body.parameterHomes = [(1, .aggregate 32)])
    (argument : args[1]? = some (aggregate256 value))
    (program : CIL.Program) (memory : Memory) (inputs : List Reference)
    (call : CallingConditions program memory inputs []) :
    ∃ copy entered,
      enterFrame body args memory = .ok (parameterFrame32 memory copy, entered) ∧
      CallingConditions program entered (inputs ++ [copy]) [] ∧
      inputValue entered copy = value ∧
      MemoryBelow memory.nextIdentity memory entered ∧
      copy.allocation = memory.nextIdentity := by
  obtain ⟨copy, entered, made, loaded, _, before, fresh⟩ :=
    make_parameter_home_aggregate memory memory.nextIdentity 1 args (32 : Fin (2^64))
      (numberBytes value.toNat 32) (by simp only [numberBytes, List.length_map, List.length_range]; rfl)
      call.1.1 argument
  have setup : enterFrame body args memory = .ok (parameterFrame32 memory copy, entered) := by
    simp only [enterFrame, kinds, initializers, makeSelectedLocals, makeLocals, makeSelectedLocalsFrom, ite_self, vectors, makeArgumentHomes,
      parameters, made, Bind.bind, Except.bind, Pure.pure, Except.pure,
      List.map_cons, List.map_nil, List.nil_append, parameterFrame32]
  exact ⟨copy, entered, setup, (call.after_frame_setup setup).with_readable_input loaded,
    inputValue_of_encoded_read loaded, before, fresh⟩

#print axioms parameter_setup32
end UInt256Model.Safety
