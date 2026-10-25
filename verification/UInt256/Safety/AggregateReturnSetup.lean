import UInt256.Safety.ConstructorSetup
import CIL.Safety.AggregateLocals

namespace UInt256Model.Safety.AggregateReturn
open CIL.Safety UInt256Model.Safety

def frame (memory : Memory) (output : Reference) : Frame :=
  {
        activation := memory.nextIdentity
        locals := [.bytes (.aggregate 32) output]
        owned := [output.allocation]
        arguments := []
        stackBytes := 0 }

/-- Value-returning methods allocate one private UInt256 aggregate local. -/
theorem setup (body : CIL.Method) (args : List Value)
    (kinds : body.localKinds = [.aggregate 32])
    (initializers : body.locals = [.aggregate (List.replicate 32 0)])
    (vectorArgs : body.vectorArgs = []) (parameters : body.parameterHomes = [])
    (opaqueLocals : body.opaqueVectorLocals = [])
    (program : CIL.Program) (memory : Memory) (inputs : List Reference)
    (call : CallingConditions program memory inputs []) :
    ∃ output entered,
      enterFrame body args memory = .ok (frame memory output, entered) ∧
      CallingConditions program entered inputs [output] ∧
      MemoryBelow memory.nextIdentity memory entered ∧
      output.allocation = memory.nextIdentity := by
  obtain ⟨output, allocated, entered, allocatedHome, stored, _, writable, before, fresh⟩ :=
    allocate_initialized_aggregate memory memory.nextIdentity (32 : Fin (2^64))
      (List.replicate 32 0) (by decide) call.1.1
  have made : makeLocal memory.nextIdentity (.aggregate 32) (.aggregate (List.replicate 32 0)) memory =
      .ok (.bytes (.aggregate 32) output, [output.allocation], entered) := by
    simp only [makeLocal, localWidth, localAlignment, allocatedHome, stored, reduceCtorEq, ↓reduceIte,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  have enteredFrame : enterFrame body args memory = .ok (frame memory output, entered) := by
    simp only [enterFrame, opaqueLocals, makeSelectedLocals, List.isEmpty_nil, ite_true, kinds, initializers, makeLocals, made, vectorArgs, parameters,
      makeArgumentHomes, makeParameterHomes, frame, Bind.bind, Except.bind, Pure.pure, Except.pure, List.map_nil, List.append_nil]
  exact ⟨output, entered, enteredFrame,
    (call.after_frame_setup enteredFrame).with_writable_output writable, before, fresh⟩

#print axioms setup
end UInt256Model.Safety.AggregateReturn
