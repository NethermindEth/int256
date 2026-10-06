import UInt256.Methods.Add.VectorParentCall
import UInt256.Methods.Add.VectorRepairReporting

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Model CIL.Vector

def parentRepairCall : Nat := prepareParentBody.code.findIdx fun op => match op with
  | .call callee 4 => callee == repairIndex | _ => false

/-- Load the saved initial-value vectors and call the certified correction
    helper. The public input locations are never reread here. -/
theorem vector_parent_repair_call (memory : Memory) (output sum mask propagation : Reference)
    (frame : Frame) (args : List Value) (a b : Limbs)
    (call : CallingConditions Extracted.program memory [] [output])
    (outputArgument : args[2]? = some (.reference (.address output)))
    (sumSlot : frame.locals[0]? = some (.bytes .vector256 sum))
    (maskSlot : frame.locals[1]? = some (.bytes .vector256 mask))
    (propagationSlot : frame.locals[3]? = some (.bytes .vector256 propagation))
    (sumRead : read memory sum 32 1 = .ok (numberBytes (zip256 (· + ·) (value a) (value b)).toNat 32))
    (maskRead : read memory mask 32 1 = .ok (numberBytes (generatedCarry (value a) (value b)).toNat 32))
    (propagationRead : read memory propagation 32 1 = .ok
      (numberBytes (propagationMask (zip256 (· + ·) (value a) (value b))).toNat 32))
    (post : Memory → List Value → Prop)
    (continuation : ∀ after flag,
      flag = (if 2^256 ≤ (value a).toNat + (value b).toNat then 1 else 0) →
      ReturnedState Extracted.program after [.scalar (.i32 flag)] →
      read after output 32 1 = .ok (numberBytes (value a + value b).toNat 32) →
      access after output 32 1 true = .ok () →
      (∀ id offset, id < memory.nextIdentity → OutsideOutput output id offset →
        after.cells id offset = memory.cells id offset) →
      ∃ fuel final returned,
        run Extracted.program fuel prepareParentIndex (parentRepairCall+1) args frame [.scalar (.i32 flag)] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel prepareParentIndex (parentRepairCall-4) args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  obtain ⟨childFuel, after, certificate, result, writable, footprint⟩ :=
    checked_repair_reporting memory output a b call
  let flag : BitVec 32 := if 2^256 ≤ (value a).toNat + (value b).toNat then 1 else 0
  have returnedState : ReturnedState Extracted.program after [.scalar (.i32 flag)] := by
    obtain ⟨_, _, _, _, _, _, _, _, _, returned⟩ := certificate.2
    exact returned
  obtain ⟨tailFuel, final, returned, tail, satisfied⟩ :=
    continuation after flag rfl returnedState result writable footprint
  let childArgs := repairArguments (zip256 (· + ·) (value a) (value b))
    (generatedCarry (value a) (value b)) (propagationMask (zip256 (· + ·) (value a) (value b))) output
  have found : Extracted.program[prepareParentIndex]? = some prepareParentBody := by rfl
  have fetched : prepareParentBody.code[parentRepairCall]? = some (.call repairIndex 4) := by rfl
  have formed := call.output_formed (reference := output) (by simp)
  have stepped : step prepareParentBody (.call repairIndex 4) parentRepairCall args frame childArgs.reverse memory =
      .ok (.call repairIndex childArgs [] memory) := by
    simp [childArgs, repairArguments, step, checkedValue, numericValue, formValue, formed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨combined, executed⟩ := run_call_exists found fetched stepped ⟨childFuel, certificate.1⟩ ⟨tailFuel, tail⟩
  have done : ∃ fuel final returned,
      run Extracted.program fuel prepareParentIndex parentRepairCall args frame childArgs.reverse memory =
        .ok (final, returned) ∧ post final returned := ⟨combined, final, returned, executed, satisfied⟩
  have loadSum := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := prepareParentBody) (args := args) (pc := pc) (stack := stack)
    .vector256 (.v256 (zip256 (· + ·) (value a) (value b))) _ rfl sumSlot sumRead
  have loadMask := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := prepareParentBody) (args := args) (pc := pc) (stack := stack)
    .vector256 (.v256 (generatedCarry (value a) (value b))) _ rfl maskSlot maskRead
  have loadPropagation := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := prepareParentBody) (args := args) (pc := pc) (stack := stack)
    .vector256 (.v256 (propagationMask (zip256 (· + ·) (value a) (value b)))) _ rfl propagationSlot propagationRead
  conv at done in parentRepairCall => cbv
  conv in parentRepairCall => cbv
  repeat' first
    | exact done
    | (apply run_next_exists post found (by rfl)
       first
       | exact loadSum _ _
       | exact loadMask _ _
       | exact loadPropagation _ _
       | (simp [step, outputArgument, checkedValue, formValue, formed, checkedAt, Except.mapError,
           Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms vector_parent_repair_call
end UInt256Proof.Add.Safety
