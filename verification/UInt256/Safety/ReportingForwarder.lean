import CIL.Safety.Equations
import UInt256.Safety.Contract
import UInt256.Safety.ReportingContract
import CIL.Safety.CallComposition
import CIL.Safety.StepComposition
import CIL.Safety.GuardNormalization

namespace UInt256Model.Safety
open CIL.Safety

/-- Run a localless `left right output` wrapper whose tail after the child call is certified separately. -/
theorem forward_binary_call (program : CIL.Program) (wrapperIndex childIndex : Nat)
    (wrapperBody : CIL.Method) (found : program[wrapperIndex]? = some wrapperBody)
    (f0 : wrapperBody.code[0]? = some (.arg 0)) (f1 : wrapperBody.code[1]? = some (.arg 1))
    (f2 : wrapperBody.code[2]? = some (.arg 2)) (f3 : wrapperBody.code[3]? = some (.call childIndex 3))
    (kinds : wrapperBody.localKinds = []) (locals : wrapperBody.locals = [])
    (parameters : wrapperBody.parameterHomes = []) (vectors : wrapperBody.vectorArgs = [])
    (memory : Memory) (left right output : Reference)
    (call : CallingConditions program memory [left, right] [output])
    (childFinal : Memory) (childReturned wrapperReturned : List Value) (childFuel : Nat)
    (child : invoke program childFuel childIndex (binaryArguments left right output) memory =
      .ok (childFinal, childReturned))
    (tail : run program 2 wrapperIndex 4 (binaryArguments left right output)
      ⟨memory.nextIdentity, [], [], []⟩ childReturned childFinal = .ok (childFinal, wrapperReturned)) :
    ∃ fuel, InvocationCertificate program wrapperIndex (binaryArguments left right output) memory fuel
      childFinal wrapperReturned := by
  let args := binaryArguments left right output
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have fl := call.input_formed (by simp : left ∈ [left, right])
  have fr := call.input_formed (by simp : right ∈ [left, right])
  have fo := call.output_formed (by simp : output ∈ [output])
  have fetched : wrapperBody.code[3]? = some (.call childIndex 3) := f3
  have stepped : step wrapperBody (.call childIndex 3) 3 args frame
      [.reference (.address output), .reference (.address right), .reference (.address left)] memory =
      .ok (.call childIndex args [] memory) := by
    simp [args, binaryArguments, step, cil_guard, observerCount, checkedValue, formValue, fl, fr, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨tailFuel, ran⟩ := run_call_exists found fetched stepped ⟨childFuel, child⟩
    ⟨2, by simpa only [List.append_nil] using tail⟩
  have prefixRun : ∃ fuel after returned,
      run program fuel wrapperIndex 0 args frame [] memory = .ok (after, returned) ∧
      after = childFinal ∧ returned = wrapperReturned := by
    apply run_next_exists (fun after returned => after = childFinal ∧ returned = wrapperReturned) found f0
    · simp [step, cil_guard, observerCount, args, binaryArguments, checkedValue, formValue, fl, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact ⟨rfl, rfl, rfl, rfl⟩
    apply run_next_exists (fun after returned => after = childFinal ∧ returned = wrapperReturned) found f1
    · simp [step, cil_guard, observerCount, args, binaryArguments, checkedValue, formValue, fr, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact ⟨rfl, rfl, rfl, rfl⟩
    apply run_next_exists (fun after returned => after = childFinal ∧ returned = wrapperReturned) found f2
    · simp [step, cil_guard, observerCount, args, binaryArguments, checkedValue, formValue, fo, checkedAt,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
      exact ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨tailFuel, childFinal, wrapperReturned, ran, rfl, rfl⟩
  obtain ⟨fuel, after, returned, executed, rfl, rfl⟩ := prefixRun
  have checked : args.mapM (checkedValue memory) = .ok args := by
    simp [args, binaryArguments, checkedValue, formValue, fl, fr, fo, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have setup : enterFrame wrapperBody args memory = .ok (frame, memory) := by
    simp [enterFrame, kinds, locals, parameters, vectors, makeSelectedLocals, makeLocals, makeSelectedLocalsFrom, ite_self, makeParameterHomes, makeArgumentHomes, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  exact ⟨fuel, certify_invocation _ _ _ _ _ _ _ _ _ _ found checked setup live executed⟩

/-- A wrapper that returns its child's byte flag keeps the child's reporting contract. -/
theorem forward_reporting_byte (program : CIL.Program) (wrapperIndex childIndex : Nat)
    (wrapperBody : CIL.Method) (operation : BitVec 256 → BitVec 256 → BitVec 256)
    (flag : BitVec 256 → BitVec 256 → Bool)
    (found : program[wrapperIndex]? = some wrapperBody)
    (code : wrapperBody.code = [.arg 0, .arg 1, .arg 2, .call childIndex 3, .ret (some .unsigned8)])
    (returns : wrapperBody.returnsValue = true)
    (kinds : wrapperBody.localKinds = []) (locals : wrapperBody.locals = [])
    (parameters : wrapperBody.parameterHomes = []) (vectors : wrapperBody.vectorArgs = [])
    (child : ReportingBinaryContract operation flag program childIndex) :
    ReportingBinaryContract operation flag program wrapperIndex := by
  intro memory left right output call
  obtain ⟨childFuel, final, certificate, value, writable, footprint⟩ := child memory left right output call
  let bit : BitVec 32 := if flag (inputValue memory left) (inputValue memory right) then 1 else 0
  have fetch : wrapperBody.code[4]? = some (.ret (some .unsigned8)) := by simp [code]
  have normalized : CIL.NarrowKind.unsigned8.extend bit = bit := by
    simp only [bit]
    split <;> rfl
  have tail : run program 2 wrapperIndex 4 (binaryArguments left right output)
      ⟨memory.nextIdentity, [], [], []⟩ [.scalar (.i32 bit)] final = .ok (final, [.scalar (.i32 bit)]) := by
    simp [run, found, fetch, returns, step, cil_guard, observerCount, normalized, leaveFrame, checkedValue, numericValue,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨fuel, certified⟩ := forward_binary_call program wrapperIndex childIndex wrapperBody found
    (by simp [code]) (by simp [code]) (by simp [code]) (by simp [code]) kinds locals parameters vectors memory left right output call
    final _ _ childFuel certificate.1 tail
  exact ⟨fuel, final, certified, value, writable, footprint⟩

/-- A wrapper that discards its child's flag keeps the child's arithmetic and footprint. -/
theorem forward_reporting_pop (program : CIL.Program) (wrapperIndex childIndex : Nat)
    (wrapperBody : CIL.Method) (operation : BitVec 256 → BitVec 256 → BitVec 256)
    (flag : BitVec 256 → BitVec 256 → Bool)
    (found : program[wrapperIndex]? = some wrapperBody)
    (code : wrapperBody.code = [.arg 0, .arg 1, .arg 2, .call childIndex 3, .pop, .ret])
    (returns : wrapperBody.returnsValue = false)
    (kinds : wrapperBody.localKinds = []) (locals : wrapperBody.locals = [])
    (parameters : wrapperBody.parameterHomes = []) (vectors : wrapperBody.vectorArgs = [])
    (child : ReportingBinaryContract operation flag program childIndex) :
    WrappingBinaryContract operation program wrapperIndex := by
  intro memory left right output call
  obtain ⟨childFuel, final, certificate, value, writable, footprint⟩ := child memory left right output call
  have popFetch : wrapperBody.code[4]? = some .pop := by simp [code]
  have retFetch : wrapperBody.code[5]? = some .ret := by simp [code]
  have tail : run program 2 wrapperIndex 4 (binaryArguments left right output)
      ⟨memory.nextIdentity, [], [], []⟩
      [.scalar (.i32 (if flag (inputValue memory left) (inputValue memory right) then 1 else 0))] final =
      .ok (final, []) := by
    simp [run, found, popFetch, retFetch, returns, step, cil_guard, observerCount, pureArity, leaveFrame,
      instruction, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  obtain ⟨fuel, certified⟩ := forward_binary_call program wrapperIndex childIndex wrapperBody found
    (by simp [code]) (by simp [code]) (by simp [code]) (by simp [code]) kinds locals parameters vectors memory left right output call
    final _ _ childFuel certificate.1 tail
  exact ⟨fuel, final, certified, value, writable, footprint⟩

#print axioms forward_binary_call
#print axioms forward_reporting_byte
#print axioms forward_reporting_pop
end UInt256Model.Safety
