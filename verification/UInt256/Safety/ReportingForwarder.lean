import CIL.Safety.Equations
import UInt256.Safety.Contract
import UInt256.Safety.ReportingContract
import CIL.Safety.CallComposition
import CIL.Safety.StepComposition
import CIL.Safety.GuardNormalization
import CIL.Safety.Forwarders

/-!
Binary reporting wrappers reuse checked argument loading and call composition from LeanCIL.
The child certificate and caller-byte footprint remain separate from a `Confined` contract.
-/

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
      {
        activation := memory.nextIdentity
        locals := []
        owned := []
        arguments := []
        stackBytes := 0 } childReturned childFinal = .ok (childFinal, wrapperReturned)) :
    ∃ fuel, InvocationCertificate program wrapperIndex (binaryArguments left right output) memory fuel
      childFinal wrapperReturned := by
  let args := binaryArguments left right output
  let frame : Frame := {
        activation := memory.nextIdentity
        locals := []
        owned := []
        arguments := []
        stackBytes := 0 }
  have valid := call.binary_arguments_valid
  have checked := checkedValues_of_valid valid
  have setup : enterFrame wrapperBody args memory = .ok (frame, memory) := by
    simp [enterFrame, kinds, locals, parameters, vectors, makeSelectedLocals, makeLocals,
      makeSelectedLocalsFrom, ite_self, makeParameterHomes, makeArgumentHomes, frame,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  have stepped : step wrapperBody (.call childIndex 3) 3 args frame
      [.reference (.address output), .reference (.address right), .reference (.address left)] memory =
      .ok (.call childIndex args [] memory) := by
    exact step_call_loaded valid rfl
  have invoked : WP (Execution (fun fuel => invoke program fuel wrapperIndex args memory))
      (fun result => result = (childFinal, wrapperReturned)) := by
    apply WP.enter found checked setup
    apply WP.adequate.mpr
    apply run_load_arguments found valid (plainLoads [0, 1, 2]) 0 [] args
    · intro position load selected
      match position with
      | 0 => cases selected; exact f0
      | 1 => cases selected; exact f1
      | 2 => cases selected; exact f2
      | _ + 3 => simp [plainLoads] at selected
    · rfl
    · exact plainLoads_unchanged _ _
    · apply WP.exists_execution
      apply WP.call found f3 stepped
        (helperPost := fun result => result = (childFinal, childReturned))
        (WP.exact_iff.mpr ⟨childFuel, child⟩)
      intro final values same
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      exact WP.exact_iff.mpr ⟨2, by simpa only [Execution, args, frame, List.append_nil] using tail⟩
  obtain ⟨fuel, executed⟩ := WP.exact_iff.mp invoked
  exact ⟨fuel, InvocationCertificate.of_invoke call.1.wellFormed call.2 executed⟩

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
  have normalized : CIL.NarrowKind.unsigned8.extend bit = bit := CIL.NarrowKind.extend_ite_one_zero _ _
  obtain ⟨fuel, certified⟩ := forward_binary_call program wrapperIndex childIndex wrapperBody found
    (by simp [code]) (by simp [code]) (by simp [code]) (by simp [code]) kinds locals parameters vectors memory left right output call
    final _ _ childFuel certificate.1 (by
      apply run_return found fetch
      · exact step_return_unchanged (by simp [returns]) rfl rfl ⟨bit, rfl, normalized⟩
      · rfl)
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
  obtain ⟨fuel, certified⟩ := forward_binary_call program wrapperIndex childIndex wrapperBody found
    (by simp [code]) (by simp [code]) (by simp [code]) (by simp [code]) kinds locals parameters vectors memory left right output call
    final _ _ childFuel certificate.1 (by
      rw [run_next found popFetch (by rw [step_pop_eq]; rfl)]
      apply run_return found retFetch
      · exact step_return_unchanged (by simp [returns]) rfl rfl trivial
      · rfl)
  exact ⟨fuel, final, certified, value, writable, footprint⟩

end UInt256Model.Safety
