import UInt256.Safety.ReportingForwarder

namespace UInt256Model.Safety
open CIL.Safety

/-- Forward the child arithmetic, output authority and caller-byte footprint unchanged. -/
theorem forward_wrapping_binary (program : CIL.Program) (wrapperIndex childIndex : Nat)
    (wrapperBody : CIL.Method) (operation : BitVec 256 → BitVec 256 → BitVec 256)
    (found : program[wrapperIndex]? = some wrapperBody)
    (code : wrapperBody.code = [.arg 0, .arg 1, .arg 2, .call childIndex 3, .ret])
    (returns : wrapperBody.returnsValue = false)
    (kinds : wrapperBody.localKinds = []) (locals : wrapperBody.locals = [])
    (parameters : wrapperBody.parameterHomes = []) (vectors : wrapperBody.vectorArgs = [])
    (child : WrappingBinaryContract operation program childIndex) :
    WrappingBinaryContract operation program wrapperIndex := by
  intro memory left right output call
  obtain ⟨childFuel, final, certificate, value, writable, footprint⟩ :=
    child memory left right output call
  have fetch : wrapperBody.code[4]? = some .ret := by simp [code]
  obtain ⟨fuel, certified⟩ := forward_binary_call program wrapperIndex childIndex wrapperBody found
    (by simp [code]) (by simp [code]) (by simp [code]) (by simp [code])
    kinds locals parameters vectors memory left right output call final [] [] childFuel certificate.1 (by
      simp [run, found, fetch, returns, step, cil_guard, observerCount, leaveFrame,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure])
  exact ⟨fuel, final, certified, value, writable, footprint⟩

end UInt256Model.Safety
