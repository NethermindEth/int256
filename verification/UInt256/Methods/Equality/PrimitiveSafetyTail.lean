import UInt256.Methods.Equality.PrimitiveSafetyPrefix
import CIL.Safety.NumericLocalStore

namespace UInt256Proof.Equality.Safety

open CIL.Safety UInt256Model.Safety

def primitiveEqualityCall : Nat := primitiveBody.code.findIdx fun op =>
  match op with | .call _ _ => true | _ => false

theorem primitive_store_prefix (memory updated : Memory) (left home : Reference)
    (right : CIL.Value) (bits : BitVec 256) (frame : Frame)
    (slots : frame.locals = [.bytes .vector256 home])
    (stored : storeLocal memory (.bytes .vector256 home) (.scalar (.v256 bits)) =
      .ok (.bytes .vector256 home, updated))
    (formed : form updated home = .ok home)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final values,
      run Extracted.program fuel primitiveIndex primitiveEqualityCall (primitiveArguments left right) frame
        [.reference (.address home), .reference (.address left)] updated = .ok (final, values) ∧
      post final values) :
    ∃ fuel final values,
      run Extracted.program fuel primitiveIndex (primitiveConstructorCall + 1)
        (primitiveArguments left right) frame [.scalar (.v256 bits), .reference (.address left)] memory =
        .ok (final, values) ∧ post final values := by
  rcases frame with ⟨activation, localSlots, owned, homes⟩
  change localSlots = _ at slots
  subst localSlots
  conv in primitiveIndex => cbv
  conv in primitiveConstructorCall => cbv
  conv at continuation in primitiveIndex => cbv
  conv at continuation in primitiveEqualityCall => cbv
  simp only [Nat.reduceAdd]
  repeat' first
    | exact continuation
    | (apply run_next_exists post
       · simp only [cil_code]; rfl
       · simp only [cil_code]; rfl
       · simp [step, stored, localAddress, formValue, formed,
           checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
         try (exact ⟨rfl, rfl, rfl, rfl⟩))

theorem primitive_return (args : List Value) (flag : BitVec 32) (frame : Frame) (memory : Memory) :
    run Extracted.program 1 primitiveIndex (primitiveEqualityCall + 1) args frame [.scalar (.i32 flag)] memory =
      .ok (leaveFrame frame memory, [.scalar (.i32 flag)]) := by
  conv in primitiveIndex => cbv
  conv in primitiveEqualityCall => cbv
  simp only [Nat.reduceAdd]
  simp [run, cil_code, step, checkedValue, numericValue,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms primitive_store_prefix
#print axioms primitive_return

end UInt256Proof.Equality.Safety
