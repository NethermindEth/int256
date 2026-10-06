import UInt256.Methods.Add.VectorParentFastMath
import UInt256.Methods.Add.VectorParentCall

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

def parentFastReturn : Nat := match prepareParentBody.code[prepareCall + 8]? with
  | some (.brzero target) => target
  | _ => 0

/-- Read only the initialized private masks, then follow the extracted branch.
    Neither outcome rereads potentially overwritten caller inputs. -/
theorem vector_parent_branch (memory : Memory) (frame : Frame) (args : List Value)
    (propagationHome incomingHome : Reference) (propagation incoming : BitVec 256)
    (propagationSlot : frame.locals[3]? = some (.bytes .vector256 propagationHome))
    (incomingSlot : frame.locals[2]? = some (.bytes .vector256 incomingHome))
    (propagationRead : read memory propagationHome 32 1 = .ok (numberBytes propagation.toNat 32))
    (incomingRead : read memory incomingHome 32 1 = .ok (numberBytes incoming.toNat 32))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run Extracted.program fuel prepareParentIndex
        (if parentPropagationBits propagation incoming = BitVec.ofNat 32 0 then parentFastReturn else prepareCall + 9)
        args frame [] memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel prepareParentIndex (prepareCall + 1) args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  have loadPropagation := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := prepareParentBody) (args := args) (pc := pc) (stack := stack)
    .vector256 (.v256 propagation) propagation.toNat rfl propagationSlot propagationRead
  have loadIncoming := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := prepareParentBody) (args := args) (pc := pc) (stack := stack)
    .vector256 (.v256 incoming) incoming.toNat rfl incomingSlot incomingRead
  have found : Extracted.program[prepareParentIndex]? = some prepareParentBody := by rfl
  have profile : prepareParentBody.profile = Extracted.profile := by rfl
  have callPC : prepareCall = prepareCall := rfl
  conv at callPC => rhs; cbv
  have returnPC : parentFastReturn = parentFastReturn := rfl
  conv at returnPC => rhs; cbv
  simp only [callPC, returnPC] at continuation
  rw [callPC]
  by_cases zero : parentPropagationBits propagation incoming = BitVec.ofNat 32 0
  all_goals
    simp only [zero, ite_true, ite_false] at continuation
    simp only [parentPropagationBits] at zero
    repeat' first
      | (simpa [show (0 : BitVec 32) = BitVec.ofNat 32 0 from rfl, zero] using continuation)
      | (simp (config := { failIfUnchanged := false }) [show (0 : BitVec 32) = BitVec.ofNat 32 0 from rfl, zero]
         apply run_next_exists post found (by rfl)
         first
         | exact loadPropagation _ _
         | exact loadIncoming _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.binary,
               CIL.Intrinsic.available, CIL.Vector.intrinsic_and256,
               CIL.Vector.intrinsic_reinterpret256, CIL.Vector.intrinsic_movemask256,
               show (0 : BitVec 32) = BitVec.ofNat 32 0 from rfl, zero, checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

theorem vector_parent_return (memory : Memory) (frame : Frame) (args : List Value) :
    run Extracted.program 1 prepareParentIndex parentFastReturn args frame [] memory =
      .ok (leaveFrame frame memory, []) := by
  have found : Extracted.program[prepareParentIndex]? = some prepareParentBody := by rfl
  have fetched : prepareParentBody.code[parentFastReturn]? = some .ret := by rfl
  have returns : prepareParentBody.returnsValue = false := by rfl
  simp [run, found, fetched, returns, step, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms vector_parent_branch
#print axioms vector_parent_return
end UInt256Proof.Add.Safety
