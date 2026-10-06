import UInt256.Methods.Shift.SafetySetup
import CIL.Safety.CallComposition
import CIL.Safety.StepComposition

namespace UInt256Proof.Shift.Safety
open CIL.Safety

def countHelperIndex : Nat :=
  match shiftBody.code[1]? with
  | some (CIL.Op.call index 1) => index
  | _ => 0

def countHelperBody : CIL.Method := Extracted.program[countHelperIndex]?.getD
  { code := [], locals := [], returnsValue := false }

/-- Recheck the optional count helper's actual body. In the inline extraction,
    the fetched-call premise is impossible. No imported helper contract is assumed. -/
theorem shift_count_helper (memory : Memory) (count : BitVec 32)
    (helper : shiftBody.code[1]? = some (.call countHelperIndex 1)) :
    invoke Extracted.program 4 countHelperIndex [.scalar (.i32 count)] memory =
      .ok (memory, [.scalar (.i32 (count.sshiftRight 6))]) := by
  first
  | solve | cases helper
  | have found : Extracted.program[countHelperIndex]? = some countHelperBody := by rfl
    let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
    have setup : enterFrame countHelperBody [.scalar (.i32 count)] memory = .ok (frame, memory) := by
      have kinds : countHelperBody.localKinds = [] := by rfl
      have locals : countHelperBody.locals = [] := by rfl
      have arguments : countHelperBody.aggregateArgs = [] := by rfl
      simp [enterFrame, kinds, locals, arguments, makeLocals, makeArgumentHomes, frame,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    simp [invoke, found, checkedValue, numericValue, checkedAt, setup,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    iterate 3
      apply Eq.trans
      · apply run_next found (by rfl)
        simp [step, checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.binary,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
        first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩
    have returns : countHelperBody.returnsValue = true := by rfl
    have fetched : countHelperBody.code[3]? = some .ret := by rfl
    simp [run, found, fetched, returns, step, frame, leaveFrame,
      checkedValue, numericValue, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms shift_count_helper
end UInt256Proof.Shift.Safety
