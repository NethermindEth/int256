import UInt256.Methods.Add.Vector128ARMRepairCarry

namespace UInt256Proof.Add.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety

/-- The ARM repair suffix returns the updated high-lane carry bit and retires its frame.
    The arithmetic meaning of this flag is established separately from stepping. -/
theorem vector128_arm_repair_return (enabled : Extracted.profile.advSimd = true)
    (memory : Memory) (frame : Frame) (args : List Value)
    (home : Reference) (mask : BitVec 128)
    (slot : frame.locals[7]? = some (.bytes .vector128 home))
    (loaded : read memory home 16 1 = .ok (numberBytes mask.toNat 16)) :
    run Extracted.program 7 vector128Index 155 args frame [] memory =
      .ok (leaveFrame frame memory,
        [.scalar (.i32 (if CIL.Vector.lane64 mask 1 > BitVec.ofNat 64 0 then 1 else 0))]) := by
  first
  | solve | simp [Extracted.profile] at enabled
  |
    have load := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
      (body := vector128Body) (args := args) (pc := pc) (stack := stack)
      .vector128 (.v128 mask) mask.toNat rfl slot loaded
    have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
    have profile : vector128Body.profile = Extracted.profile := by rfl
    have returns : vector128Body.returnsValue = true := by rfl
    iterate 6
      apply Eq.trans
      · apply run_next found (by rfl)
        first
        | exact load _ _
        | (simp (config := { implicitDefEqProofs := false })
            [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.binary,
              CIL.Intrinsic.available, CIL.Vector.intrinsic_extract128,
              checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
           first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)
    have fetched : vector128Body.code[161]? = some .ret := by rfl
    simp [run, found, fetched, returns, step, checkedValue, numericValue,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms vector128_arm_repair_return
end UInt256Proof.Add.Safety
