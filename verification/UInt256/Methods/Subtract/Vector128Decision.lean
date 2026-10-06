import UInt256.Methods.Subtract.Vector128Incoming

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector

def vector128Propagation (low high incomingLow incomingHigh : BitVec 128) : BitVec 128 :=
  (zip128 (fun x y => mask64 (x == y)) low 0 &&& incomingLow) |||
  (zip128 (fun x y => mask64 (x == y)) high 0 &&& incomingHigh)

/-- Evaluate the actual propagation test using initialized snapshots. The test
    changes neither caller memory nor private snapshots. -/
theorem vector128_decision (memory : Memory) (frame : Frame) (args : List Value)
    (low high incomingLow incomingHigh : BitVec 128)
    (lowHome highHome incomingLowHome incomingHighHome : Reference)
    (lowSlot : frame.locals[5]? = some (.bytes .vector128 lowHome))
    (highSlot : frame.locals[6]? = some (.bytes .vector128 highHome))
    (incomingLowSlot : frame.locals[9]? = some (.bytes .vector128 incomingLowHome))
    (incomingHighSlot : frame.locals[10]? = some (.bytes .vector128 incomingHighHome))
    (lowRead : read memory lowHome 16 1 = .ok (numberBytes low.toNat 16))
    (highRead : read memory highHome 16 1 = .ok (numberBytes high.toNat 16))
    (incomingLowRead : read memory incomingLowHome 16 1 = .ok (numberBytes incomingLow.toNat 16))
    (incomingHighRead : read memory incomingHighHome 16 1 = .ok (numberBytes incomingHigh.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel vector128Index
        (if vector128Propagation low high incomingLow incomingHigh = BitVec.ofNat 128 0 then 119 else 77)
        args frame [] memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel vector128Index 63 args frame [] memory = .ok (result, returned) ∧ post result returned := by
  have loadLow := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 low) low.toNat rfl lowSlot lowRead
  have loadHigh := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 high) high.toNat rfl highSlot highRead
  have loadIncomingLow := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 incomingLow) incomingLow.toNat rfl incomingLowSlot incomingLowRead
  have loadIncomingHigh := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := vector128Body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 incomingHigh) incomingHigh.toNat rfl incomingHighSlot incomingHighRead
  have found : Extracted.program[vector128Index]? = some vector128Body := by rfl
  have profile : vector128Body.profile = Extracted.profile := by rfl
  by_cases zero : vector128Propagation low high incomingLow incomingHigh = BitVec.ofNat 128 0
  all_goals
    simp only [zero, ite_true, ite_false] at continuation
    simp only [vector128Propagation] at zero
    iterate 14
      apply run_next_exists post found (by rfl)
      first
      | exact loadLow _ _
      | exact loadHigh _ _
      | exact loadIncomingLow _ _
      | exact loadIncomingHigh _ _
      | (simp (config := { implicitDefEqProofs := false })
             [step, profile, cil_code, pureArity, scalars, CIL.step, CIL.Intrinsic.available,
               intrinsic_zero128, intrinsic_eq128, intrinsic_and128, intrinsic_or128, intrinsic_equal_all128,
               show (0 : BitVec 128) = BitVec.ofNat 128 0 from rfl, zero,
               checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
         first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)
    simp at zero
    simp_all

#print axioms vector128_decision
end UInt256Proof.Subtract.Safety
