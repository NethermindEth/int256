import UInt256.Methods.Multiply.HomeExecution
open Lean Meta Elab Command Tactic CIL UInt256Model UInt256Proof UInt256Proof.Bitwise
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply

elab "multiply_home_storage_summaries" : command => do
  let indices ← liftTermElabM do listTerms (mkConst `Extracted.storageCandidates)
  for expression in indices do
    let .lit (.natVal index) ← liftTermElabM (whnf expression) | throwError "Expected concrete candidate"
    let number := Syntax.mkNumLit (toString index)
    let name := mkIdent (Name.mkSimple s!"execute_home_storage_{index}")
    let candidates := mkIdent `Extracted.storageCandidates
    elabCommand (← `(command| if_extracted $candidates {
      theorem $name (memory : Memory) (frame fuel outFrame outKind outIndex : Nat)
          (r0 r1 r2 r3 : W64) (bound : executionBound Extracted.program $number ≤ fuel) :
          ∃ final, run Extracted.program fuel $number 0
              [.ref (.home outFrame outKind outIndex 0), .i64 r0, .i64 r1, .i64 r2, .i64 r3]
              frame [] memory = some (final, []) ∧
            readAggregate final outFrame outKind outIndex =
              some (.v256 (CIL.Vector.pack256 r0 r1 r2 r3)) ∧
            (∀ address, final (.byte address) = memory (.byte address)) ∧
            ∀ other index, other ≠ frame → final (.local other index) = memory (.local other index) := by
        have splitFuel : fuel = (fuel - executionBound Extracted.program $number) +
            executionBound Extracted.program $number := by omega
        rw [splitFuel]
        generalize fuel - executionBound Extracted.program $number = remaining
        cil_execute_core evalMemory, write256, unsafeAsRef, unsafeAdd, offsetValue,
          aggregate_fourWrites, readAggregate_fullWrite, home_four_numbers with
          (fail "Use raw storage instructions")
        all_goals simp (config := { implicitDefEqProofs := false, failIfUnchanged := false }) only
          [home_four_numbers, word_cast_mod, BitVec.ofNat_toNat, four_value_pack]
        all_goals intro other index different
        all_goals simp [writeHomeBytes, write, different]
    }))

multiply_home_storage_summaries
end UInt256Proof.Multiply


