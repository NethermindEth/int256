import UInt256.Methods.Add.ScalarLeftPrefix
import UInt256.Methods.Add.CarryCall

namespace UInt256Proof.Safety

open CIL.Safety

def scalarFirstCarryCall : Nat :=
  Extracted.addScalarBody.code.findIdx fun op => match op with
    | .call callee _ => callee == Extracted.addWithCarryIndex
    | _ => false

/-- Both operands have upper limbs. Follow the second decision, scalar ISA
    guard, carry initialization and actual local loads/address formation. -/
theorem scalar_carry_prefix (args : List Value) (frame : Frame) (before after : Memory)
    (leftUpper a b : BitVec 64) (largeLeft : leftUpper ≠ BitVec.ofNat 64 0)
    (leftHome rightHome carryHome resultHome : Reference)
    (leftSlot : frame.locals[1]? = some (.bytes .word64 leftHome))
    (rightSlot : frame.locals[0]? = some (.bytes .word64 rightHome))
    (carrySlot : frame.locals[2]? = some (.bytes .word64 carryHome))
    (resultSlot : frame.locals[3]? = some (.bytes .word64 resultHome))
    (leftRead : read after leftHome 8 1 = .ok (numberBytes a.toNat 8))
    (rightRead : read after rightHome 8 1 = .ok (numberBytes b.toNat 8))
    (carryFormed : form after carryHome = .ok carryHome)
    (resultFormed : form after resultHome = .ok resultHome)
    (stored : ∀ pc rest, step Extracted.addScalarBody (.setLocal 2) pc args frame
      (.scalar (.i64 0) :: rest) before = .ok (.next (pc + 1) rest frame after))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex scalarFirstCarryCall args frame
        [.reference (.address resultHome), .reference (.address carryHome), .scalar (.i64 b), .scalar (.i64 a)]
        after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex scalarSecondDecision args frame
        [.scalar (.i64 leftUpper)] before = .ok (result, returned) ∧ post result returned := by
  conv in scalarSecondDecision => cbv
  have leftLoaded := load_local_word64_of_read leftRead
  have rightLoaded := load_local_word64_of_read rightRead
  repeat'
    first
    | exact continuation
    | simp (config := { failIfUnchanged := false }) [BitVec.ofNat_eq_ofNat, largeLeft]
      apply run_next_exists post
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · first
        | exact stored _ _
        | simp (config := { implicitDefEqProofs := false })
            [cil_code, step, checkedValue, numericValue, formValue, carryFormed, resultFormed,
              leftSlot, rightSlot, carrySlot, resultSlot, leftLoaded, rightLoaded, localAddress,
              pureArity, scalars, CIL.step, CIL.FeatureProfile.evaluate, instruction,
              checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩

/-- Bind the first discovered parent call to the checked carry contract. -/
theorem scalar_first_carry (args : List Value) (frame : Frame) (memory : Memory)
    (a b : BitVec 64) (carryHome resultHome : Reference)
    (wellFormed : memory.WellFormed)
    (carryRead : read memory carryHome 8 1 = .ok (numberBytes 0 8))
    (carryWrite : access memory carryHome 8 1 true = .ok ())
    (resultWrite : access memory resultHome 8 1 true = .ok ())
    (disjoint : WordsDisjoint carryHome resultHome)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, CarryPost a b 0 carryHome resultHome memory after →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarIndex (scalarFirstCarryCall + 1) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex scalarFirstCarryCall args frame
        [.reference (.address resultHome), .reference (.address carryHome), .scalar (.i64 b), .scalar (.i64 a)]
        memory = .ok (result, returned) ∧ post result returned := by
  have carryFormed := access_reference_valid _ _ _ _ _ carryWrite
  have resultFormed := access_reference_valid _ _ _ _ _ resultWrite
  apply run_carry_call a b 0 carryHome resultHome post (body := Extracted.addScalarBody)
    (op := .call Extracted.addWithCarryIndex 4)
  · simp only [cil_code]
  · conv in scalarFirstCarryCall => cbv
    simp only [cil_code]
  · simp [step, checkedValue, numericValue, formValue, carryFormed, resultFormed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl⟩
  · exact wellFormed
  · decide
  · exact carryRead
  · exact carryWrite
  · exact resultWrite
  · exact disjoint
  · exact continuation

#print axioms scalar_carry_prefix
#print axioms scalar_first_carry

end UInt256Proof.Safety
