import UInt256.Methods.Add.ScalarCarryPrefix
import UInt256.Safety.LimbAccess

namespace UInt256Proof.Safety

open CIL.Safety

/-- Discover successive calls to the proved carry helper in extracted order. -/
def scalarCarryCall : Nat → Nat
  | 0 => scalarFirstCarryCall
  | n + 1 =>
    let start := scalarCarryCall n + 1
    start + (Extracted.addScalarBody.code.drop start).findIdx (fun op => match op with
      | .call callee _ => callee == Extracted.addWithCarryIndex
      | _ => false)

/-- Each remaining limb follows its actual load/load/address/address sequence
    between discovered calls. The indexed statement covers all three segments. -/
theorem scalar_carry_segment (segment : Fin 3) (left right output : Reference) (extra : List Value)
    (frame : Frame) (memory : Memory) (a b : BitVec 64) (carryHome resultHome : Reference)
    (leftFormed : form memory left = .ok left) (rightFormed : form memory right = .ok right)
    (leftRead : ∀ rest, instruction (.field ⟨segment.val + 1, by omega⟩)
      (.reference (.address left) :: rest) memory = .ok (memory, .scalar (.i64 a) :: rest))
    (rightRead : ∀ rest, instruction (.field ⟨segment.val + 1, by omega⟩)
      (.reference (.address right) :: rest) memory = .ok (memory, .scalar (.i64 b) :: rest))
    (carrySlot : frame.locals[2]? = some (.bytes .word64 carryHome))
    (resultSlot : frame.locals[segment.val + 4]? = some (.bytes .word64 resultHome))
    (carryFormed : form memory carryHome = .ok carryHome)
    (resultFormed : form memory resultHome = .ok resultHome)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall (segment.val + 1))
        ([.reference (.address left), .reference (.address right), .reference (.address output)] ++ extra)
        frame [.reference (.address resultHome), .reference (.address carryHome), .scalar (.i64 b), .scalar (.i64 a)]
        memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall segment.val + 1)
        ([.reference (.address left), .reference (.address right), .reference (.address output)] ++ extra)
        frame [] memory = .ok (result, returned) ∧ post result returned := by
  obtain ⟨segment, bound⟩ := segment
  have cases : segment = 0 ∨ segment = 1 ∨ segment = 2 := by omega
  rcases cases with rfl | rfl | rfl
  all_goals
    dsimp at leftRead rightRead resultSlot
    conv in (scalarCarryCall _) => cbv
    repeat'
      first
      | exact continuation
      | simp (config := { failIfUnchanged := false })
        apply run_next_exists post
        · simp only [cil_code]; rfl
        · simp only [cil_code]; rfl
        · simp (config := { implicitDefEqProofs := false })
            [cil_code, step, checkedValue, formValue, leftFormed, rightFormed,
              carryFormed, resultFormed, carrySlot, resultSlot, localAddress, leftRead, rightRead,
              pureArity, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩

#print axioms scalar_carry_segment

/-- Every discovered scalar carry call uses the checked arithmetic contract. -/
theorem scalar_indexed_carry (index : Fin 4) (args : List Value) (frame : Frame) (memory : Memory)
    (a b c : BitVec 64) (carryHome resultHome : Reference)
    (wellFormed : memory.WellFormed) (incoming : c.toNat ≤ 1)
    (carryRead : read memory carryHome 8 1 = .ok (numberBytes c.toNat 8))
    (carryWrite : access memory carryHome 8 1 true = .ok ())
    (resultWrite : access memory resultHome 8 1 true = .ok ())
    (disjoint : WordsDisjoint carryHome resultHome)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, CarryPost a b c carryHome resultHome memory after →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall index.val + 1) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall index.val) args frame
        [.reference (.address resultHome), .reference (.address carryHome), .scalar (.i64 b), .scalar (.i64 a)]
        memory = .ok (result, returned) ∧ post result returned := by
  have carryFormed := access_reference_valid _ _ _ _ _ carryWrite
  have resultFormed := access_reference_valid _ _ _ _ _ resultWrite
  apply run_carry_call a b c carryHome resultHome post (body := Extracted.addScalarBody)
    (op := .call Extracted.addWithCarryIndex 4)
  · simp only [cil_code]
  · obtain ⟨index, bound⟩ := index
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    all_goals
      conv in (scalarCarryCall _) => cbv
      simp only [cil_code]
  · simp [step, checkedValue, numericValue, formValue, carryFormed, resultFormed,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl⟩
  · exact wellFormed
  · exact incoming
  · exact carryRead
  · exact carryWrite
  · exact resultWrite
  · exact disjoint
  · exact continuation

#print axioms scalar_indexed_carry

open UInt256Model.Safety

/-- Valid caller views discharge both field loads for each remaining limb;
    checked home accesses discharge address formation and the mathematical call. -/
theorem scalar_carry_segment_checked (segment : Fin 3) (left right output : Reference) (extra : List Value)
    (frame : Frame) (memory : CIL.Safety.Memory) (c : BitVec 64) (carryHome resultHome : Reference)
    (call : CallingConditions Extracted.program memory [left, right] [output])
    (carrySlot : frame.locals[2]? = some (.bytes .word64 carryHome))
    (resultSlot : frame.locals[segment.val + 4]? = some (.bytes .word64 resultHome))
    (incoming : c.toNat ≤ 1)
    (carryRead : read memory carryHome 8 1 = .ok (numberBytes c.toNat 8))
    (carryWrite : access memory carryHome 8 1 true = .ok ())
    (resultWrite : access memory resultHome 8 1 true = .ok ())
    (disjoint : WordsDisjoint carryHome resultHome)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ after,
      CarryPost (inputLimb memory left ⟨segment.val + 1, by omega⟩)
        (inputLimb memory right ⟨segment.val + 1, by omega⟩) c carryHome resultHome memory after →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall (segment.val + 1) + 1)
          (binaryArguments left right output ++ extra) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall segment.val + 1)
        (binaryArguments left right output ++ extra) frame [] memory = .ok (result, returned) ∧ post result returned := by
  apply scalar_carry_segment segment left right output extra frame memory _ _ carryHome resultHome
    (call.input_formed (by simp)) (call.input_formed (by simp))
    (fun rest => call.input_field_instruction (by simp) _ rest)
    (fun rest => call.input_field_instruction (by simp) _ rest) carrySlot resultSlot
    (access_reference_valid _ _ _ _ _ carryWrite) (access_reference_valid _ _ _ _ _ resultWrite) post
  exact scalar_indexed_carry ⟨segment.val + 1, by omega⟩ (binaryArguments left right output ++ extra)
    frame memory _ _ c carryHome resultHome call.1.1 incoming carryRead carryWrite resultWrite disjoint post continuation

#print axioms scalar_carry_segment_checked

end UInt256Proof.Safety
