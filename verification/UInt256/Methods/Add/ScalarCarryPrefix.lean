import UInt256.Methods.Add.ScalarPrefix
import UInt256.Methods.Add.CarryContract
import UInt256.Safety.LimbAccess

set_option maxRecDepth 4096

namespace UInt256Proof.Safety

open CIL.Safety UInt256Proof.Add.CarrySafety

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
  have found : Extracted.program[Extracted.addScalarIndex]? = some Extracted.addScalarBody := by
    simp only [cil_code]
  cil_contract_steps [found, largeLeft, carryFormed, resultFormed, leftSlot, rightSlot,
    carrySlot, resultSlot, leftLoaded, rightLoaded, stored, BitVec.ofNat_eq_ofNat] until continuation


end UInt256Proof.Safety

namespace UInt256Proof.Safety

open CIL.Safety UInt256Proof.Add.CarrySafety

/-- Discover successive calls to the proved carry helper in extracted order. -/
def scalarCarryCall : Nat → Nat
  | 0 => scalarFirstCarryCall
  | n + 1 =>
    let start := scalarCarryCall n + 1
    start + (Extracted.addScalarBody.code.drop start).findIdx (fun op => match op with
      | .call callee _ => callee == Extracted.addWithCarryIndex
      | _ => false)

/-- Every discovered scalar carry call uses the checked arithmetic contract. -/
theorem scalar_indexed_carry (contract : CarryHelperContract Extracted.program Extracted.addWithCarryIndex) (index : Fin 4) (args : List Value) (frame : Frame) (memory : Memory)
    (a b c : BitVec 64) (carryHome resultHome : Reference)
    (wellFormed : memory.WellFormed) (incoming : c.toNat ≤ 1)
    (carryRead : read memory carryHome 8 1 = .ok (numberBytes c.toNat 8))
    (carryWrite : access memory carryHome 8 1 true = .ok ())
    (resultWrite : access memory resultHome 8 1 true = .ok ())
    (disjoint : WordsDisjoint carryHome resultHome)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, after.WellFormed →
      (StaticWorldPreserved Extracted.program memory after) →
      Confined [(carryHome, 8), (resultHome, 8)] memory after →
      CarryPost a b c carryHome resultHome after →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall index.val + 1) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall index.val) args frame
        [.reference (.address resultHome), .reference (.address carryHome), .scalar (.i64 b), .scalar (.i64 a)]
        memory = .ok (result, returned) ∧ post result returned := by
  have carryFormed := access_reference_valid _ _ _ _ _ carryWrite
  have resultFormed := access_reference_valid _ _ _ _ _ resultWrite
  apply run_call_of_contract_formed contract ⟨a, b, c, carryHome, resultHome⟩ (body := Extracted.addScalarBody)
    (op := .call Extracted.addWithCarryIndex 4) (encoded := rfl) (formed := wellFormed)
  · simp only [cil_code]
  · obtain ⟨index, bound⟩ := index
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    all_goals
      conv in (scalarCarryCall _) => cbv
      simp only [cil_code]
  · cil_checked_step [carryFormed, resultFormed]
  · exact ⟨wellFormed, incoming, carryRead, carryWrite, resultWrite, disjoint⟩
  · intro after output call invariants
    simpa only [carryContract, List.append_nil] using
      continuation after invariants.formed invariants.staticWorld call.framed call.post


open UInt256Model.Safety

/-- Valid caller views discharge both field loads for each remaining limb;
    checked home accesses discharge address formation and the mathematical call. -/
theorem scalar_carry_segment_checked (contract : CarryHelperContract Extracted.program Extracted.addWithCarryIndex) (segment : Fin 3) (left right output : Reference) (extra : List Value)
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
    (continuation : ∀ after, after.WellFormed →
      (StaticWorldPreserved Extracted.program memory after) →
      Confined [(carryHome, 8), (resultHome, 8)] memory after →
      CarryPost (inputLimb memory left ⟨segment.val + 1, by omega⟩)
        (inputLimb memory right ⟨segment.val + 1, by omega⟩) c carryHome resultHome after →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall (segment.val + 1) + 1)
          (binaryArguments left right output ++ extra) frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex (scalarCarryCall segment.val + 1)
        (binaryArguments left right output ++ extra) frame [] memory = .ok (result, returned) ∧ post result returned := by
  have leftFormed := call.input_formed (reference := left) (by simp)
  have rightFormed := call.input_formed (reference := right) (by simp)
  have leftRead := fun rest => call.input_field_instruction (reference := left) (by simp)
    ⟨segment.val + 1, by omega⟩ rest
  have rightRead := fun rest => call.input_field_instruction (reference := right) (by simp)
    ⟨segment.val + 1, by omega⟩ rest
  have carryFormed := access_reference_valid _ _ _ _ _ carryWrite
  have resultFormed := access_reference_valid _ _ _ _ _ resultWrite
  have suffix := scalar_indexed_carry contract ⟨segment.val + 1, by omega⟩
    (binaryArguments left right output ++ extra) frame memory
    (inputLimb memory left ⟨segment.val + 1, by omega⟩)
    (inputLimb memory right ⟨segment.val + 1, by omega⟩) c carryHome resultHome call.1.1
    incoming carryRead carryWrite resultWrite disjoint post continuation
  have found : Extracted.program[Extracted.addScalarIndex]? = some Extracted.addScalarBody := by
    simp only [cil_code]
  obtain ⟨segment, bound⟩ := segment
  have cases : segment = 0 ∨ segment = 1 ∨ segment = 2 := by omega
  rcases cases with rfl | rfl | rfl
  all_goals
    dsimp at leftRead rightRead resultSlot suffix
    conv in (scalarCarryCall _) => cbv
    cil_contract_steps [found, binaryArguments, leftFormed, rightFormed, carryFormed,
      resultFormed, carrySlot, resultSlot, leftRead, rightRead] until suffix

end UInt256Proof.Safety
