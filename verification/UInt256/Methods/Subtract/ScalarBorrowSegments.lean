import UInt256.Methods.Subtract.BorrowContract
import UInt256.Methods.Subtract.ScalarSafetySetup

/-! The borrow-helper call sites of the extracted scalar body and their checked contract call. -/

namespace UInt256Proof.Subtract.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Subtract.Profile

def scalarBorrowCalls : List Nat := scalarBody.code.zipIdx.filterMap fun (op, pc) =>
  match op with
  | .call callee _ => if callee == Extracted.subtractWithBorrowIndex then some pc else none
  | _ => none

def scalarBorrowCall (index : Nat) : Nat := scalarBorrowCalls[index]?.getD 0

theorem scalar_indexed_borrow (contract : BorrowHelperContract Extracted.program Extracted.subtractWithBorrowIndex) (index : Fin 4) (args : List Value) (frame : Frame) (memory : Memory)
    (a b c : BitVec 64) (borrowHome resultHome : Reference)
    (wellFormed : memory.WellFormed) (incoming : c.toNat ≤ 1)
    (borrowRead : read memory borrowHome 8 1 = .ok (numberBytes c.toNat 8))
    (borrowWrite : access memory borrowHome 8 1 true = .ok ())
    (resultWrite : access memory resultHome 8 1 true = .ok ()) (disjoint : WordsDisjoint borrowHome resultHome)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, after.WellFormed →
      (StaticWorldPreserved Extracted.program memory after) →
      Confined [(borrowHome, 8), (resultHome, 8)] memory after →
      BorrowPost a b c borrowHome resultHome after →
      ∃ fuel result returned,
        run Extracted.program fuel scalarIndex (scalarBorrowCall index.val + 1) args frame [] after =
          .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel scalarIndex (scalarBorrowCall index.val) args frame
        [.reference (.address resultHome), .reference (.address borrowHome), .scalar (.i64 b), .scalar (.i64 a)]
        memory = .ok (result, returned) ∧ post result returned := by
  have fb := access_reference_valid _ _ _ _ _ borrowWrite
  have fr := access_reference_valid _ _ _ _ _ resultWrite
  apply run_call_of_contract_formed contract ⟨a, b, c, borrowHome, resultHome⟩ (body := scalarBody)
    (op := .call Extracted.subtractWithBorrowIndex 4) (encoded := rfl) (formed := wellFormed)
  · rfl
  · obtain ⟨index, bound⟩ := index
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> rfl
  · cil_checked_step [fb, fr]
  · exact ⟨wellFormed, incoming, borrowRead, borrowWrite, resultWrite, disjoint⟩
  · intro after output call invariants
    simpa only [borrowContract, List.append_nil] using
      continuation after invariants.formed invariants.staticWorld call.framed call.post

end UInt256Proof.Subtract.Safety
