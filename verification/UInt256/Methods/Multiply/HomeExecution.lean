import UInt256.Methods.Multiply.DispatchCalls
import UInt256.Methods.Equality.Aggregate
open Lean Meta Elab Command Tactic CIL UInt256Model UInt256Proof UInt256Proof.Bitwise
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof.Multiply

@[irreducible] def productVector (a b : Limbs) : CIL.Vector.V256 :=
  CIL.Vector.pack256 (productLimbs a b 0) (productLimbs a b 1)
    (productLimbs a b 2) (productLimbs a b 3)

theorem home_four_numbers (memory : Memory) (frame kind index : Nat) (a b c d : Nat) :
    readAggregate (writeHomeBytes (writeHomeBytes (writeHomeBytes (writeHomeBytes memory
      frame kind index 0 a 8) frame kind index 8 b 8)
      frame kind index 16 c 8) frame kind index 24 d 8) frame kind index =
      some (.v256 (CIL.Vector.pack256 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b)
        (BitVec.ofNat 64 c) (BitVec.ofNat 64 d))) := by
  simpa only [BitVec.toNat_ofNat, show 2^64 = (256 : Nat)^8 from rfl,
    Equality.writeHomeBytes_mod, four_value_pack] using
      aggregate_fourWrites memory frame kind index
        (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) (BitVec.ofNat 64 c) (BitVec.ofNat 64 d)

theorem word_cast_mod (n : Nat) : BitVec.ofNat 64 (n % 18446744073709551616) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, show 2^64 = 18446744073709551616 from rfl, Nat.mod_mod]

elab "multiply_home_limb_summaries" : command => do
  let indices ← liftTermElabM do listTerms (mkConst `Extracted.limbProductCandidates)
  for expression in indices do
    let .lit (.natVal index) ← liftTermElabM (whnf expression) | throwError "Expected concrete candidate"
    for suffix in ["", "LeftTwo_", "BothTwo_"] do
      let existing := `UInt256Proof.Multiply |>.str s!"execute_limbs_{suffix}{index}"
      unless (← getEnv).contains existing do continue
      let number := Syntax.mkNumLit (toString index)
      let name := mkIdent (Name.mkSimple s!"execute_home_limbs_{suffix}{index}")
      let candidates := mkIdent `Extracted.limbProductCandidates
      let upperA ← if suffix == "" then `(term| True) else `(term| a 2 = 0 ∧ a 3 = 0)
      let upperB ← if suffix == "BothTwo_" then `(term| b 2 = 0 ∧ b 3 = 0) else `(term| True)
      let mut zeroFacts : Array (TSyntax `term) := #[(← `(term| True.intro))]
      if suffix != "" then
        zeroFacts := zeroFacts.push (← `(term| upperA.1)) |>.push (← `(term| upperA.2))
      if suffix == "BothTwo_" then
        zeroFacts := zeroFacts.push (← `(term| upperB.1)) |>.push (← `(term| upperB.2))
      elabCommand (← `(command| if_extracted $candidates {
        theorem $name (memory : Memory) (left right frame fuel outFrame outKind outIndex : Nat)
            (a b : Limbs) (upperA : $upperA) (upperB : $upperB)
            (leftReads : ∀ i : Fin 4, read64 memory (.byte (left + 8*i.val)) = some (.i64 (a i)))
            (rightReads : ∀ i : Fin 4, read64 memory (.byte (right + 8*i.val)) = some (.i64 (b i))) :
            ∃ final, run Extracted.program (fuel + executionBound Extracted.program $number) $number 0
                [.object left, .object right, .ref (.home outFrame outKind outIndex 0)] frame [] memory =
                  some (final, []) ∧
              readAggregate final outFrame outKind outIndex = some (.v256 (productVector a b)) ∧
              ∀ address, final (.byte address) = memory (.byte address) := by
          obtain ⟨l0, l1, l2, l3⟩ := limb_reads memory left a leftReads
          obtain ⟨r0, r1, r2, r3⟩ := limb_reads memory right b rightReads
          have vl := read256_of_limbs memory left (a 0) (a 1) (a 2) (a 3) l0 l1 l2 l3
          have vr := read256_of_limbs memory right (b 0) (b 1) (b 2) (b 3) r0 r1 r2 r3
          cil_execute_core l0, l1, l2, l3, r0, r1, r2, r3, vl, vr, evalMemory, write256, unsafeAsRef, unsafeAdd,
            digitLow_shift32, narrow_low_correct, narrow_low_split, narrow_low_tail,
            aggregate_fourWrites, readAggregate_fullWrite with
            (first | cil_wide_product_call | cil_count_carry_call)
          all_goals simp (config := { implicitDefEqProofs := false, failIfUnchanged := false }) only [home_four_numbers, four_value_pack, word_cast_mod,
            BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          all_goals unfold productVector
          all_goals simp (config := { implicitDefEqProofs := false, failIfUnchanged := false }) only [productLimbs, Fin.val_zero, Fin.val_one, Fin.val_two,
            show (3 : Fin 4).val = 3 from rfl, Nat.reduceEqDiff, ↓reduceIte,
            firstColumn, secondColumn, topWords, column, List.foldl_cons, List.foldl_nil,
            columnStep, List.sum_cons, List.sum_nil, BitVec.add_zero, BitVec.add_assoc]
          all_goals simp (config := { implicitDefEqProofs := false, failIfUnchanged := false }) only [$[$zeroFacts:term],*, show (0 : W64) = BitVec.ofNat 64 0 from rfl, lowProduct_zero_left, lowProduct_zero_right, highProduct_zero_left, highProduct_zero_right, BitVec.add_zero, BitVec.zero_add, countCarry, sumHigh_zero_left, sumHigh_zero_right]
          all_goals simp (config := { implicitDefEqProofs := false, failIfUnchanged := false }) only [BitVec.add_assoc, BitVec.add_zero, BitVec.zero_add]
          all_goals try rfl
          all_goals simp (config := { implicitDefEqProofs := false, failIfUnchanged := false }) only [CIL.Vector.pack256, lowProduct, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_zero, show (2 : Nat)^64 = 18446744073709551616 from rfl, Nat.add_mod, Nat.mod_mod, Nat.add_assoc, Nat.add_zero, Nat.zero_mod, Nat.mul_zero, Nat.zero_mul, Nat.zero_add]
          all_goals simp (config := { implicitDefEqProofs := false, failIfUnchanged := false }) only [Nat.mod_mod]
      }))

multiply_home_limb_summaries
end UInt256Proof.Multiply
