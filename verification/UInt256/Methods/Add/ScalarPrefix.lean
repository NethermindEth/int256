import UInt256.Methods.Add.Bindings
import CIL.Safety.StepComposition
import CIL.Safety.WordLocals
import CIL.Safety.GuardNormalization

namespace UInt256Proof.Safety

open CIL.Safety

/-- Discover the first reachable small-operand decision from extracted CIL. -/
def scalarFirstDecision : Nat :=
  Extracted.addScalarBody.code.findIdx fun op => match op with
    | .brnonzero _ => true
    | _ => false

/-- The scalar dispatch and right-operand prefix execute actual fetched steps.
    Memory premises are checked operations, discharged by caller access and
    local-store preservation; the continuation must still prove either branch. -/
theorem scalar_right_prefix (left right output : Reference) (extra : List Value)
    (words : Fin 4 → BitVec 64) (frame : Frame) (before after : Memory)
    (rightBefore : form before right = .ok right)
    (rightAfter : form after right = .ok right)
    (firstRead : ∀ rest, instruction (.fieldAt 0 8) (.reference (.address right) :: rest) before =
      .ok (before, .scalar (.i64 (words 0)) :: rest))
    (upperReads : ∀ (index : Fin 4) rest,
      instruction (.fieldAt (8 * index.val) 8) (.reference (.address right) :: rest) after =
        .ok (after, .scalar (.i64 (words index)) :: rest))
    (stored : ∀ pc rest, step Extracted.addScalarBody (.setLocal 0) pc
      ([.reference (.address left), .reference (.address right), .reference (.address output)] ++ extra)
      frame (.scalar (.i64 (words 0)) :: rest) before =
        .ok (.next (pc + 1) rest frame after))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex scalarFirstDecision
        ([.reference (.address left), .reference (.address right), .reference (.address output)] ++ extra)
        frame [.scalar (.i64 (words 1 ||| words 2 ||| words 3))] after = .ok (result, returned) ∧
      post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex 0
        ([.reference (.address left), .reference (.address right), .reference (.address output)] ++ extra)
        frame [] before = .ok (result, returned) ∧ post result returned := by
  have upper1 := upperReads 1
  have upper2 := upperReads 2
  have upper3 := upperReads 3
  simp only [Fin.val_one, Fin.val_two, CIL.fin_val_three, Nat.reduceMul] at upper1 upper2 upper3
  simp [scalarFirstDecision, cil_code] at continuation
  repeat'
    first
    | exact continuation
    | simp (config := { failIfUnchanged := false }) [BitVec.ofNat_eq_ofNat]
      apply run_next_exists post
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · first
        | ((with_reducible show step _ (.setLocal 0) _ _ _ _ _ = _); exact stored _ _)
        | simp (config := { implicitDefEqProofs := false })
            [cil_code, step, cil_guard, observerCount, checkedValue, numericValue, formValue, rightBefore, rightAfter,
              pureArity, scalars, CIL.step.eq_def, CIL.binary, CIL.unary, CIL.FeatureProfile.evaluate, firstRead, upper1, upper2, upper3,
              checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩

#print axioms scalar_right_prefix

end UInt256Proof.Safety

namespace UInt256Proof.Safety

open CIL.Safety

/-- The second small-operand decision is discovered after the first one. -/
def scalarSecondDecision : Nat :=
  scalarFirstDecision + 1 +
    (Extracted.addScalarBody.code.drop (scalarFirstDecision + 1)).findIdx (fun op =>
      match op with | .brnonzero _ => true | _ => false)

/-- Checked execution of the non-small-right branch through the left-operand
    prefix. Memory premises and the next continuation are separate obligations. -/
theorem scalar_left_prefix (left right output : Reference) (extra : List Value)
    (rightUpper : BitVec 64) (largeRight : rightUpper ≠ BitVec.ofNat 64 0)
    (words : Fin 4 → BitVec 64) (frame : Frame) (before after : Memory)
    (leftBefore : form before left = .ok left)
    (leftAfter : form after left = .ok left)
    (firstRead : ∀ rest, instruction (.fieldAt 0 8) (.reference (.address left) :: rest) before =
      .ok (before, .scalar (.i64 (words 0)) :: rest))
    (upperReads : ∀ (index : Fin 4) rest,
      instruction (.fieldAt (8 * index.val) 8) (.reference (.address left) :: rest) after =
        .ok (after, .scalar (.i64 (words index)) :: rest))
    (stored : ∀ pc rest, step Extracted.addScalarBody (.setLocal 1) pc
      ([.reference (.address left), .reference (.address right), .reference (.address output)] ++ extra)
      frame (.scalar (.i64 (words 0)) :: rest) before =
        .ok (.next (pc + 1) rest frame after))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex scalarSecondDecision
        ([.reference (.address left), .reference (.address right), .reference (.address output)] ++ extra)
        frame [.scalar (.i64 (words 1 ||| words 2 ||| words 3))] after = .ok (result, returned) ∧
      post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarIndex scalarFirstDecision
        ([.reference (.address left), .reference (.address right), .reference (.address output)] ++ extra)
        frame [.scalar (.i64 rightUpper)] before = .ok (result, returned) ∧ post result returned := by
  have upper1 := upperReads 1
  have upper2 := upperReads 2
  have upper3 := upperReads 3
  simp only [Fin.val_one, Fin.val_two, CIL.fin_val_three, Nat.reduceMul] at upper1 upper2 upper3
  simp [scalarSecondDecision, scalarFirstDecision, cil_code] at continuation
  conv in scalarFirstDecision => cbv
  repeat'
    first
    | exact continuation
    | simp (config := { failIfUnchanged := false }) [BitVec.ofNat_eq_ofNat, largeRight]
      apply run_next_exists post
      · simp only [cil_code]; rfl
      · simp only [cil_code]; rfl
      · first
        | ((with_reducible show step _ (.setLocal 1) _ _ _ _ _ = _); exact stored _ _)
        | simp (config := { implicitDefEqProofs := false })
            [cil_code, step, cil_guard, observerCount, checkedValue, numericValue, formValue, leftBefore, leftAfter,
              pureArity, scalars, CIL.step.eq_def, CIL.binary, CIL.unary, firstRead, upper1, upper2, upper3,
              checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩

#print axioms scalar_left_prefix

end UInt256Proof.Safety
