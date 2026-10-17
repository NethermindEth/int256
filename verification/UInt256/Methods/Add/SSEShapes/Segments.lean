import UInt256.Methods.Add.Vector128Propagation

namespace UInt256Proof.Add.SSEShapes
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety CIL.Vector

/-- Fetch from a segment placed after a prefix of known length. -/
theorem code_at {body : CIL.Method} {leading seg tail : List CIL.Op} {base : Nat}
    (code : body.code = leading ++ seg ++ tail) (leadingLength : leading.length = base) {k : Nat} {op : CIL.Op}
    (fetched : seg[k]? = some op) : body.code[base + k]? = some op := by
  have bound : k < seg.length := by
    rcases Nat.lt_or_ge k seg.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at fetched; contradiction
  rw [code, List.append_assoc, List.getElem?_append_right (by omega), leadingLength, Nat.add_sub_cancel_left,
    List.getElem?_append_left bound]
  exact fetched

/-- Fetch the first instruction of a segment. -/
theorem code_at_base {body : CIL.Method} {leading seg tail : List CIL.Op} {base : Nat}
    (code : body.code = leading ++ seg ++ tail) (leadingLength : leading.length = base) {op : CIL.Op}
    (fetched : seg[0]? = some op) : body.code[base]? = some op :=
  code_at (k := 0) code leadingLength fetched

set_option hygiene false in
/-- Normalize the program counter and fetch from the segment named `code` placed at `leadingLength`. -/
macro "fetch_segment" : tactic =>
  `(tactic| first | exact code_at_base code leadingLength rfl | exact code_at code leadingLength rfl)

set_option hygiene false in
/-- Normalize nested program-counter offsets to `base + k`. -/
macro "normalize_pc" : tactic =>
  `(tactic| simp (config := { failIfUnchanged := false }) only [Nat.add_assoc, Nat.reduceAdd])

/-- An ARM feature test that SSE skips, either once or as `feature & feature`. -/
def guardCode (doubled : Bool) (target : Nat) : List CIL.Op :=
  if doubled then [.feature .advSimd, .feature .advSimd, .band, .brzero target]
  else [.feature .advSimd, .brzero target]

/-- With AdvSimd disabled the guard jumps to its target without touching stack or memory. -/
theorem guard_skip (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat)
    (leadingLength : leading.length = base) (doubled : Bool) (target : Nat)
    (code : body.code = leading ++ guardCode doubled target ++ tail)
    (disabled : body.profile.advSimd = false) (args stack : List Value) (frame : Frame) (memory : Memory)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method target args frame stack memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method base args frame stack memory = .ok (result, returned) ∧ post result returned := by
  cases doubled
  all_goals repeat' first
    | exact continuation
    | (simp (config := { failIfUnchanged := false }) only [Nat.add_assoc, Nat.reduceAdd]
       apply run_next_exists post found (by first | exact code_at_base code leadingLength rfl | exact code_at code leadingLength rfl)
       simp (config := { implicitDefEqProofs := false })
         [step, disabled, pureArity, scalars, CIL.step.eq_def, CIL.FeatureProfile.evaluate, CIL.binary,
           checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
       first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

/-- `SkipInit` on the output followed by the ARM early-store guard. -/
def earlyCode (doubled : Bool) (target : Nat) : List CIL.Op :=
  [.arg 2, .skipInit] ++ guardCode doubled target

/-- SSE checks the output reference and skips the ARM early stores. -/
theorem early_skip (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat)
    (leadingLength : leading.length = base) (doubled : Bool) (target : Nat)
    (code : body.code = leading ++ earlyCode doubled target ++ tail)
    (disabled : body.profile.advSimd = false) (memory : Memory) (output : Reference)
    (frame : Frame) (args : List Value)
    (argument : args[2]? = some (.reference (.address output)))
    (formed : form memory output = .ok output)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method target args frame [] memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method base args frame [] memory = .ok (result, returned) ∧ post result returned := by
  have guard : body.code = (leading ++ [.arg 2, .skipInit]) ++ guardCode doubled target ++ tail := by
    rw [code, earlyCode]; simp only [List.append_assoc]
  have skipped := guard_skip program body method found _ tail (base + 1 + 1) (by simp [leadingLength]) doubled target guard
    disabled args [] frame memory post continuation
  cases doubled
  all_goals
    iterate 2
      simp (config := { failIfUnchanged := false }) only [Nat.add_assoc, Nat.reduceAdd]
      apply run_next_exists post found (by first | exact code_at_base code leadingLength rfl | exact code_at code leadingLength rfl)
      · simp (config := { implicitDefEqProofs := false })
          [step, argument, checkedValue, formValue, formed, instruction, pureArity, scalars, CIL.step.eq_def,
            numericValue, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
        try exact ⟨rfl, rfl, rfl, rfl⟩
    simpa only [Nat.add_assoc, Nat.reduceAdd] using skipped

#print axioms guard_skip
#print axioms early_skip
end UInt256Proof.Add.SSEShapes
