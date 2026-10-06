import UInt256.Methods.Add.SmallCarryState

namespace UInt256Proof.Safety

open CIL.Safety UInt256Model.Safety

def smallIncrementStart : Nat → Nat
  | 0 => match Extracted.addScalarUInt64Body.code[smallCarryDecision]? with
      | some (.bltu target) => target
      | _ => 0
  | n + 1 => ((Extracted.addScalarUInt64Body.code.drop (smallIncrementStart n)).findSome? fun op =>
      match op with | .brzero target => some target | _ => none).getD 0

def smallIncrementDecision (segment : Nat) : Nat :=
  smallIncrementStart segment +
    (Extracted.addScalarUInt64Body.code.drop (smallIncrementStart segment)).findIdx fun op =>
      match op with | .brzero _ => true | _ => false

theorem small_increment_prefix (segment : Fin 3) (input output home : Reference) (word value : BitVec 64)
    (frame : Frame) (before after : CIL.Safety.Memory)
    (slot : frame.locals[segment.val + 1]? = some (.bytes .word64 home))
    (loaded : read before home 8 1 = .ok (numberBytes value.toNat 8))
    (stored : ∀ pc rest, step Extracted.addScalarUInt64Body (.setLocal (segment.val + 1)) pc
      (smallArguments input output word) frame (.scalar (.i64 (value + 1)) :: rest) before =
        .ok (.next (pc + 1) rest frame after))
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index (smallIncrementDecision segment.val)
        (smallArguments input output word) frame [.scalar (.i64 (value + 1))] after = .ok (result, returned) ∧
      post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index (smallIncrementStart segment.val)
        (smallArguments input output word) frame [] before = .ok (result, returned) ∧
      post result returned := by
  have reading := load_local_word64_of_read loaded
  obtain ⟨segment, bound⟩ := segment
  have cases : segment = 0 ∨ segment = 1 ∨ segment = 2 := by omega
  rcases cases with rfl | rfl | rfl
  all_goals
    conv in (smallIncrementStart _) => cbv
    conv at continuation in (smallIncrementDecision _) => cbv
    dsimp at slot stored
    repeat'
      first
      | exact continuation
      | simp (config := { failIfUnchanged := false })
        apply run_next_exists post
        · simp only [cil_code]; rfl
        · simp only [cil_code]; rfl
        · first
          | exact stored _ _
          | simp (config := { implicitDefEqProofs := false })
              [cil_code, step, slot, reading, checkedValue, numericValue, pureArity, scalars,
                CIL.step, CIL.binary, Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩

theorem SmallCarryState.increment {original current : CIL.Safety.Memory} {frame : Frame}
    {input output sumHome : Reference} {homes : Fin 4 → Reference}
    {words : Fin 4 → BitVec 64} {sum : BitVec 64}
    (state : SmallCarryState original current frame input output sumHome homes words sum)
    (call : CallingConditions Extracted.program original [input] [output])
    (segment : Fin 3) (word : BitVec 64)
    (post : CIL.Safety.Memory → List Value → Prop)
    (continuation : ∀ after,
      SmallCarryState original after frame input output sumHome homes
        (fun i => if i = (⟨segment.val + 1, by omega⟩ : Fin 4) then words i + 1 else words i) sum →
      ∃ fuel result returned,
        run Extracted.program fuel Extracted.addScalarUInt64Index (smallIncrementDecision segment.val)
          (smallArguments input output word) frame
          [.scalar (.i64 (words ⟨segment.val + 1, by omega⟩ + 1))] after = .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run Extracted.program fuel Extracted.addScalarUInt64Index (smallIncrementStart segment.val)
        (smallArguments input output word) frame [] current = .ok (result, returned) ∧ post result returned := by
  let index : Fin 4 := ⟨segment.val + 1, by omega⟩
  obtain ⟨after, updated, stored⟩ := state.store call index (words index + 1) word
  have shape : (fun i => if i = index then words index + 1 else words i) =
      (fun i => if i = index then words i + 1 else words i) := by
    funext i
    by_cases same : i = index
    · subst i; rfl
    · simp [same]
  rw [shape] at updated
  exact small_increment_prefix segment input output (homes index) word (words index) frame current after
    (state.slots index) (state.reads index) stored post (continuation after updated)

#print axioms small_increment_prefix
#print axioms SmallCarryState.increment

end UInt256Proof.Safety
