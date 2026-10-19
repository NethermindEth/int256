import UInt256.Methods.Add.SSEShapes.Incoming
import UInt256.Methods.AddSubtract.CascadeHelper

namespace UInt256Proof.Add.SSEShapes
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety UInt256Proof.Add.Safety CIL.Vector

/-- A private helper returning the lane-wise OR of its two vector arguments. -/
def mergeBody (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile := profile, returnsValue := true, locals := [], localKinds := [], parameterHomes := [], staticSites := [],
    code := [.arg 0, .arg 1, .intrinsic (.vector (.bor 128)) 2, .ret] }

/-- The merge helper returns `low ||| high` and leaves memory unchanged. -/
theorem merge_invoke (profile : CIL.FeatureProfile) (program : CIL.Program) (index : Nat)
    (found : program[index]? = some (mergeBody profile)) (memory : Memory) (low high : BitVec 128) :
    invoke program 4 index [.scalar (.v128 low), .scalar (.v128 high)] memory =
      .ok (memory, [.scalar (.v128 (low ||| high))]) := by
  simp only [invoke, found]
  change run program 4 index 0 [.scalar (.v128 low), .scalar (.v128 high)]
    ⟨memory.nextIdentity, [], [], []⟩ [] memory = _
  iterate 3
    apply Eq.trans
    · apply run_next found
      · rfl
      · rfl
  rw [run]
  simp only [found]
  rfl

/-- Combine both propagation masks inline or through the merge helper, then jump to the join. -/
def combineCode (merge : Option Nat) (join : Nat) : List CIL.Op :=
  [.local 12, .local 13,
    (match merge with
     | none => .intrinsic (.vector (.bor 128)) 2
     | some index => .call index 2),
    .branch join]

/-- Store the combined condition and branch to the fast suffix when no lane propagates. -/
def joinCode (fast : Nat) : List CIL.Op :=
  [.setLocal 14, .local 14, .intrinsic (.vector (.zero 128)) 0, .intrinsic (.vector (.equalsAll 128)) 2, .brnonzero fast]

/-- Compute `low ||| high` from the saved propagation masks and store it in its private home. -/
theorem combine_checked (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat)
    (leadingLength : leading.length = base) (merge : Option Nat) (join fast : Nat)
    (code : body.code = leading ++ combineCode merge join ++ tail)
    (joinLeading joinTail : List CIL.Op) (joinLength : joinLeading.length = join)
    (joinFound : body.code = joinLeading ++ joinCode fast ++ joinTail)
    (mergeFound : ∀ index, merge = some index → program[index]? = some (mergeBody body.profile))
    (specs : List NumericLocalSpec) (slotSpec : specs[13]? = some vector128ZeroSpec) (boundary : Nat) (entered current : Memory)
    (inputs outputs : List Reference) (frame : Frame) (root : LocalSlot) (slots : List LocalSlot)
    (layout : frame.locals = root :: slots) (args : List Value)
    (currentCall : CallingConditions program current inputs outputs)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered boundary specs slots)
    (authority : AccessBelow entered.nextIdentity entered current)
    (low high : BitVec 128) (lowHome highHome : Reference)
    (lowSlot : frame.locals[12]? = some (.bytes .vector128 lowHome))
    (highSlot : frame.locals[13]? = some (.bytes .vector128 highHome))
    (lowRead : read current lowHome 16 1 = .ok (numberBytes low.toNat 16))
    (highRead : read current highHome 16 1 = .ok (numberBytes high.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[14]? = some (.bytes .vector128 reference) →
      read after reference 16 1 = .ok (numberBytes (low ||| high).toNat 16) →
      MemoryBelow boundary current after →
      CallingConditions program after inputs outputs →
      AccessBelow entered.nextIdentity entered after →
      write current reference (numberBytes (low ||| high).toNat 16) 1 = .ok after →
      ∃ fuel result returned,
        run program fuel method (join + 1) args frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method base args frame [] current = .ok (result, returned) ∧ post result returned := by
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store program body specs boundary entered current inputs outputs frame root slots layout currentCall
      enteredWF homes authority 13 vector128ZeroSpec slotSpec
      (.v128 (low ||| high)) (low ||| high).toNat rfl
  have done := continuation reference after slot loaded retained afterCall afterAuthority written
  have loadLow := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 low) low.toNat rfl lowSlot lowRead
  have loadHigh := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 high) high.toNat rfl highSlot highRead
  have joined : ∃ fuel result returned,
      run program fuel method join args frame [.scalar (.v128 (low ||| high))] current =
        .ok (result, returned) ∧ post result returned := by
    apply run_next_exists post found
      (code_at_base (leading := joinLeading) (seg := joinCode fast) joinFound joinLength rfl) (stored _ _ _)
    exact done
  apply run_next_exists post found (by fetch_segment)
  · exact loadLow _ _
  normalize_pc
  apply run_next_exists post found (by fetch_segment)
  · exact loadHigh _ _
  normalize_pc
  cases merge with
  | none =>
    apply run_next_exists post found (by fetch_segment)
    · simp (config := { implicitDefEqProofs := false })
        [localResult, step, checkedIntrinsic, pureArity, scalars, CIL.step.eq_def, CIL.Intrinsic.available,
          CIL.Vector.intrinsic_or128, checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
      try exact ⟨rfl, rfl, rfl, rfl⟩
    normalize_pc
    apply run_next_exists post found (by fetch_segment)
    · simp (config := { implicitDefEqProofs := false })
        [step, pureArity, scalars, CIL.step.eq_def, checkedValue, numericValue,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      try exact ⟨rfl, rfl, rfl, rfl⟩
    exact joined
  | some index =>
    apply UInt256Proof.AddSubtract.run_pure_call_exists (rest := []) (arguments := [.scalar (.v128 low), .scalar (.v128 high)]) post found (by fetch_segment)
      (by simp [localResult, step, checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
          try exact ⟨⟨rfl, rfl⟩, rfl⟩)
      ⟨4, merge_invoke body.profile program index (mergeFound index rfl) current low high⟩
    normalize_pc
    apply run_next_exists post found (by fetch_segment)
    · simp (config := { implicitDefEqProofs := false })
        [step, pureArity, scalars, CIL.step.eq_def, checkedValue, numericValue,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      try exact ⟨rfl, rfl, rfl, rfl⟩
    exact joined

/-- Test the saved condition and expose both targets. -/
theorem join_branch (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (base : Nat)
    (leadingLength : leading.length = base) (fast : Nat)
    (code : body.code = leading ++ joinCode fast ++ tail) (memory : Memory) (frame : Frame) (args : List Value)
    (home : Reference) (condition : BitVec 128)
    (slot : frame.locals[14]? = some (.bytes .vector128 home))
    (loaded : read memory home 16 1 = .ok (numberBytes condition.toNat 16))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method (if condition = BitVec.ofNat 128 0 then fast else base + 5)
        args frame [] memory = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method (base + 1) args frame [] memory = .ok (result, returned) ∧ post result returned := by
  have load := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := body) (args := args) (pc := pc) (stack := stack)
    .vector128 (.v128 condition) condition.toNat rfl slot loaded
  by_cases zero : condition = BitVec.ofNat 128 0
  all_goals
    simp only [zero, ite_true, ite_false] at continuation
    iterate 4
      normalize_pc
      apply run_next_exists post found (by fetch_segment)
      first
      | exact load _ _
      | (simp (config := { implicitDefEqProofs := false })
           [CIL.truth, Option.bind, List.mapM, localResult, checkedIntrinsic, step, pureArity, scalars, CIL.step.eq_def, CIL.Intrinsic.available,
             CIL.Vector.intrinsic_zero128, CIL.Vector.intrinsic_equal_all128,
             show (0 : BitVec 128) = BitVec.ofNat 128 0 from rfl, zero,
             checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
         try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))
    simpa only [List.reverse_nil, Nat.add_assoc, Nat.reduceAdd] using continuation

#print axioms merge_invoke
#print axioms combine_checked
#print axioms join_branch
end UInt256Proof.Add.SSEShapes
