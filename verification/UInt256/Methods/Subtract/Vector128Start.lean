import UInt256.Methods.AddSubtract.Vector128Inputs

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector

def subtractStartCode : List CIL.Op := [
  .local 1, .local 3, .intrinsic (.vector (.sub64 128)) 2, .setLocal 5,
  .local 2, .local 4, .intrinsic (.vector (.sub64 128)) 2, .setLocal 6,
  .local 1, .local 3, .intrinsic (.vector (.ltu64 128)) 2, .setLocal 7,
  .local 2, .local 4, .intrinsic (.vector (.ltu64 128)) 2, .setLocal 8]

def subtractIncomingCode (adv : Bool) : List CIL.Op := if adv then [
  .feature .advSimd, .brzero 51,
  .intrinsic (.vector (.zero 128)) 0, .local 7, .const32 1, .intrinsic (.advSimd .extract64) 3, .setLocal 9,
  .local 7, .local 8, .const32 1, .intrinsic (.advSimd .extract64) 3, .setLocal 10,
  .branch 63,
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile"
] else [
  .feature .advSimd, .brzero 51,
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile", .unsupported "Unreachable under selected profile",
  .unsupported "Unreachable under selected profile",
  .local 7, .const32 8, .intrinsic (.sse .shiftLeftBytes) 2, .setLocal 9,
  .local 8, .intrinsic (.vector (.reinterpret 128)) 1, .local 7, .intrinsic (.vector (.reinterpret 128)) 1,
  .const32 8, .intrinsic (.sse .alignBytes) 3, .intrinsic (.vector (.reinterpret 128)) 1, .setLocal 10]

def subtractDecisionCode : List CIL.Op := [
  .local 5, .intrinsic (.vector (.zero 128)) 0, .intrinsic (.vector (.eq64 128)) 2,
  .local 9, .intrinsic (.vector (.band 128)) 2,
  .local 6, .intrinsic (.vector (.zero 128)) 0, .intrinsic (.vector (.eq64 128)) 2,
  .local 10, .intrinsic (.vector (.band 128)) 2,
  .intrinsic (.vector (.bor 128)) 2,
  .intrinsic (.vector (.zero 128)) 0, .intrinsic (.vector (.equalsAll 128)) 2,
  .brnonzero 119]

theorem subtract_incoming_length (adv : Bool) : (subtractIncomingCode adv).length = 25 := by
  cases adv <;> rfl

def subtractMask (a b : BitVec 128) : BitVec 128 := zip128 (fun x y => mask64 (x.ult y)) a b

/-- Initial halves, lane differences, borrow masks and the two incoming-borrow vectors. -/
def subtractSnapshot (values : Fin 4 → BitVec 128) (i : Fin 10) : BitVec 128 :=
  if h : i.val < 4 then values ⟨i.val, h⟩
  else if i.val = 4 then zip128 (· - ·) (values 0) (values 2)
  else if i.val = 5 then zip128 (· - ·) (values 1) (values 3)
  else if i.val = 6 then subtractMask (values 0) (values 2)
  else if i.val = 7 then subtractMask (values 1) (values 3)
  else if i.val = 8 then incoming128Low (subtractMask (values 0) (values 2))
  else incoming128High (subtractMask (values 0) (values 2)) (subtractMask (values 1) (values 3))

def subtractPropagation (values : Fin 4 → BitVec 128) : BitVec 128 :=
  (zip128 (fun x y => mask64 (x == y)) (subtractSnapshot values 4) 0 &&& subtractSnapshot values 8) |||
    (zip128 (fun x y => mask64 (x == y)) (subtractSnapshot values 5) 0 &&& subtractSnapshot values 9)

abbrev SubtractSnapshots (memory : Memory) (slots : List LocalSlot) (values : Fin 4 → BitVec 128) (done : Nat) : Prop :=
  ∀ i : Fin 10, i.val < done → ∃ reference,
    slots[i.val]? = some (.bytes .vector128 reference) ∧
    read memory reference 16 1 = .ok (numberBytes (subtractSnapshot values i).toNat 16)

structure SubtractVectorState (program : CIL.Program) (original entered current : Memory)
    (inputs outputs : List Reference) (slots : List LocalSlot) (values : Fin 4 → BitVec 128) (done : Nat) : Prop where
  call : CallingConditions program current inputs outputs
  preserved : MemoryBelow original.nextIdentity original current
  authority : AccessBelow entered.nextIdentity entered current
  snapshots : SubtractSnapshots current slots values done

/-- Storing the next snapshot keeps every earlier private snapshot and all caller facts. -/
theorem SubtractVectorState.store {program : CIL.Program} {original entered current : Memory}
    {inputs outputs : List Reference} {slots : List LocalSlot} {values : Fin 4 → BitVec 128} {done : Nat}
    (state : SubtractVectorState program original entered current inputs outputs slots values done)
    (body : CIL.Method) (specs : List NumericLocalSpec) (frame : Frame) (root : LocalSlot)
    (layout : frame.locals = root :: slots)
    (enteredWF : entered.WellFormed) (homes : NumericHomes entered original.nextIdentity specs slots)
    (bound : done < 10) (specified : specs[done]? = some vector128ZeroSpec) :
    ∃ after, SubtractVectorState program original entered after inputs outputs slots values (done + 1) ∧
      ∀ pc args rest, step body (.setLocal (done + 1)) pc args frame
        (.scalar (.v128 (subtractSnapshot values ⟨done, bound⟩)) :: rest) current =
          .ok (.next (pc + 1) rest frame after) := by
  obtain ⟨reference, after, slot, loaded, retained, afterCall, afterAuthority, written, stored⟩ :=
    vector128_local_store program body specs original.nextIdentity entered current inputs outputs frame root slots
      layout state.call enteredWF homes state.authority done vector128ZeroSpec specified
      (.v128 (subtractSnapshot values ⟨done, bound⟩)) (subtractSnapshot values ⟨done, bound⟩).toNat rfl
  have tailSlot : slots[done]? = some (.bytes .vector128 reference) := by
    simpa [layout, vector128ZeroSpec] using slot
  refine ⟨after, ⟨afterCall, state.preserved.trans retained, afterAuthority, ?_⟩, fun pc args rest => stored pc args rest⟩
  intro i lower
  by_cases same : i.val = done
  · have equal : i = ⟨done, bound⟩ := Fin.ext same
    subst equal
    exact ⟨reference, tailSlot, loaded⟩
  · obtain ⟨source, sourceSlot, sourceRead⟩ := state.snapshots i (by omega)
    exact ⟨source, sourceSlot, vector128_prior_read specs entered current after original.nextIdentity slots homes
      i.val done (by omega) source reference sourceSlot tailSlot _ _ written sourceRead⟩

theorem SubtractSnapshots.load {current : Memory} {slots : List LocalSlot} {values : Fin 4 → BitVec 128} {done : Nat}
    (snapshots : SubtractSnapshots current slots values done)
    (frame : Frame) (root : LocalSlot) (layout : frame.locals = root :: slots)
    (i : Fin 10) (lower : i.val < done) (body : CIL.Method) (pc : Nat) (args stack : List Value) :
    step body (.local (i.val + 1)) pc args frame stack current =
      .ok (.next (pc + 1) (.scalar (.v128 (subtractSnapshot values i)) :: stack) frame current) := by
  obtain ⟨reference, slot, loaded⟩ := snapshots i lower
  have actual : frame.locals[i.val + 1]? = some (.bytes .vector128 reference) := by
    simpa [layout] using slot
  exact step_load_numeric_local .vector128 (.v128 _) _ rfl actual loaded

theorem SubtractVectorState.load {program : CIL.Program} {original entered current : Memory}
    {inputs outputs : List Reference} {slots : List LocalSlot} {values : Fin 4 → BitVec 128} {done : Nat}
    (state : SubtractVectorState program original entered current inputs outputs slots values done)
    (frame : Frame) (root : LocalSlot) (layout : frame.locals = root :: slots)
    (i : Fin 10) (lower : i.val < done) (body : CIL.Method) (pc : Nat) (args stack : List Value) :
    step body (.local (i.val + 1)) pc args frame stack current =
      .ok (.next (pc + 1) (.scalar (.v128 (subtractSnapshot values i)) :: stack) frame current) :=
  state.snapshots.load frame root layout i lower body pc args stack

/-- Fresh private homes keep their snapshots across writes that spare fresh allocations. -/
theorem SubtractSnapshots.transfer {entered before after : Memory} {boundary : Nat}
    {specs : List NumericLocalSpec} {slots : List LocalSlot} {values : Fin 4 → BitVec 128} {done : Nat}
    (snapshots : SubtractSnapshots before slots values done)
    (homes : NumericHomes entered boundary specs slots)
    (vectorSpecs : ∀ i : Fin 10, specs[i.val]? = some vector128ZeroSpec)
    (kept : ∀ reference, boundary ≤ reference.allocation → ∀ bytes,
      read before reference 16 1 = .ok bytes → read after reference 16 1 = .ok bytes) :
    SubtractSnapshots after slots values done := by
  intro i lower
  obtain ⟨reference, slot, loaded⟩ := snapshots i lower
  obtain ⟨home, homeSlot, fresh, _, _⟩ := homes.home_at i.val vector128ZeroSpec (vectorSpecs i)
  have same : home = reference := by
    rw [slot] at homeSlot
    simpa [vector128ZeroSpec] using homeSlot.symm
  subst home
  exact ⟨reference, slot, kept reference fresh _ loaded⟩

theorem SubtractVectorState.retain {program : CIL.Program} {original entered current : Memory}
    {inputs outputs : List Reference} {slots : List LocalSlot} {values : Fin 4 → BitVec 128} {done : Nat}
    (state : SubtractVectorState program original entered current inputs outputs slots values done)
    (fewer : Nat) (smaller : fewer ≤ done) :
    SubtractVectorState program original entered current inputs outputs slots values fewer :=
  ⟨state.call, state.preserved, state.authority, fun i lower => state.snapshots i (by omega)⟩

#print axioms SubtractVectorState.store
#print axioms SubtractVectorState.load
#print axioms SubtractVectorState.retain
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector

/-- Lane differences and borrow masks from the four saved halves. -/
theorem subtract_start_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (leadingLength : leading.length = 22)
    (code : body.code = leading ++ subtractStartCode ++ tail)
    (vectorSpecs : ∀ i : Fin 10, specs[i.val]? = some vector128ZeroSpec)
    (original entered current : Memory) (inputs outputs : List Reference)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot) (layout : frame.locals = root :: slots)
    (args : List Value) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity specs slots) (values : Fin 4 → BitVec 128)
    (state : SubtractVectorState program original entered current inputs outputs slots values 4)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, SubtractVectorState program original entered after inputs outputs slots values 8 →
      ∃ fuel result returned,
        run program fuel method 38 args frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 22 args frame [] current = .ok (result, returned) ∧ post result returned := by
  obtain ⟨m4, s5, st4⟩ := state.store body specs frame root layout enteredWF homes (by decide) (vectorSpecs 4)
  obtain ⟨m5, s6, st5⟩ := s5.store body specs frame root layout enteredWF homes (by decide) (vectorSpecs 5)
  obtain ⟨m6, s7, st6⟩ := s6.store body specs frame root layout enteredWF homes (by decide) (vectorSpecs 6)
  obtain ⟨m7, s8, st7⟩ := s7.store body specs frame root layout enteredWF homes (by decide) (vectorSpecs 7)
  have done := continuation m7 s8
  have a0 := state.load frame root layout 0 (by decide) body
  have a2 := state.load frame root layout 2 (by decide) body
  have b1 := s5.load frame root layout 1 (by decide) body
  have b3 := s5.load frame root layout 3 (by decide) body
  have c0 := s6.load frame root layout 0 (by decide) body
  have c2 := s6.load frame root layout 2 (by decide) body
  have d1 := s7.load frame root layout 1 (by decide) body
  have d3 := s7.load frame root layout 3 (by decide) body
  have e0 : subtractSnapshot values 0 = values 0 := rfl
  have e1 : subtractSnapshot values 1 = values 1 := rfl
  have e2 : subtractSnapshot values 2 = values 2 := rfl
  have e3 : subtractSnapshot values 3 = values 3 := rfl
  have e4 : subtractSnapshot values ⟨4, by decide⟩ = zip128 (· - ·) (values 0) (values 2) := rfl
  have e5 : subtractSnapshot values ⟨5, by decide⟩ = zip128 (· - ·) (values 1) (values 3) := rfl
  have e6 : subtractSnapshot values ⟨6, by decide⟩ =
      zip128 (fun x y => mask64 (x.ult y)) (values 0) (values 2) := rfl
  have e7 : subtractSnapshot values ⟨7, by decide⟩ =
      zip128 (fun x y => mask64 (x.ult y)) (values 1) (values 3) := rfl
  rw [e0] at a0 c0
  rw [e1] at b1 d1
  rw [e2] at a2 c2
  rw [e3] at b3 d3
  rw [e4] at st4
  rw [e5] at st5
  rw [e6] at st6
  rw [e7] at st7
  repeat' first
    | exact done
    | (apply run_next_exists post found (by simp [code, List.getElem?_append, leadingLength, subtractStartCode]; rfl)
       first
       | exact a0 _ _ _
       | exact a2 _ _ _
       | exact b1 _ _ _
       | exact b3 _ _ _
       | exact c0 _ _ _
       | exact c2 _ _ _
       | exact d1 _ _ _
       | exact d3 _ _ _
       | exact st4 _ _ _
       | exact st5 _ _ _
       | exact st6 _ _ _
       | exact st7 _ _ _
       | (simp (config := { implicitDefEqProofs := false })
           [step, checkedIntrinsic, pureArity, scalars, CIL.step.eq_def, CIL.Intrinsic.available,
             CIL.Vector.intrinsic_sub128, CIL.Vector.intrinsic_lt128, checkedValue, numericValue,
             Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms subtract_start_checked
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.AddSubtract.Safety CIL.Vector

/-- The selected ISA's incoming-borrow instructions store both shifted masks. -/
theorem subtract_incoming_checked (program : CIL.Program) (body : CIL.Method) (method : Nat) (specs : List NumericLocalSpec)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (leadingLength : leading.length = 38)
    (code : body.code = leading ++ subtractIncomingCode body.profile.advSimd ++ tail)
    (sse : body.profile.advSimd = false → body.profile.sse2 = true)
    (ssse : body.profile.advSimd = false → body.profile.ssse3 = true)
    (vectorSpecs : ∀ i : Fin 10, specs[i.val]? = some vector128ZeroSpec)
    (original entered current : Memory) (inputs outputs : List Reference)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot) (layout : frame.locals = root :: slots)
    (args : List Value) (enteredWF : entered.WellFormed)
    (homes : NumericHomes entered original.nextIdentity specs slots) (values : Fin 4 → BitVec 128)
    (state : SubtractVectorState program original entered current inputs outputs slots values 8)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after, SubtractVectorState program original entered after inputs outputs slots values 10 →
      ∃ fuel result returned,
        run program fuel method 63 args frame [] after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 38 args frame [] current = .ok (result, returned) ∧ post result returned := by
  obtain ⟨m8, s9, st8⟩ := state.store body specs frame root layout enteredWF homes (by decide) (vectorSpecs 8)
  obtain ⟨m9, s10, st9⟩ := s9.store body specs frame root layout enteredWF homes (by decide) (vectorSpecs 9)
  have done := continuation m9 s10
  have a6 := state.load frame root layout 6 (by decide) body
  have b6 := s9.load frame root layout 6 (by decide) body
  have b7 := s9.load frame root layout 7 (by decide) body
  have e6 : subtractSnapshot values 6 = subtractMask (values 0) (values 2) := rfl
  have e7 : subtractSnapshot values 7 = subtractMask (values 1) (values 3) := rfl
  have e8 : subtractSnapshot values ⟨8, by decide⟩ = incoming128Low (subtractMask (values 0) (values 2)) := rfl
  have e9 : subtractSnapshot values ⟨9, by decide⟩ =
      incoming128High (subtractMask (values 0) (values 2)) (subtractMask (values 1) (values 3)) := rfl
  rw [e6] at a6 b6
  rw [e7] at b7
  rw [e8] at st8
  rw [e9] at st9
  cases selected : body.profile.advSimd
  · rw [← incoming128_sse_low] at st8
    rw [← incoming128_sse_high] at st9
    repeat' first
      | exact done
      | (apply run_next_exists post found (by simp [code, List.getElem?_append, leadingLength, subtractIncomingCode, selected]; rfl)
         first
         | exact a6 _ _ _
         | exact b6 _ _ _
         | exact b7 _ _ _
         | exact st8 _ _ _
         | exact st9 _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [show (BitVec.setWidth 8 (8 : BitVec 32)).toNat = 8 from rfl, step, selected, sse, ssse, pureArity,
               scalars, CIL.step.eq_def, CIL.Intrinsic.available, CIL.FeatureProfile.evaluate,
               CIL.Vector.intrinsic_sse_shift, CIL.Vector.intrinsic_sse_align,
               CIL.Vector.intrinsic_reinterpret128, checkedValue, numericValue,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))
  · rw [← incoming128_arm_low] at st8
    rw [← incoming128_arm_high] at st9
    repeat' first
      | exact done
      | (apply run_next_exists post found (by simp [code, List.getElem?_append, leadingLength, subtractIncomingCode, selected]; rfl)
         first
         | exact a6 _ _ _
         | exact b6 _ _ _
         | exact b7 _ _ _
         | exact st8 _ _ _
         | exact st9 _ _ _
         | (simp (config := { implicitDefEqProofs := false })
             [step, selected, pureArity, scalars, CIL.step.eq_def, CIL.Intrinsic.available, CIL.FeatureProfile.evaluate,
               CIL.Vector.intrinsic_zero128, CIL.Vector.intrinsic_adv_extract, checkedValue, numericValue,
               Bind.bind, Except.bind, Pure.pure, Except.pure]
            first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

/-- Branch on the actual coalesced propagation test without writing memory. -/
theorem subtract_decision_checked (program : CIL.Program) (body : CIL.Method) (method : Nat)
    (found : program[method]? = some body) (leading tail : List CIL.Op) (leadingLength : leading.length = 63)
    (code : body.code = leading ++ subtractDecisionCode ++ tail)
    (original entered current : Memory) (inputs outputs : List Reference)
    (frame : Frame) (root : LocalSlot) (slots : List LocalSlot) (layout : frame.locals = root :: slots)
    (args : List Value) (values : Fin 4 → BitVec 128)
    (state : SubtractVectorState program original entered current inputs outputs slots values 10)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel result returned,
      run program fuel method (if subtractPropagation values = BitVec.ofNat 128 0 then 119 else 77) args frame []
        current = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 63 args frame [] current = .ok (result, returned) ∧ post result returned := by
  have a4 := state.load frame root layout 4 (by decide) body
  have a5 := state.load frame root layout 5 (by decide) body
  have a8 := state.load frame root layout 8 (by decide) body
  have a9 := state.load frame root layout 9 (by decide) body
  by_cases zero : subtractPropagation values = BitVec.ofNat 128 0
  all_goals
    simp only [zero, ite_true, ite_false] at continuation
    unfold subtractPropagation at zero
    iterate 14
      apply run_next_exists post found (by simp [code, List.getElem?_append, leadingLength, subtractDecisionCode]; rfl)
      first
      | exact a4 _ _ _
      | exact a5 _ _ _
      | exact a8 _ _ _
      | exact a9 _ _ _
      | (simp (config := { implicitDefEqProofs := false })
           [CIL.truth, Option.bind, List.mapM, checkedIntrinsic, step, pureArity, scalars, CIL.step.eq_def,
             CIL.Intrinsic.available, CIL.Vector.intrinsic_zero128, CIL.Vector.intrinsic_eq128,
             CIL.Vector.intrinsic_and128, CIL.Vector.intrinsic_or128, CIL.Vector.intrinsic_equal_all128,
             show (0 : BitVec 128) = BitVec.ofNat 128 0 from rfl, zero,
             checkedValue, numericValue, Bind.bind, Except.bind, Pure.pure, Except.pure]
         try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))
    try simp only [List.reverse_nil]
    -- The intrinsic simp set splits the or-test into two zero tests.
    split
    all_goals first
      | exact continuation
      | (exfalso; simp only [show (0 : BitVec 128) = BitVec.ofNat 128 0 from rfl] at *; simp_all)

#print axioms subtract_incoming_checked
#print axioms subtract_decision_checked
end UInt256Proof.Subtract.Profile
