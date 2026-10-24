import CIL.StepEquations
import CIL.Safety.Equations
import UInt256.Methods.Subtract.Vector128Entry
import UInt256.Methods.Subtract.SmallHelper
import CIL.Safety.WordLocals

namespace UInt256Proof.Subtract.Profile
open CIL.Safety

def subtractScalarUnreachable : CIL.Op := .unsupported "Unreachable under selected profile"

/-- AdvSimd skips the SSE4.2 guard; both ISAs share the right-small test and the vector call. -/
def subtractScalarGuard (adv : Bool) : List CIL.Op :=
  [if adv then subtractScalarUnreachable else .feature .sse42,
   if adv then subtractScalarUnreachable else .brzero 26]

def subtractScalarBody (profile : CIL.FeatureProfile) (vectorIndex smallIndex : Nat) : CIL.Method :=
  { profile := profile, returnsValue := true,
    locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
    localKinds := [.word64, .word64, .word64, .word64, .word64, .word64],
    parameterHomes := [], staticSites := [],
    code := [.arg 1, .fieldAt 0 8, .setLocal 0, .arg 1, .fieldAt 8 8, .arg 1, .fieldAt 16 8, .bor,
      .arg 1, .fieldAt 24 8, .bor, .brnonzero 17, .arg 0, .local 0, .arg 2, .call smallIndex 3,
      .ret (some .unsigned8), .feature .advSimd, .brnonzero 21] ++ subtractScalarGuard profile.advSimd ++
      [.arg 0, .arg 1, .arg 2, .call vectorIndex 3, .ret (some .unsigned8)] ++
      List.replicate 41 subtractScalarUnreachable }

def subtractScalarSpecs : List (Option (BitVec 64)) := List.replicate 6 (some 0)

theorem subtract_scalar_frame_setup (profile : CIL.FeatureProfile) (vectorIndex smallIndex : Nat)
    (memory : Memory) (args : List Value) (wellFormed : memory.WellFormed) :
    ∃ frame result,
      enterFrame (subtractScalarBody profile vectorIndex smallIndex) args memory = .ok (frame, result) ∧
      WordHomes result memory.nextIdentity subtractScalarSpecs frame.locals ∧
      MemoryBelow memory.nextIdentity memory result ∧ result.WellFormed :=
  word_frame_setup (subtractScalarBody profile vectorIndex smallIndex) subtractScalarSpecs (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) memory args wellFormed

#print axioms subtract_scalar_frame_setup
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety

theorem subtract_scalar_right_store (program : CIL.Program) (body : CIL.Method)
    (memory entered : Memory) (left right output : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] [output])
    (setup : enterFrame body (binaryArguments left right output) memory = .ok (frame, entered))
    (homes : WordHomes entered memory.nextIdentity subtractScalarSpecs frame.locals) :
    ∃ reference after,
      frame.locals[0]? = some (.bytes .word64 reference) ∧
      read after reference 8 1 = .ok (numberBytes (inputLimb memory right 0).toNat 8) ∧
      MemoryBelow memory.nextIdentity memory after ∧
      CallingConditions program after [left, right] [output] ∧
      AccessBelow entered.nextIdentity entered after ∧
      ∀ pc rest, step body (.setLocal 0) pc (binaryArguments left right output) frame
        (.scalar (.i64 (inputLimb memory right 0)) :: rest) entered = .ok (.next (pc + 1) rest frame after) := by
  have specified : subtractScalarSpecs[0]? = some (some 0) := by rfl
  obtain ⟨reference, slot, bound, _, writable⟩ := homes.word_at 0 0 specified
  obtain ⟨after, written, _, loaded, _⟩ := store_local_word64 (inputLimb memory right 0) writable
  have preserved := (enterFrame_preserves_caller_memory _ _ _ _ _ setup).trans
    (write_preserves_memory_below _ _ _ _ _ _ bound written)
  have enteredCall := call.after_frame_setup setup
  refine ⟨reference, after, slot, loaded, preserved,
    call.after_memory_below preserved (write_preserves_wellFormed _ _ _ _ _ enteredCall.1.1 written)
      (write_preserves_static_world _ _ _ _ _ _ enteredCall.2 written),
    write_preserves_access_below written _, ?_⟩
  intro pc rest
  obtain ⟨result, stepped, sameWrite, _⟩ := step_store_word64_same_frame
    (body := body) (pc := pc) (args := binaryArguments left right output) (rest := rest)
    (inputLimb memory right 0) slot writable
  rw [written] at sameWrite
  cases sameWrite
  exact stepped

/-- Save the right low limb and or-combine its three upper limbs from initial caller bytes. -/
theorem subtract_scalar_prefix (program : CIL.Program) (method vectorIndex smallIndex : Nat)
    (profile : CIL.FeatureProfile) (found : program[method]? = some (subtractScalarBody profile vectorIndex smallIndex))
    (memory entered : Memory) (left right output : Reference) (frame : Frame)
    (call : CallingConditions program memory [left, right] [output])
    (setup : enterFrame (subtractScalarBody profile vectorIndex smallIndex) (binaryArguments left right output) memory =
      .ok (frame, entered))
    (homes : WordHomes entered memory.nextIdentity subtractScalarSpecs frame.locals)
    (post : Memory → List Value → Prop)
    (continuation : ∀ reference after,
      frame.locals[0]? = some (.bytes .word64 reference) →
      read after reference 8 1 = .ok (numberBytes (inputLimb memory right 0).toNat 8) →
      MemoryBelow memory.nextIdentity memory after →
      CallingConditions program after [left, right] [output] →
      AccessBelow entered.nextIdentity entered after →
      ∃ fuel result returned,
        run program fuel method 11 (binaryArguments left right output) frame
          [.scalar (.i64 (inputLimb memory right 1 ||| inputLimb memory right 2 ||| inputLimb memory right 3))]
          after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method 0 (binaryArguments left right output) frame [] entered =
        .ok (result, returned) ∧ post result returned := by
  obtain ⟨reference, after, slot, loaded, preserved, afterCall, authority, stored⟩ :=
    subtract_scalar_right_store program (subtractScalarBody profile vectorIndex smallIndex) memory entered
      left right output frame call setup homes
  have done := continuation reference after slot loaded preserved afterCall authority
  have beforeFormed := (call.after_frame_setup setup).input_formed (reference := right) (by simp)
  have afterFormed := afterCall.input_formed (reference := right) (by simp)
  have firstRead := call.input_field_after_setup setup (by simp : right ∈ [left, right]) 0
  have upperReads (index : Fin 4) (rest : List Value) :
      instruction (.fieldAt (8 * index.val) 8) (.reference (.address right) :: rest) after =
        .ok (after, .scalar (.i64 (inputLimb memory right index)) :: rest) := by
    rw [afterCall.input_field_instruction (by simp) index rest]
    simp only [inputLimb, call.input_bytes_of_memory_below preserved (reference := right) (by simp)]
  have upper1 := upperReads 1
  have upper2 := upperReads 2
  have upper3 := upperReads 3
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show (3 : Fin 4).val = 3 from rfl, Nat.reduceMul]
    at firstRead upper1 upper2 upper3
  repeat' first
    | exact done
    | (simp (config := { failIfUnchanged := false }) [BitVec.ofNat_eq_ofNat]
       apply run_next_exists post found (by rfl)
       first
       | ((with_reducible show step _ (.setLocal 0) _ _ _ _ _ = _); exact stored _ _)
       | (simp (config := { implicitDefEqProofs := false })
           [step, cil_guard, observerCount, binaryArguments, checkedValue, numericValue, formValue, beforeFormed, afterFormed,
             firstRead, upper1, upper2, upper3, pureArity, scalars, CIL.step, CIL.binary, CIL.unary, checkedAt,
             Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

/-- A zero upper part selects the small helper; otherwise control reaches the ISA guard. -/
theorem subtract_scalar_upper_branch (program : CIL.Program) (method vectorIndex smallIndex : Nat)
    (profile : CIL.FeatureProfile) (found : program[method]? = some (subtractScalarBody profile vectorIndex smallIndex))
    (memory : Memory) (frame : Frame) (args : List Value) (condition : BitVec 64)
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel method (if condition = BitVec.ofNat 64 0 then 12 else 17) args frame [] memory =
        .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel method 11 args frame [.scalar (.i64 condition)] memory =
        .ok (final, returned) ∧ post final returned := by
  by_cases zero : condition = BitVec.ofNat 64 0
  all_goals
    simp only [zero, ite_true, ite_false] at continuation
    apply run_next_exists post found (by rfl) _ continuation
    simp [step, cil_guard, observerCount, checkedValue, numericValue, pureArity, scalars, CIL.step.eq_def, CIL.truth,
      show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, zero,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem subtract_scalar_next (original entered current : Memory) (frame : Frame)
    (homes : WordHomes entered original.nextIdentity subtractScalarSpecs frame.locals)
    (enteredWF : entered.WellFormed) (currentWF : current.WellFormed)
    (authority : AccessBelow entered.nextIdentity entered current) : original.nextIdentity ≤ current.nextIdentity := by
  have specified : subtractScalarSpecs[0]? = some (some 0) := by rfl
  obtain ⟨reference, _, fresh, _, writable⟩ := homes.word_at 0 0 specified
  obtain ⟨allocation, ready⟩ := access_requirements writable
  have currentWrite := authority.access writable (enteredWF.1 _ _ ready.present).1
  obtain ⟨currentAllocation, currentReady⟩ := access_requirements currentWrite
  exact Nat.le_trans fresh (Nat.le_of_lt (currentWF.1 _ _ currentReady.present).1)

#print axioms subtract_scalar_right_store
#print axioms subtract_scalar_prefix
#print axioms subtract_scalar_upper_branch
#print axioms subtract_scalar_next
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.Subtract.Safety

/-- A child result over current caller bytes is the parent result over the original bytes. -/
theorem subtract_result_retire {program : CIL.Program} (original current final : Memory) (frame : Frame)
    (left right output : Reference) (returned : List Value)
    (call : CallingConditions program original [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (next : original.nextIdentity ≤ current.nextIdentity)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (result : SubtractResult current final returned left right output) :
    SubtractResult original (leaveFrame frame final) returned left right output := by
  have keptLeft : inputValue current left = inputValue original left := by
    simp only [inputValue, call.input_bytes_of_memory_below preserved (reference := left) (by simp)]
  have keptRight : inputValue current right = inputValue original right := by
    simp only [inputValue, call.input_bytes_of_memory_below preserved (reference := right) (by simp)]
  have retained := leaveFrame_preserves_memory_below frame final original.nextIdentity owned
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.output_formed (by simp : output ∈ [output]))
  have old := (call.1.1.1 _ _ present).1
  have bytes : (fun offset => ((leaveFrame frame final).cells output.allocation offset).bits) =
      (fun offset => (final.cells output.allocation offset).bits) := by
    funext offset
    rw [retained.cells output.allocation old offset]
  refine ⟨leaveFrame_preserves_wellFormed _ _ result.wellFormed, ?_, ?_, ?_, ?_⟩
  · have math := result.value
    rw [keptLeft, keptRight] at math
    simpa only [inputValue, bytes] using math
  · rw [result.flag]
    simp only [subtractUnderflow, keptLeft, keptRight]
  · exact (retained.access output old 32 1 true).trans result.writable
  · intro id bound offset outside
    exact (retained.cells id bound offset).trans
      ((result.footprint id (Nat.lt_of_lt_of_le bound next) offset outside).trans (preserved.cells id bound offset))

theorem subtract_input_small_value (memory : Memory) (reference : Reference)
    (small : inputLimb memory reference 1 ||| inputLimb memory reference 2 ||| inputLimb memory reference 3 = 0) :
    inputValue memory reference = BitVec.ofNat 256 (inputLimb memory reference 0).toNat := by
  obtain ⟨h12, h3⟩ := BitVec.or_eq_zero_iff.mp small
  obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h12
  have initial : UInt256Model.value (inputLimb memory reference) = inputValue memory reference :=
    UInt256Proof.input_value (fun offset => (memory.cells reference.allocation offset).bits) reference.offset
  rw [← initial, ← UInt256Proof.singleLimb_eq (inputLimb memory reference) h1 h2 h3]
  simp [UInt256Model.value, UInt256Proof.singleLimb]

/-- The right-small route calls the certified small helper on the left operand and the saved limb. -/
theorem subtract_scalar_small_route (program : CIL.Program) (method vectorIndex smallIndex storage : Nat)
    (profile : CIL.FeatureProfile) (found : program[method]? = some (subtractScalarBody profile vectorIndex smallIndex))
    (smallFound : program[smallIndex]? = some (subtractSmallBody profile storage))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (original current : Memory) (frame : Frame) (left right output home : Reference)
    (call : CallingConditions program original [left, right] [output])
    (currentCall : CallingConditions program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (next : original.nextIdentity ≤ current.nextIdentity)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (slot : frame.locals[0]? = some (.bytes .word64 home))
    (loaded : read current home 8 1 = .ok (numberBytes (inputLimb original right 0).toNat 8))
    (small : inputLimb original right 1 ||| inputLimb original right 2 ||| inputLimb original right 3 = 0) :
    ∃ fuel final returned,
      run program fuel method 12 (binaryArguments left right output) frame [] current = .ok (final, returned) ∧
      SubtractResult original final returned left right output := by
  let word := inputLimb original right 0
  let args := binaryArguments left right output
  let post := fun final returned => SubtractResult original final returned left right output
  have member : left ∈ [left, right] := by simp
  have selected : CallingConditions program current [left] [output] := by
    refine ⟨⟨currentCall.1.1, ?_, currentCall.1.2.2⟩, currentCall.2⟩
    intro view included
    have same : view = wordView left := by simpa using included
    subst view
    exact currentCall.1.2.1 _ (List.mem_map.mpr ⟨_, member, rfl⟩)
  have fl := currentCall.input_formed member
  have fo := currentCall.output_formed (by simp : output ∈ [output])
  obtain ⟨childFuel, after, values, certified, result⟩ :=
    small_checked program smallIndex storage profile smallFound storageFound current left output word selected
  have invoked := certified.1
  rw [result.underflow] at invoked
  have stepped : step (subtractScalarBody profile vectorIndex smallIndex) (.call smallIndex 3) 15 args frame
      [.reference (.address output), .scalar (.i64 word), .reference (.address left)] current =
        .ok (.call smallIndex (smallArguments left output word) [] current) := by
    simp [step, cil_guard, observerCount, smallArguments, checkedValue, numericValue, formValue, fl, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have returned : run program 1 method 16 args frame
      [.scalar (.i32 (if (inputValue current left).toNat < word.toNat then 1 else 0))] after =
        .ok (leaveFrame frame after, [.scalar (.i32 (if (inputValue current left).toNat < word.toNat then 1 else 0))]) := by
    have fetched : (subtractScalarBody profile vectorIndex smallIndex).code[16]? = some (.ret (some .unsigned8)) := by rfl
    have returns : (subtractScalarBody profile vectorIndex smallIndex).returnsValue = true := rfl
    split <;> simp [run, found, fetched, returns, step, cil_guard, observerCount, checkedValue, numericValue, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure] <;> rfl
  obtain ⟨fuel, finished⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, invoked⟩ ⟨1, returned⟩
  have keptLeft : inputValue current left = inputValue original left := by
    simp only [inputValue, call.input_bytes_of_memory_below preserved (reference := left) (by simp)]
  have keptRight : inputValue current right = inputValue original right := by
    simp only [inputValue, call.input_bytes_of_memory_below preserved (reference := right) (by simp)]
  have smallValue := subtract_input_small_value original right small
  have wide : (inputLimb original right 0).toNat < 2^256 := Nat.lt_trans (inputLimb original right 0).isLt (by decide)
  have childResult : SubtractResult current after
      [.scalar (.i32 (if (inputValue current left).toNat < word.toNat then 1 else 0))] left right output := by
    refine ⟨result.wellFormed, ?_, ?_, result.writable, result.footprint⟩
    · rw [result.modular_difference, keptRight, smallValue]
    · simp only [subtractUnderflow, keptRight, smallValue, BitVec.toNat_ofNat, Nat.mod_eq_of_lt wide]
      rfl
  have done := subtract_result_retire original current after frame left right output _ call preserved next owned childResult
  have wordLoad := fun (pc : Nat) (stack : List Value) => step_load_word64
    (body := subtractScalarBody profile vectorIndex smallIndex) (pc := pc) (args := args) (stack := stack) slot loaded
  have finish : ∃ fuel final returned,
      run program fuel method 15 args frame
        [.reference (.address output), .scalar (.i64 word), .reference (.address left)] current =
        .ok (final, returned) ∧ post final returned := ⟨fuel, _, _, finished, done⟩
  repeat' first
    | exact finish
    | (apply run_next_exists post found (by rfl)
       first
       | exact wordLoad _ _
       | (simp (config := { implicitDefEqProofs := false })
           [step, cil_guard, observerCount, args, binaryArguments, checkedValue, formValue, fl, fo,
             checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
          try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)))

#print axioms subtract_result_retire
#print axioms subtract_input_small_value
#print axioms subtract_scalar_small_route
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.Subtract.Safety

/-- With AdvSimd, or SSE4.2 without it, the dispatcher calls the certified 128-bit helper. -/
theorem subtract_scalar_vector_route (program : CIL.Program) (method vectorIndex smallIndex borrow storage : Nat)
    (profile : CIL.FeatureProfile) (found : program[method]? = some (subtractScalarBody profile vectorIndex smallIndex))
    (vectorFound : program[vectorIndex]? = some (subtractVectorBody profile borrow storage))
    (borrowFound : program[borrow]? = some (borrowBody profile))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (sse : profile.advSimd = false → profile.sse2 = true)
    (ssse : profile.advSimd = false → profile.ssse3 = true)
    (sse42 : profile.advSimd = false → profile.sse42 = true)
    (original current : Memory) (frame : Frame) (left right output : Reference)
    (call : CallingConditions program original [left, right] [output])
    (currentCall : CallingConditions program current [left, right] [output])
    (preserved : MemoryBelow original.nextIdentity original current)
    (next : original.nextIdentity ≤ current.nextIdentity)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id) :
    ∃ fuel final returned,
      run program fuel method 17 (binaryArguments left right output) frame [] current = .ok (final, returned) ∧
      SubtractResult original final returned left right output := by
  let args := binaryArguments left right output
  let post := fun final returned => SubtractResult original final returned left right output
  obtain ⟨childFuel, final, returned, certified, result⟩ :=
    checked_subtract_vector_contract program vectorIndex borrow storage profile vectorFound borrowFound storageFound
      sse ssse current left right output currentCall
  have fl := currentCall.input_formed (reference := left) (by simp)
  have fr := currentCall.input_formed (reference := right) (by simp)
  have fo := currentCall.output_formed (reference := output) (by simp)
  have stepped : step (subtractScalarBody profile vectorIndex smallIndex) (.call vectorIndex 3) 24 args frame
      [.reference (.address output), .reference (.address right), .reference (.address left)] current =
        .ok (.call vectorIndex (binaryArguments left right output) [] current) := by
    simp [step, cil_guard, observerCount, args, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have returnedRun : run program 1 method 25 args frame (returned ++ []) final =
      .ok (leaveFrame frame final, returned) := by
    have fetched : (subtractScalarBody profile vectorIndex smallIndex).code[25]? = some (.ret (some .unsigned8)) := by rfl
    have returns : (subtractScalarBody profile vectorIndex smallIndex).returnsValue = true := rfl
    rw [result.flag]
    unfold subtractUnderflow
    split <;> simp [run, found, fetched, returns, step, cil_guard, observerCount, checkedValue, numericValue, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure] <;> rfl
  obtain ⟨fuel, executed⟩ := run_call_exists found (by rfl) stepped ⟨childFuel, certified.1⟩ ⟨1, returnedRun⟩
  have done := subtract_result_retire original current final frame left right output returned call preserved next owned result
  have finish : ∃ fuel final returned,
      run program fuel method 24 args frame
        [.reference (.address output), .reference (.address right), .reference (.address left)] current =
        .ok (final, returned) ∧ post final returned := ⟨fuel, _, _, executed, done⟩
  have bodyProfile : (subtractScalarBody profile vectorIndex smallIndex).profile = profile := rfl
  cases adv : profile.advSimd
  · have enabled := sse42 adv
    repeat' first
      | exact finish
      | (apply run_next_exists post found (by rfl)
         simp (config := { implicitDefEqProofs := false })
           [step, cil_guard, observerCount, adv, enabled, bodyProfile, args, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo,
             pureArity, scalars, CIL.step.eq_def, CIL.truth, CIL.FeatureProfile.evaluate,
             checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
         try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))
  · repeat' first
      | exact finish
      | (apply run_next_exists post found (by rfl)
         simp (config := { implicitDefEqProofs := false })
           [step, cil_guard, observerCount, adv, bodyProfile, args, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo,
             pureArity, scalars, CIL.step.eq_def, CIL.truth, CIL.FeatureProfile.evaluate,
             checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
         try (first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms subtract_scalar_vector_route
end UInt256Proof.Subtract.Profile

namespace UInt256Proof.Subtract.Profile
open CIL.Safety UInt256Model.Safety UInt256Proof.Subtract.Safety

/-- Complete dispatcher execution: right-small helper or the 128-bit vector helper. -/
theorem subtract_scalar_entry (program : CIL.Program) (method vectorIndex smallIndex borrow storage : Nat)
    (profile : CIL.FeatureProfile) (found : program[method]? = some (subtractScalarBody profile vectorIndex smallIndex))
    (vectorFound : program[vectorIndex]? = some (subtractVectorBody profile borrow storage))
    (smallFound : program[smallIndex]? = some (subtractSmallBody profile storage))
    (borrowFound : program[borrow]? = some (borrowBody profile))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (sse : profile.advSimd = false → profile.sse2 = true)
    (ssse : profile.advSimd = false → profile.ssse3 = true)
    (sse42 : profile.advSimd = false → profile.sse42 = true)
    (original entered : Memory) (left right output : Reference) (frame : Frame)
    (call : CallingConditions program original [left, right] [output])
    (setup : enterFrame (subtractScalarBody profile vectorIndex smallIndex) (binaryArguments left right output) original =
      .ok (frame, entered))
    (homes : WordHomes entered original.nextIdentity subtractScalarSpecs frame.locals) :
    ∃ fuel final returned,
      run program fuel method 0 (binaryArguments left right output) frame [] entered = .ok (final, returned) ∧
      SubtractResult original final returned left right output := by
  let post := fun final returned => SubtractResult original final returned left right output
  have enteredWF := (call.after_frame_setup setup).1.1
  have fresh := enterFrame_fresh _ _ _ _ _ setup
  have owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id := fun id member => (fresh.2 id member).1
  apply subtract_scalar_prefix program method vectorIndex smallIndex profile found original entered left right output
    frame call setup homes post
  intro home current slot loaded preserved currentCall authority
  have next := subtract_scalar_next original entered current frame homes enteredWF currentCall.1.1 authority
  apply subtract_scalar_upper_branch program method vectorIndex smallIndex profile found current frame _ _ post
  by_cases small : inputLimb original right 1 ||| inputLimb original right 2 ||| inputLimb original right 3 =
    BitVec.ofNat 64 0
  · simp only [small, ite_true]
    exact subtract_scalar_small_route program method vectorIndex smallIndex storage profile found smallFound storageFound
      original current frame left right output home call currentCall preserved next owned slot loaded small
  · simp only [small, ite_false]
    exact subtract_scalar_vector_route program method vectorIndex smallIndex borrow storage profile found vectorFound
      borrowFound storageFound sse ssse sse42 original current frame left right output call currentCall preserved next owned

/-- Certify the dispatcher and every visited state from ordinary caller views. -/
theorem checked_subtract_scalar_contract (program : CIL.Program) (method vectorIndex smallIndex borrow storage : Nat)
    (profile : CIL.FeatureProfile) (found : program[method]? = some (subtractScalarBody profile vectorIndex smallIndex))
    (vectorFound : program[vectorIndex]? = some (subtractVectorBody profile borrow storage))
    (smallFound : program[smallIndex]? = some (subtractSmallBody profile storage))
    (borrowFound : program[borrow]? = some (borrowBody profile))
    (storageFound : program[storage]? = some (UInt256Proof.Multiply.LimbStorage.body profile))
    (sse : profile.advSimd = false → profile.sse2 = true)
    (ssse : profile.advSimd = false → profile.ssse3 = true)
    (sse42 : profile.advSimd = false → profile.sse42 = true)
    (memory : Memory) (left right output : Reference)
    (call : CallingConditions program memory [left, right] [output]) :
    ∃ fuel final returned,
      InvocationCertificate program method (binaryArguments left right output) memory fuel final returned ∧
      SubtractResult memory final returned left right output := by
  let args := binaryArguments left right output
  obtain ⟨frame, entered, setup, homes, _, _⟩ :=
    subtract_scalar_frame_setup profile vectorIndex smallIndex memory args call.1.1
  obtain ⟨fuel, final, returned, executed, result⟩ :=
    subtract_scalar_entry program method vectorIndex smallIndex borrow storage profile found vectorFound smallFound
      borrowFound storageFound sse ssse sse42 memory entered left right output frame call setup homes
  have checked : args.mapM (checkedValue memory) = .ok args := by
    have fl := call.input_formed (reference := left) (by simp)
    have fr := call.input_formed (reference := right) (by simp)
    have fo := call.output_formed (reference := output) (by simp)
    simp [args, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo,
      checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have live := checked_entry_live_state _ _ _ _ _ _ _ call.1.1 call.2 checked setup
  exact ⟨fuel, final, returned,
    certify_invocation program method (subtractScalarBody profile vectorIndex smallIndex)
      args memory frame entered fuel final returned found checked setup live executed, result⟩

#print axioms subtract_scalar_entry
#print axioms checked_subtract_scalar_contract
end UInt256Proof.Subtract.Profile
