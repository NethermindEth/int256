import UInt256.Safety.PrivateWordAccess
import UInt256.Safety.OutputReturn
import UInt256.Safety.OutputValue
import UInt256.Safety.OutputReadability
import CIL.Safety.StepComposition
import CIL.Safety.WordHomes
import CIL.Safety.WordLocals
import CIL.Safety.UnknownHomes

namespace UInt256Model.Safety
open CIL.Safety

/-- Initialized word homes are writable homes of the same word kinds. -/
theorem writable_of_word_homes {memory : Memory} {lower : Nat} {specs slots}
    (homes : WordHomes memory lower specs slots) (words : ∀ spec ∈ specs, spec ≠ none) :
    WritableHomes memory lower (wordKinds specs) slots := by
  induction homes with
  | nil lower => exact .nil lower
  | root _ _ => exact absurd rfl (words none (by simp))
  | word reference _ fresh _ writable _ ih =>
    exact .cons reference .word64 fresh writable (ih fun spec member => words spec (by simp [member]))

/-- A word-local store remembers its value; the continuation receives the new state. -/
theorem PrivateWords.run_store {program : CIL.Program} {original entered current : Memory}
    {inputs outputs : List Reference} {body : CIL.Method} {frame : Frame} {known : Nat → Option (BitVec 64)}
    {kinds : List CIL.LocalKind} {method pc index : Nat} {args stack : List Value} {value : BitVec 64}
    (post : Memory → List Value → Prop)
    (state : PrivateWords program original entered current inputs outputs frame known)
    (enteredWF : entered.WellFormed) (homes : WritableHomes entered original.nextIdentity kinds frame.locals)
    (found : program[method]? = some body) (fetched : body.code[pc]? = some (.setLocal index))
    (specified : kinds[index]? = some .word64)
    (continuation : ∀ after,
      PrivateWords program original entered after inputs outputs frame (rememberWord known index value) →
      ∃ fuel result returned,
        run program fuel method (pc + 1) args frame stack after = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame (.scalar (.i64 value) :: stack) current = .ok (result, returned) ∧
        post result returned := by
  obtain ⟨after, stepped, next⟩ := state.store enteredWF homes index specified value pc args stack (body := body)
  exact run_next_exists post found fetched stepped (continuation after next)

/-- A word-local load pushes the remembered value. -/
theorem PrivateWords.run_load {program : CIL.Program} {original entered current : Memory}
    {inputs outputs : List Reference} {body : CIL.Method} {frame : Frame} {known : Nat → Option (BitVec 64)}
    {method pc index : Nat} {args stack : List Value} {value : BitVec 64}
    (post : Memory → List Value → Prop)
    (state : PrivateWords program original entered current inputs outputs frame known)
    (found : program[method]? = some body) (fetched : body.code[pc]? = some (.local index))
    (specified : known index = some value)
    (continuation : ∃ fuel result returned,
      run program fuel method (pc + 1) args frame (.scalar (.i64 value) :: stack) current = .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame stack current = .ok (result, returned) ∧ post result returned :=
  run_next_exists post found fetched (state.snapshots.load value specified) continuation

/-- An input limb read yields the original caller limb, regardless of later private stores. -/
theorem PrivateWords.run_field {program : CIL.Program} {original entered current : Memory}
    {inputs outputs : List Reference} {body : CIL.Method} {frame : Frame} {known : Nat → Option (BitVec 64)}
    {method pc : Nat} {args rest : List Value}
    (post : Memory → List Value → Prop)
    (state : PrivateWords program original entered current inputs outputs frame known)
    (originalCall : CallingConditions program original inputs outputs)
    (found : program[method]? = some body) (input : Reference) (member : input ∈ inputs) (index : Fin 4)
    (fetched : body.code[pc]? = some (.fieldAt (8 * index.val) 8))
    (continuation : ∃ fuel result returned,
      run program fuel method (pc + 1) args frame (.scalar (.i64 (inputLimb original input index)) :: rest)
        current = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame (.reference (.address input) :: rest) current =
        .ok (result, returned) ∧ post result returned := by
  apply run_next_exists post found fetched _ continuation
  simp only [step, state.input_field originalCall input member index rest, pureArity,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Store one output limb from a word local; reads disjoint from that limb survive. -/
theorem run_output_limb {program : CIL.Program} {memory : Memory} {inputs : List Reference}
    {output reference : Reference} {body : CIL.Method} {frame : Frame} {method pc position index : Nat}
    {args stack : List Value} {word : BitVec 64}
    (post : Memory → List Value → Prop)
    (call : CallingConditions program memory inputs [output])
    (found : program[method]? = some body) (limb : Fin 4)
    (argument : args[position]? = some (.reference (.address output)))
    (h0 : body.code[pc]? = some (.arg position))
    (h1 : body.code[pc + 1]? = some (.fieldAddress (8 * limb.val)))
    (h2 : body.code[pc + 2]? = some (.memory .asRef))
    (h3 : body.code[pc + 3]? = some (.local index))
    (h4 : body.code[pc + 4]? = some .store64)
    (slot : frame.locals[index]? = some (.bytes .word64 reference))
    (loaded : read memory reference 8 1 = .ok (numberBytes word.toNat 8))
    (continuation : ∀ stored, CallingConditions program stored inputs [output] →
      (∀ id offset, OutsideOutput output id offset → stored.cells id offset = memory.cells id offset) →
      read stored { output with offset := output.offset + 8 * limb.val } 8 1 = .ok (numberBytes word.toNat 8) →
      (∀ q bytes, q.allocation ≠ output.allocation ∨ q.offset + 8 ≤ output.offset + 8 * limb.val ∨
          output.offset + 8 * limb.val + 8 ≤ q.offset →
        read memory q 8 1 = .ok bytes → read stored q 8 1 = .ok bytes) →
      ∃ fuel result returned,
        run program fuel method (pc + 5) args frame stack stored = .ok (result, returned) ∧ post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame stack memory = .ok (result, returned) ∧ post result returned := by
  have length : (numberBytes word.toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨stored, written, storedCall, outside, readback⟩ :=
    call.write_output_slice (by simp : output ∈ [output]) (8 * limb.val) (numberBytes word.toNat 8)
      (by rw [length]; decide) (by rw [length]; omega)
  have formed := call.output_formed (by simp : output ∈ [output])
  have address := call.output_limb_address (by simp : output ∈ [output]) limb
  have fieldFormed := call.output_limb_formed (by simp : output ∈ [output]) limb
  apply run_next_exists post found h0
    (by simp [step, argument, checkedValue, formValue, formed, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]; try exact ⟨rfl, rfl, rfl, rfl⟩)
  apply run_next_exists post found h1
    (by simp [step, pureArity, CIL.Safety.instruction, address, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]; try exact ⟨rfl, rfl, rfl, rfl⟩)
  apply run_next_exists post found h2
    (by simp [step, staticInstruction, memoryInstruction, formValue, fieldFormed, checkedAt, Except.mapError,
      Bind.bind, Except.bind, Pure.pure, Except.pure]; try exact ⟨rfl, rfl, rfl, rfl⟩)
  apply run_next_exists post found h3 (step_load_word64 slot loaded)
  apply run_next_exists post found h4
    (by simp [step, pureArity, CIL.Safety.instruction, storeValue, referenceAt, ordinaryAccessAlignment,
      written, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]; try exact ⟨rfl, rfl, rfl, rfl⟩)
  exact continuation stored storedCall outside (by simpa only [length] using readback)
    fun q bytes disjoint readable => write_preserves_disjoint_read written readable (by simpa only [length] using disjoint)

/-- Store four remembered word locals to the output limbs and return. Private
    homes are fresh, so earlier limb and local reads survive later limb stores. -/
theorem PrivateWords.finish_words {program : CIL.Program} {original entered current : Memory}
    {inputs : List Reference} {output : Reference} {body : CIL.Method} {frame : Frame}
    {known : Nat → Option (BitVec 64)} {kinds : List CIL.LocalKind} {method pc position i0 i1 i2 i3 : Nat}
    {args : List Value} {w0 w1 w2 w3 : BitVec 64}
    (state : PrivateWords program original entered current inputs [output] frame known)
    (originalCall : CallingConditions program original inputs [output])
    (homes : WritableHomes entered original.nextIdentity kinds frame.locals)
    (owned : ∀ id ∈ frame.owned, original.nextIdentity ≤ id)
    (found : program[method]? = some body)
    (argument : args[position]? = some (.reference (.address output)))
    (tail : body.code.drop pc = [.arg position, .fieldAddress 0, .memory .asRef, .local i0, .store64,
      .arg position, .fieldAddress 8, .memory .asRef, .local i1, .store64,
      .arg position, .fieldAddress 16, .memory .asRef, .local i2, .store64,
      .arg position, .fieldAddress 24, .memory .asRef, .local i3, .store64, .ret])
    (returns : body.returnsValue = false)
    (k0 : known i0 = some w0) (k1 : known i1 = some w1) (k2 : known i2 = some w2) (k3 : known i3 = some w3)
    (expected : BitVec 256)
    (value : BitVec.ofNat 256 (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192) = expected) :
    ∃ fuel result returned,
      run program fuel method pc args frame [] current = .ok (result, returned) ∧
        OutputResult original result output expected returned := by
  have f (k : Nat) : body.code[pc + k]? = (body.code.drop pc)[k]? := by rw [List.getElem?_drop]
  rw [tail] at f
  obtain ⟨_, present, _, _⟩ := formed_reference_live _ _ _ (originalCall.output_formed (by simp : output ∈ [output]))
  have outputOld := (originalCall.1.1.1 _ _ present).1
  have separate (index : Nat) (reference : Reference)
      (slot : frame.locals[index]? = some (.bytes .word64 reference)) :
      reference.allocation ≠ output.allocation :=
    Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le outputOld (homes.home_bound index .word64 reference slot)))
  obtain ⟨r0, s0, l0⟩ := state.snapshots i0 w0 k0
  obtain ⟨r1, s1, l1⟩ := state.snapshots i1 w1 k1
  obtain ⟨r2, s2, l2⟩ := state.snapshots i2 w2 k2
  obtain ⟨r3, s3, l3⟩ := state.snapshots i3 w3 k3
  let post := fun result returned => OutputResult original result output expected returned
  apply run_output_limb post state.call found 0 argument (f 0) (f 1) (f 2) (f 3) (f 4) s0 l0
  intro m1 c1 o1 d0 keep1
  apply run_output_limb post c1 found 1 argument (f 5) (f 6) (f 7) (f 8) (f 9) s1
    (keep1 _ _ (Or.inl (separate _ _ s1)) l1)
  intro m2 c2 o2 d1 keep2
  apply run_output_limb post c2 found 2 argument (f 10) (f 11) (f 12) (f 13) (f 14) s2
    (keep2 _ _ (Or.inl (separate _ _ s2)) (keep1 _ _ (Or.inl (separate _ _ s2)) l2))
  intro m3 c3 o3 d2 keep3
  apply run_output_limb post c3 found 3 argument (f 15) (f 16) (f 17) (f 18) (f 19) s3
    (keep3 _ _ (Or.inl (separate _ _ s3)) (keep2 _ _ (Or.inl (separate _ _ s3))
      (keep1 _ _ (Or.inl (separate _ _ s3)) l3)))
  intro m4 c4 o4 d3 keep4
  have self : { output with offset := output.offset } = output := by cases output; rfl
  simp only [show (0 : Fin 4).val = 0 from rfl, show (1 : Fin 4).val = 1 from rfl,
    show (2 : Fin 4).val = 2 from rfl, show (3 : Fin 4).val = 3 from rfl, Nat.reduceMul, Nat.add_zero]
    at d0 d1 d2 d3 keep2 keep3 keep4
  rw [self] at d0
  have e0 : read m4 output 8 1 = .ok (numberBytes w0.toNat 8) :=
    keep4 _ _ (Or.inr (Or.inl (by omega))) (keep3 _ _ (Or.inr (Or.inl (by omega)))
      (keep2 _ _ (Or.inr (Or.inl (by omega))) d0))
  have e1 := keep4 _ _ (Or.inr (Or.inl (by simp))) (keep3 _ _ (Or.inr (Or.inl (by simp))) d1)
  have e2 := keep4 _ _ (Or.inr (Or.inl (by simp))) d2
  refine ⟨1, leaveFrame frame m4, [], ?_, ?_⟩
  · rw [run]
    simp [found, f 20, step, returns, leaveFrame, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · apply output_result_of_storage original current m4 inputs output expected frame originalCall c4 owned
      state.caller ((output_value_of_limb_reads m4 output w0 w1 w2 w3 e0 e1 e2 d3).trans value)
    · apply output_readable_of_limbs m4 output (c4.1.2.2 (wordView output) (by simp))
      intro i
      obtain ⟨i, bound⟩ := i
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl
      · exact ⟨_, by simpa using e0⟩
      · exact ⟨_, e1⟩
      · exact ⟨_, e2⟩
      · exact ⟨_, d3⟩
    · intro id offset outside
      rw [o4 id offset outside, o3 id offset outside, o2 id offset outside, o1 id offset outside]

set_option hygiene false in
/-- Execute one instruction of a binary `left right output` method over private
    word locals. Expects `post state enteredWF homes found call` in scope. -/
macro "private_word_step" : tactic => `(tactic| first
  | (apply PrivateWords.run_store post state enteredWF homes found (by rfl) (by rfl)
     intro current state)
  | apply PrivateWords.run_load post state found (by rfl) (by rfl)
  | apply PrivateWords.run_field post state call found _ (by simp) 0 (by rfl)
  | apply PrivateWords.run_field post state call found _ (by simp) 1 (by rfl)
  | apply PrivateWords.run_field post state call found _ (by simp) 2 (by rfl)
  | apply PrivateWords.run_field post state call found _ (by simp) 3 (by rfl)
  | (have fl := state.call.input_formed (reference := left) (by simp)
     have fr := state.call.input_formed (reference := right) (by simp)
     have fo := state.call.output_formed (reference := output) (by simp)
     apply run_next_exists post found (by rfl)
     · simp [step, binaryArguments, checkedValue, numericValue, formValue, fl, fr, fo, pureArity, scalars,
         CIL.step.eq_def, CIL.binary, CIL.unary, instruction, memoryInstruction,
         checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
       try exact ⟨rfl, rfl, rfl, rfl⟩))

#print axioms PrivateWords.finish_words
#print axioms writable_of_word_homes
#print axioms PrivateWords.run_store
#print axioms PrivateWords.run_load
#print axioms PrivateWords.run_field
#print axioms run_output_limb
end UInt256Model.Safety
