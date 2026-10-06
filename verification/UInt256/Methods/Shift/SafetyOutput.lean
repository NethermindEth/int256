import UInt256.Methods.Shift.SafetyPrepared

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety

def outputWords (direction : Direction) (whole : Fin 4) (words : Fin 4 → BitVec 64)
    (mask complement : BitVec 32) : List (BitVec 64) :=
  let n := (mask &&& 63).toNat % 64
  let c := (complement &&& 63).toNat % 64
  match direction with
  | .left =>
    let low := words 0 <<< n
    let join := fun (i j : Fin 4) => (words i <<< n) ||| ((words j >>> 1) >>> c)
    match whole.val with
    | 0 => [low, join 1 0, join 2 1, join 3 2]
    | 1 => [0, low, join 1 0, join 2 1]
    | 2 => [0, 0, low, join 1 0]
    | _ => [0, 0, 0, low]
  | .right =>
    let high := words 3 >>> n
    let join := fun (i j : Fin 4) => (words i >>> n) ||| ((words j <<< 1) <<< c)
    match whole.val with
    | 0 => [join 0 1, join 1 2, join 2 3, high]
    | 1 => [join 1 2, join 2 3, high, 0]
    | 2 => [join 2 3, high, 0, 0]
    | _ => [high, 0, 0, 0]

def outputStart (whole : Fin 4) : Nat :=
  match whole.val with | 0 => shiftPc 41 | 1 => shiftPc 91 | 2 => shiftPc 130 | _ => shiftPc 155

def outputCall (whole : Fin 4) : Nat :=
  match whole.val with | 0 => shiftPc 86 | 1 => shiftPc 125 | 2 => shiftPc 153 | _ => shiftPc 167

/-- Each nonzero-result route computes the actual store arguments from private
    snapshots, without re-reading or changing any caller bytes. -/
theorem shift_output_arguments (whole : Fin 4) (memory : Memory) (frame : Frame)
    (args : List Value) (output : Reference) (mask complement : BitVec 32)
    (maskHome complementHome : Reference) (homes : Fin 4 → Reference) (words : Fin 4 → BitVec 64)
    (argument : args[2]? = some (.reference (.address output)))
    (formed : form memory output = .ok output)
    (maskSlot : frame.locals[1]? = some (.bytes .word32 maskHome))
    (complementSlot : frame.locals[2]? = some (.bytes .word32 complementHome))
    (maskRead : read memory maskHome 4 1 = .ok (numberBytes mask.toNat 4))
    (complementRead : read memory complementHome 4 1 = .ok (numberBytes complement.toNat 4))
    (slots : ∀ i : Fin 4, frame.locals[3 + i.val]? = some (.bytes .word64 (homes i)))
    (reads : ∀ i : Fin 4, read memory (homes i) 8 1 = .ok (numberBytes (words i).toNat 8))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run Extracted.program fuel shiftIndex (outputCall whole) args frame
        ((outputWords shiftDirection whole words mask complement).reverse.map (fun w => .scalar (.i64 w)) ++
          [.reference (.address output)]) memory = .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel shiftIndex (outputStart whole) args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  have loadMask := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := shiftBody) (args := args) (pc := pc) (stack := stack)
    .word32 (.i32 mask) mask.toNat rfl maskSlot maskRead
  have loadComplement := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := shiftBody) (args := args) (pc := pc) (stack := stack)
    .word32 (.i32 complement) complement.toNat rfl complementSlot complementRead
  have loadWord := fun (i : Fin 4) (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := shiftBody) (args := args) (pc := pc) (stack := stack)
    .word64 (.i64 (words i)) (words i).toNat rfl (slots i) (reads i)
  have found : Extracted.program[shiftIndex]? = some shiftBody := by rfl
  have cases : whole = 0 ∨ whole = 1 ∨ whole = 2 ∨ whole = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  all_goals
    simp only [outputStart, outputCall, outputWords, shiftDirection, shiftBody, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.append_assoc, List.cons_append, List.map_cons, List.map_nil] at continuation ⊢
    repeat'
      first
      | exact continuation
      | apply run_next_exists post found (by rfl)
        first
        | exact loadMask _ _
        | exact loadComplement _ _
        | exact loadWord 0 _ _
        | exact loadWord 1 _ _
        | exact loadWord 2 _ _
        | exact loadWord 3 _ _
        | (simp (config := { implicitDefEqProofs := false })
            [step, argument, checkedValue, formValue, formed, numericValue, pureArity, scalars,
              CIL.step, CIL.binary, Bind.bind, Except.bind, Pure.pure, Except.pure]
           first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

#print axioms shift_output_arguments

/-- The bounded whole-limb count selects exactly its checked output route. -/
theorem shift_output_dispatch (whole : Fin 4) (memory : Memory) (frame : Frame)
    (args : List Value) (home : Reference)
    (slot : frame.locals[0]? = some (.bytes .word32 home))
    (loaded : read memory home 4 1 = .ok (numberBytes whole.val 4))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run Extracted.program fuel shiftIndex (outputStart whole) args frame [] memory =
        .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel shiftIndex (shiftPc 39) args frame [] memory =
        .ok (final, returned) ∧ post final returned := by
  have fits : localNumber .word32 (.i32 (BitVec.ofNat 32 whole.val)) = .ok whole.val := by
    simp [localNumber, Nat.mod_eq_of_lt (show whole.val < 2^32 by omega)]
  have load := fun (pc : Nat) (stack : List Value) => step_load_numeric_local
    (body := shiftBody) (args := args) (pc := pc) (stack := stack)
    .word32 (.i32 (BitVec.ofNat 32 whole.val)) whole.val fits slot loaded
  have cases : whole = 0 ∨ whole = 1 ∨ whole = 2 ∨ whole = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  all_goals
    have found : Extracted.program[shiftIndex]? = some shiftBody := by rfl
    simp only [outputStart] at continuation
    repeat'
      first
      | exact continuation
      | apply run_next_exists post found (by rfl)
        first
        | exact load _ _
        | (simp (config := { implicitDefEqProofs := false })
            [step, checkedValue, numericValue, pureArity, scalars, CIL.step, CIL.binary,
              Bind.bind, Except.bind, Pure.pure, Except.pure]
           first | rfl | exact ⟨rfl, rfl, rfl, rfl⟩)

#print axioms shift_output_dispatch
end UInt256Proof.Shift.Safety
