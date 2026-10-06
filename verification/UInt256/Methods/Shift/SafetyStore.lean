import UInt256.Methods.Shift.SafetyPrepared
import UInt256.Methods.Shift.ValueOutputs
import UInt256.Methods.Shift.Count
import UInt256.Methods.Add.StorageCall
import CIL.Safety.ReturnMemory

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

namespace UInt256Proof.Shift.Safety

/-- The values computed for the actual store call implement the independent
    256-bit left-shift operation, including cross-limb carry bits. -/
theorem shift_output_value (direction : Direction) (whole : Fin 4) (words : Fin 4 → BitVec 64) (count : BitVec 32) :
    let output := outputWords direction whole words (count &&& 63) (63 - (count &&& 63))
    pack (output.getD 0 0) (output.getD 1 0) (output.getD 2 0) (output.getD 3 0) =
      shiftValue direction (UInt256Model.value words) (64 * whole.val + count.toNat % 64) := by
  have masked : ((count &&& (63 : BitVec 32)) &&& 63).toNat % 64 = count.toNat % 64 := by
    rw [mask_count, mask_count]
    simp
  have complement : (((63 : BitVec 32) - (count &&& 63)) &&& 63).toNat % 64 =
      63 - count.toNat % 64 := by
    rw [mask_count, carry_count]
    have bound := Nat.mod_lt count.toNat (show 0 < 64 by decide)
    omega
  have bound := Nat.mod_lt count.toNat (show 0 < 64 by decide)
  have cases : whole = 0 ∨ whole = 1 ∨ whole = 2 ∨ whole = 3 := by omega
  cases direction <;> rcases cases with rfl | rfl | rfl | rfl
  all_goals
    simp only [outputWords, shiftValue, masked, complement, List.getD_cons_zero, List.getD_cons_succ,
      Fin.val_zero, Fin.val_one, Fin.val_two, CIL.fin_val_three, Nat.mul_zero, Nat.zero_add,
      Nat.mul_one, Nat.reduceMul]
  · exact left_pack_zero words _ bound
  · exact left_pack_one words _ bound
  · exact left_pack_two words _ bound
  · exact left_pack_three words _ bound

  · exact right_pack_zero words _ bound
  · exact right_pack_one words _ bound
  · exact right_pack_two words _ bound
  · exact right_pack_three words _ bound

#print axioms shift_output_value
end UInt256Proof.Shift.Safety

namespace UInt256Proof.Shift.Safety
open CIL.Safety UInt256Model.Safety UInt256Proof.Safety

/-- Invoke the current extracted storage helper and retire the parent frame;
    neither the helper nor its aliasing behavior is assumed. -/
theorem shift_store_return (whole : Fin 4) (memory : Memory) (inputs : List Reference)
    (frame : Frame) (args : List Value) (output : Reference) (boundary : Nat)
    (w0 w1 w2 w3 : BitVec 64)
    (call : CallingConditions Extracted.program memory inputs [output])
    (outputOld : output.allocation < boundary)
    (owned : ∀ id ∈ frame.owned, boundary ≤ id) :
    ∃ fuel final returned,
      run Extracted.program fuel shiftIndex (outputCall whole) args frame
        [.scalar (.i64 w3), .scalar (.i64 w2), .scalar (.i64 w1), .scalar (.i64 w0),
          .reference (.address output)] memory = .ok (final, returned) ∧
      returned = [] ∧ final.WellFormed ∧
      inputValue final output = BitVec.ofNat 256
        (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192) ∧
      access final output 32 1 true = .ok () ∧
      (∃ bytes, read final output 32 1 = .ok bytes) ∧
      (∀ id, id < boundary → ∀ offset, OutsideOutput output id offset →
        final.cells id offset = memory.cells id offset) := by
  have cases : whole = 0 ∨ whole = 1 ∨ whole = 2 ∨ whole = 3 := by omega
  have fetched : shiftBody.code[outputCall whole]? = some (.call Extracted.storeLimbsIndex 5) := by
    rcases cases with rfl | rfl | rfl | rfl <;> rfl
  have returned : shiftBody.code[outputCall whole + 1]? = some .ret := by
    rcases cases with rfl | rfl | rfl | rfl <;> rfl
  have found : Extracted.program[shiftIndex]? = some shiftBody := by rfl
  have returns : shiftBody.returnsValue = false := by rfl
  have formed := call.output_formed (by simp : output ∈ [output])
  apply run_store_limbs_readable inputs output w0 w1 w2 w3 _ found fetched
  · unfold UInt256Proof.Safety.storageArguments
    repeat' (conv in UInt256Proof.Safety.storageWordOrder => cbv)
    simp [List.range_succ, List.findIdx, List.findIdx.go, step, checkedValue, numericValue, formValue, formed, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ⟨rfl, rfl⟩
  · exact call
  · intro stored valid outside authority value readable
    have retained := leaveFrame_preserves_memory_below frame stored boundary owned
    have bytes : (fun offset => ((leaveFrame frame stored).cells output.allocation offset).bits) =
        (fun offset => (stored.cells output.allocation offset).bits) := by
      funext offset
      rw [retained.cells output.allocation outputOld offset]
    refine ⟨1, leaveFrame frame stored, [], ?_, rfl,
      leaveFrame_preserves_wellFormed _ _ valid.1.1, ?_,
      (retained.access output outputOld 32 1 true).trans
        (valid.1.2.2 (wordView output) (by simp)), ?_, ?_⟩
    · simp [run, found, returned, returns, step, Except.mapError,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    · simpa only [inputValue, bytes] using value
    · obtain ⟨snapshot, loaded⟩ := readable
      exact ⟨snapshot, (retained.read output outputOld 32 1).trans loaded⟩
    · intro id old offset untouched
      exact (retained.cells id old offset).trans (outside id offset untouched)

#print axioms shift_store_return
end UInt256Proof.Shift.Safety
