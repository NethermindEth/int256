import CIL.StepEquations
import CIL.Safety.Equations
import UInt256.Methods.Shift.ScalarCount
import UInt256.Methods.Shift.ValueOutputs
import UInt256.Methods.Shift.Count
import CIL.SymbolicExecution
import CIL.Safety.ReturnMemory

set_option maxHeartbeats 1000000

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

def outputCall (whole : Fin 4) : Nat :=
  match whole.val with | 0 => 86 | 1 => 125 | 2 => 153 | _ => 167

variable {profile : CIL.FeatureProfile} {direction : Direction} {storage : Nat}
  {program : CIL.Program} {index : Nat}
  (bodyFound : program[index]? = some (scalarBody profile direction storage))
include bodyFound
/-- Each nonzero-result route selected by the whole-limb count computes the actual store
    arguments from the private snapshots, without re-reading or changing any caller byte. -/
theorem shift_output_arguments (whole : Fin 4) (original entered memory : Memory)
    (input output : Reference) (frame : Frame) (args : List Value) (count : BitVec 32)
    (words : Fin 4 → BitVec 64) (known : Nat → Option CIL.Value)
    (argument : args[2]? = some (.reference (.address output)))
    (state : VectorFrame program original entered memory [input] output frame
      (preparedLocals known count words) none)
    (wholeKnown : known 0 = some (.i32 (BitVec.ofNat 32 whole.val)))
    (post : Memory → List Value → Prop)
    (continuation : ∃ fuel final returned,
      run program fuel index (outputCall whole) args frame
        ((outputWords direction whole words (count &&& 63) (63 - (count &&& 63))).reverse.map
          (fun w => .scalar (.i64 w)) ++ [.reference (.address output)]) memory =
        .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run program fuel index 39 args frame [] memory = .ok (final, returned) ∧
        post final returned := by
  have formed := state.call.output_formed (by simp : output ∈ [output])
  have found := bodyFound
  have cases : whole = 0 ∨ whole = 1 ∨ whole = 2 ∨ whole = 3 := by omega
  cases direction <;> rcases cases with rfl | rfl | rfl | rfl
  all_goals
    simp only [outputCall, outputWords, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.map_cons, List.map_nil] at continuation
    cil_contract_steps (snapshots := state.locals) [argument, formed, preparedLocals,
      wholeKnown] until continuation
end UInt256Proof.Shift.Safety

set_option maxHeartbeats 1000000

namespace UInt256Proof.Shift.Safety

def shiftValue (direction : Direction) (word : BitVec 256) (count : Nat) : BitVec 256 :=
  match direction with
  | .left => word <<< count
  | .right => word >>> count
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

end UInt256Proof.Shift.Safety
