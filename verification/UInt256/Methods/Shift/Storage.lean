import UInt256.ExecutionAutomation
import UInt256.VectorRepresentation
import UInt256.Methods.Shift.Home

open Lean Meta Elab Tactic CIL UInt256Model UInt256Proof
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof.Shift

@[simp↓] theorem eval_create256 (r0 r1 r2 r3 : W64) :
    evalIntrinsic (.vector (.create64 256)) [.i64 r0, .i64 r1, .i64 r2, .i64 r3] =
      some (.v256 (CIL.Vector.pack256 r0 r1 r2 r3)) := by rfl

@[simp↓] theorem eval_store256 (memory : Memory) (out : Nat) (r0 r1 r2 r3 : W64)
    (rest : List Value) :
    evalMemory .store256 (.v256 (CIL.Vector.pack256 r0 r1 r2 r3) :: .ref (.byte out) :: rest) memory =
      some (store4 memory out r0 r1 r2 r3, rest) := by
  simp only [evalMemory, write256_four_limbs, bind, pure, Option.bind]

if_extracted Extracted.storeLimbsIndex {
theorem execute_shift_store_contract (memory : Memory) (frame fuel out : Nat)
    (r0 r1 r2 r3 : W64) (bound : Extracted.storeLimbsBody.code.length + 1 ≤ fuel) :
    ∃ final, run Extracted.program fuel Extracted.storeLimbsIndex 0
      [.object out, .i64 r0, .i64 r1, .i64 r2, .i64 r3] frame [] memory = some (final, []) ∧
      (∀ address, final (.byte address) = store4 memory out r0 r1 r2 r3 (.byte address)) ∧
      ∀ other index, other ≠ frame → final (.local other index) = memory (.local other index) := by
  have splitFuel : fuel = (fuel - (Extracted.storeLimbsBody.code.length + 1)) +
      (Extracted.storeLimbsBody.code.length + 1) := by omega
  rw [splitFuel]
  generalize fuel - (Extracted.storeLimbsBody.code.length + 1) = remaining
  have h8 : (0 : Int) ≤ (out : Int) + 8 := by omega
  have h16 : (0 : Int) ≤ (out : Int) + 16 := by omega
  have h24 : (0 : Int) ≤ (out : Int) + 24 := by omega
  have ha8 : ((out : Int) + 8).toNat = out + 8 := by omega
  have ha16 : ((out : Int) + 16).toNat = out + 16 := by omega
  have ha24 : ((out : Int) + 24).toNat = out + 24 := by omega
  simp only [cil_code, Nat.add_succ, Nat.add_zero]
  cil_steps evalMemory, eval_create256, eval_store256, unsafeAsRef, unsafeAdd, offsetValue,
    h8, h16, h24, ha8, ha16, ha24
  all_goals simp [store4]
  all_goals intro address
  all_goals rfl
}

if_extracted Extracted.storeLimbsIndex {
theorem execute_shift_store_home (memory : Memory) (frame fuel homeFrame kind index : Nat)
    (r0 r1 r2 r3 : W64) (bound : Extracted.storeLimbsBody.code.length + 1 ≤ fuel) :
    ∃ final, run Extracted.program fuel Extracted.storeLimbsIndex 0
      [.ref (.home homeFrame kind index 0), .i64 r0, .i64 r1, .i64 r2, .i64 r3]
      frame [] memory = some (final, []) ∧
      readAggregate final homeFrame kind index = some (.v256 (pack r0 r1 r2 r3)) ∧
      ∀ address, final (.byte address) = memory (.byte address) := by
  have splitFuel : fuel = (fuel - (Extracted.storeLimbsBody.code.length + 1)) +
      (Extracted.storeLimbsBody.code.length + 1) := by omega
  rw [splitFuel]
  generalize fuel - (Extracted.storeLimbsBody.code.length + 1) = remaining
  simp only [cil_code, Nat.add_succ, Nat.add_zero]
  cil_steps evalMemory, eval_create256, eval_store_home, unsafeAsRef, unsafeAdd, offsetValue
  all_goals first
    | exact readAggregate_four_words memory homeFrame kind index r0 r1 r2 r3
    | simp only [pack_vector]
}

elab "cil_shift_store_call" : tactic => withMainContext do
  let (call, values) ← provedCall `Extracted.storeLimbsIndex
    `UInt256Proof.Shift.execute_shift_store_contract "shift storage" 5
  let out ← PrettyPrinter.delab (← constructorArg ``CIL.Value.object values[0]!)
  let mut words : Array Term := #[]
  for value in values[1:] do
    words := words.push (← PrettyPrinter.delab (← constructorArg ``CIL.Value.i64 value))
  let memory ← PrettyPrinter.delab call[7]!
  let frame ← PrettyPrinter.delab call[5]!
  let fuel ← PrettyPrinter.delab call[1]!
  let final := mkIdent (← mkFreshUserName `storedMemory)
  let run := mkIdent (← mkFreshUserName `storeRun)
  let bytes := mkIdent (← mkFreshUserName `storeBytes)
  let locals := mkIdent (← mkFreshUserName `storeLocals)
  let r0 := words[0]!
  let r1 := words[1]!
  let r2 := words[2]!
  let r3 := words[3]!
  evalTactic (← `(tactic|
    obtain ⟨$final:ident, $run:ident, $bytes:ident, $locals:ident⟩ :=
      execute_shift_store_contract $memory $frame $fuel $out $r0 $r1 $r2 $r3
        (by simp [cil_code]; all_goals omega)))
  rewriteHelperRun run

elab "cil_shift_store_home_call" : tactic => withMainContext do
  let (call, values) ← provedCall `Extracted.storeLimbsIndex
    `UInt256Proof.Shift.execute_shift_store_home "shift private storage" 5
  let address ← whnf (← constructorArg ``CIL.Value.ref values[0]!)
  unless address.isAppOfArity ``CIL.Address.home 4 do
    throwError "Private storage requires an aggregate home"
  let fields := address.getAppArgs
  unless ← isDefEq fields[3]! (mkNatLit 0) do
    throwError "Private storage requires the beginning of the aggregate home"
  let homeFrame ← PrettyPrinter.delab fields[0]!
  let kind ← PrettyPrinter.delab fields[1]!
  let index ← PrettyPrinter.delab fields[2]!
  let mut words : Array Term := #[]
  for value in values[1:] do
    words := words.push (← PrettyPrinter.delab (← constructorArg ``CIL.Value.i64 value))
  let memory ← PrettyPrinter.delab call[7]!
  let frame ← PrettyPrinter.delab call[5]!
  let fuel ← PrettyPrinter.delab call[1]!
  let final := mkIdent (← mkFreshUserName `storedHome)
  let run := mkIdent (← mkFreshUserName `storeHomeRun)
  let aggregate := mkIdent (← mkFreshUserName `storeHomeSnapshot)
  let bytes := mkIdent (← mkFreshUserName `storeHomeBytes)
  let r0 := words[0]!
  let r1 := words[1]!
  let r2 := words[2]!
  let r3 := words[3]!
  evalTactic (← `(tactic|
    obtain ⟨$final:ident, $run:ident, $aggregate:ident, $bytes:ident⟩ :=
      execute_shift_store_home $memory $frame $fuel $homeFrame $kind $index $r0 $r1 $r2 $r3
        (by simp [cil_code]; all_goals omega)))
  rewriteHelperRun run

end UInt256Proof.Shift
