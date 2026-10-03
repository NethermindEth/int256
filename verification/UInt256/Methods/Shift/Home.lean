import CIL.AggregateMemory
import UInt256.Methods.Shift.Representation

open CIL UInt256Model

namespace UInt256Proof.Shift

@[simp↓] theorem eval_init_home (memory : Memory) (frame kind index : Nat) (rest : List Value) :
    evalMemory .init256 (.ref (.home frame kind index 0) :: rest) memory =
      some (writeAggregate memory frame kind index (0 : BitVec 256), rest) := by rfl

@[simp↓] theorem eval_store_home (memory : Memory) (frame kind index : Nat)
    (bits : BitVec 256) (rest : List Value) :
    evalMemory .store256 (.v256 bits :: .ref (.home frame kind index 0) :: rest) memory =
      some (writeAggregate memory frame kind index bits, rest) := by rfl

@[simp] theorem writeAggregate_caller (memory : Memory) (frame kind index address : Nat)
    (bits : BitVec 256) :
    writeAggregate memory frame kind index bits (.byte address) = memory (.byte address) := by
  exact writeHomeBytes_caller memory frame kind index 0 bits.toNat 32 address

theorem readAggregate_four_words (memory : Memory) (frame kind index : Nat) (r0 r1 r2 r3 : W64) :
    readAggregate (storeHomeWords memory frame kind index r0 r1 r2 r3) frame kind index =
      some (.v256 (pack r0 r1 r2 r3)) := by
  rw [readAggregate_storeHomeWords]
  have representation := pack_value
    (fun i => if i.val = 0 then r0 else if i.val = 1 then r1 else if i.val = 2 then r2 else r3)
  simp only [value, Fin.val_zero, Fin.val_one, Fin.val_two,
    show (3 : Fin 4).val = 3 from rfl, Nat.reduceEqDiff, ↓reduceIte] at representation
  rw [representation]

theorem storeHomeWords_caller (memory : Memory) (frame kind index : Nat)
    (r0 r1 r2 r3 : W64) (address : Nat) :
    storeHomeWords memory frame kind index r0 r1 r2 r3 (.byte address) = memory (.byte address) := by
  simp only [storeHomeWords, writeHomeBytes_caller]

end UInt256Proof.Shift
