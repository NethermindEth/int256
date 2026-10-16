import UInt256.Methods.Bitwise.ScalarSafetyContract
import UInt256.VectorRepresentation
namespace UInt256Proof.Bitwise.Early
open CIL.Safety UInt256Model.Safety UInt256Model.Bitwise

theorem read_pair (program : CIL.Program) (index pc fuel : Nat) (body : CIL.Method)
    (found : program[index]? = some body) (limb : Fin 4)
    (h0 : body.code[pc]? = some (.arg 0))
    (h1 : body.code[pc + 1]? = some (.fieldAt (8 * limb.val) 8))
    (h2 : body.code[pc + 2]? = some (.arg 1))
    (h3 : body.code[pc + 3]? = some (.fieldAt (8 * limb.val) 8))
    (memory : Memory) (left right output : Reference) (frame : Frame) (rest : List Value)
    (call : CallingConditions program memory [left, right] [output]) :
    run program (fuel + 4) index pc (binaryArguments left right output) frame rest memory =
      run program fuel index (pc + 4) (binaryArguments left right output) frame
        (.scalar (.i64 (inputLimb memory right limb)) ::
         .scalar (.i64 (inputLimb memory left limb)) :: rest) memory := by
  have leftFormed := call.input_formed (reference := left) (by simp)
  have rightFormed := call.input_formed (reference := right) (by simp)
  have leftField := call.input_field_instruction (reference := left) (by simp) limb
  have rightField := call.input_field_instruction (reference := right) (by simp) limb
  apply Eq.trans
  · apply run_next (target := pc + 1) (nextFrame := frame) (updated := memory)
      (values := .reference (.address left) :: rest) found h0
    bitwise_step_simp leftFormed
  apply Eq.trans
  · apply run_next (target := pc + 2) (nextFrame := frame) (updated := memory)
      (values := .scalar (.i64 (inputLimb memory left limb)) :: rest) found h1
    bitwise_step_simp leftField
  apply Eq.trans
  · apply run_next (target := pc + 3) (nextFrame := frame) (updated := memory)
      (values := .reference (.address right) :: .scalar (.i64 (inputLimb memory left limb)) :: rest) found h2
    bitwise_step_simp rightFormed
  apply Eq.trans
  · apply run_next (target := pc + 4) (nextFrame := frame) (updated := memory)
      (values := .scalar (.i64 (inputLimb memory right limb)) ::
        .scalar (.i64 (inputLimb memory left limb)) :: rest) found h3
    bitwise_step_simp rightField
  rfl

theorem input_limb_preserved {program : CIL.Program} {before after : Memory}
    {inputs : List Reference} {output input : Reference}
    (call : CallingConditions program before inputs [output]) (member : input ∈ inputs)
    (disjoint : output.allocation ≠ input.allocation)
    (outside : ∀ id, id < before.nextIdentity → ∀ offset, OutsideOutput output id offset →
      after.cells id offset = before.cells id offset) (limb : Fin 4) :
    inputLimb after input limb = inputLimb before input limb := by
  obtain ⟨allocation, present, _, _⟩ := formed_reference_live _ _ _ (call.input_formed member)
  have bound := (call.1.1.1 _ _ present).1
  have cells : (fun offset => (after.cells input.allocation offset).bits) =
      (fun offset => (before.cells input.allocation offset).bits) := by
    funext offset
    rw [outside input.allocation bound offset (Or.inl (Ne.symm disjoint))]
  simp only [inputLimb, cells]

#print axioms read_pair
#print axioms input_limb_preserved

theorem store_limb {program : CIL.Program} {memory : Memory} {inputs : List Reference}
    {output : Reference} (call : CallingConditions program memory inputs [output])
    (limb : Fin 4) (word : BitVec 64) (rest : List Value) :
    ∃ stored,
      instruction .store64 (.scalar (.i64 word) ::
        .reference (.address { output with offset := output.offset + 8 * limb.val }) :: rest) memory =
          .ok (stored, rest) ∧
      CallingConditions program stored inputs [output] ∧
      (∀ id offset, OutsideOutput output id offset → stored.cells id offset = memory.cells id offset) ∧
      read stored { output with offset := output.offset + 8 * limb.val } 8 1 =
        .ok (numberBytes word.toNat 8) ∧
      (∀ other : Fin 4, other ≠ limb → ∀ bytes,
        read memory { output with offset := output.offset + 8 * other.val } 8 1 = .ok bytes →
        read stored { output with offset := output.offset + 8 * other.val } 8 1 = .ok bytes) := by
  have length : (numberBytes word.toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨stored, written, storedCall, outside, readback⟩ :=
    call.write_output_slice (by simp : output ∈ [output]) (8 * limb.val) (numberBytes word.toNat 8)
      (by rw [length]; decide) (by rw [length]; omega)
  refine ⟨stored, ?_, storedCall, outside, ?_, ?_⟩
  · simp [instruction, storeValue, referenceAt, ordinaryAccessAlignment, written, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · simpa only [length] using readback
  · intro other distinct bytes readable
    apply write_preserves_disjoint_read written readable
    have different : other.val ≠ limb.val := fun equal => distinct (Fin.ext equal)
    simp only [length]
    omega

#print axioms store_limb
end UInt256Proof.Bitwise.Early
namespace UInt256Proof.Bitwise.Early
open CIL.Safety UInt256Model.Safety UInt256Proof.ConstructorSafety
theorem first_limb (memory : Memory) (output : Reference) (word : BitVec 64)
    (wf : memory.WellFormed)
    (loaded : read memory output 32 1 = .ok (numberBytes (UInt256Proof.ConstructorSafety.packed word 0 0 0).toNat 32)) :
    read memory output 8 1 = .ok (numberBytes word.toNat 8) := by
  have slice := read_slice_bytes wf loaded 0 8 (by decide) (by decide)
  have bound : word.toNat < 2^256 := Nat.lt_trans word.isLt (by decide)
  simpa [UInt256Proof.ConstructorSafety.packed, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound,
    numberBytes, ← List.map_take, List.take_range] using slice

#print axioms first_limb
theorem encoded_limbs (memory : Memory) (output : Reference) (w0 w1 w2 w3 : BitVec 64)
    (writable : access memory output 32 1 true = .ok ())
    (r0 : read memory output 8 1 = .ok (numberBytes w0.toNat 8))
    (r1 : read memory {output with offset := output.offset + 8} 8 1 = .ok (numberBytes w1.toNat 8))
    (r2 : read memory {output with offset := output.offset + 16} 8 1 = .ok (numberBytes w2.toNat 8))
    (r3 : read memory {output with offset := output.offset + 24} 8 1 = .ok (numberBytes w3.toNat 8)) :
    read memory output 32 1 = .ok (numberBytes (packed w0 w1 w2 w3).toNat 32) := by
  have value := output_value_of_limb_reads memory output w0 w1 w2 w3 r0 r1 r2 r3
  obtain ⟨bytes, loaded⟩ := output_readable_of_limbs memory output writable (by
    intro i
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> first | exact ⟨_, r0⟩ | exact ⟨_, r1⟩ | exact ⟨_, r2⟩ | exact ⟨_, r3⟩)
  have length : bytes.length = 32 := by rw [read_result_snapshot loaded]; simp
  have decoded := (output_snapshot_value memory output bytes loaded).trans value
  have roundtrip := vector256_bytes_roundtrip bytes length
  rw [decoded] at roundtrip
  change read memory output 32 1 = .ok (numberBytes (BitVec.ofNat 256 (w0.toNat + w1.toNat * 2^64 + w2.toNat * 2^128 + w3.toNat * 2^192)).toNat 32)
  rw [roundtrip]
  exact loaded

end UInt256Proof.Bitwise.Early
namespace UInt256Proof.Bitwise.Early
open CIL.Safety UInt256Model.Safety UInt256Proof.ConstructorSafety

def StoreContract (program : CIL.Program) (index : Nat) (original : Memory)
    (inputs : List Reference) (output : Reference) (args : List Value) (frame : Frame)
    (words : Fin 4 → BitVec 64) (pc : Nat → Nat) : Prop :=
  ∀ limb : Fin 4, 0 < limb.val → ∀ memory,
    CallingConditions program memory inputs [output] →
    (∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset → memory.cells id offset = original.cells id offset) →
    ∃ stored,
      CallingConditions program stored inputs [output] ∧
      (∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset → stored.cells id offset = original.cells id offset) ∧
      read stored {output with offset := output.offset + 8 * limb.val} 8 1 = .ok (numberBytes (words limb).toNat 8) ∧
      (∀ other : Fin 4, other ≠ limb → ∀ bytes,
        read memory {output with offset := output.offset + 8 * other.val} 8 1 = .ok bytes →
        read stored {output with offset := output.offset + 8 * other.val} 8 1 = .ok bytes) ∧
      ∀ final values, (∃ fuel, run program fuel index (pc (limb.val + 1)) args frame [] stored = .ok (final, values)) →
        ∃ fuel, run program fuel index (pc limb.val) args frame [] memory = .ok (final, values)

theorem finish_stores (program : CIL.Program) (index : Nat) (original initial : Memory)
    (inputs : List Reference) (output : Reference) (args : List Value) (frame : Frame)
    (words : Fin 4 → BitVec 64) (pc : Nat → Nat)
    (call : CallingConditions program initial inputs [output])
    (outside : ∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset → initial.cells id offset = original.cells id offset)
    (r0 : read initial output 8 1 = .ok (numberBytes (words 0).toNat 8))
    (store : StoreContract program index original inputs output args frame words pc) :
    ∃ stored,
      CallingConditions program stored inputs [output] ∧
      (∀ id, id < original.nextIdentity → ∀ offset, OutsideOutput output id offset → stored.cells id offset = original.cells id offset) ∧
      read stored output 32 1 = .ok (numberBytes (packed (words 0) (words 1) (words 2) (words 3)).toNat 32) ∧
      ∀ final values, (∃ fuel, run program fuel index (pc 4) args frame [] stored = .ok (final, values)) →
        ∃ fuel, run program fuel index (pc 1) args frame [] initial = .ok (final, values) := by
  obtain ⟨m1, c1, o1, r1, keep1, run1⟩ := store 1 (by decide) initial call outside
  have r01 := keep1 0 (by decide) _ r0
  obtain ⟨m2, c2, o2, r2, keep2, run2⟩ := store 2 (by decide) m1 c1 o1
  have r02 := keep2 0 (by decide) _ r01
  have r12 := keep2 1 (by decide) _ r1
  obtain ⟨m3, c3, o3, r3, keep3, run3⟩ := store 3 (by decide) m2 c2 o2
  have r03 := keep3 0 (by decide) _ r02
  have r13 := keep3 1 (by decide) _ r12
  have r23 := keep3 2 (by decide) _ r2
  refine ⟨m3, c3, o3, encoded_limbs m3 output _ _ _ _ (c3.1.2.2 (wordView output) (by simp)) r03 r13 r23 r3, ?_⟩
  intro final values continuation
  exact run1 final values (run2 final values (run3 final values continuation))

#print axioms finish_stores
end UInt256Proof.Bitwise.Early

