import Extracted
import UInt256.StorageLemmas
import UInt256.Arithmetic.Carry

open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace UInt256Proof

theorem execute_store (m : Memory) (out frame fuel : Nat) (r0 r1 r2 r3 : W64) :
    run Extracted.program (fuel + 40) 4 0
      [.object out, .i64 r0, .i64 r1, .i64 r2, .i64 r3] frame [] m =
        some (store4 m out r0 r1 r2 r3, []) := by
  rfl

theorem execute_store_result (initial : Bytes) (m : Memory)
    (h : ∀ address, m (.byte address) = byteMemory initial (.byte address))
    (out frame fuel : Nat) (r0 r1 r2 r3 : W64) :
    ∃ final, run Extracted.program (fuel + 40) 4 0
      [.object out, .i64 r0, .i64 r1, .i64 r2, .i64 r3] frame [] m = some (final, []) ∧
      ∀ address, final (.byte address) = (writeBytes (byteMemory initial) out
        (value (fun i => if i.val = 0 then r0 else if i.val = 1 then r1 else
          if i.val = 2 then r2 else r3)).toNat 32) (.byte address) := by
  refine ⟨store4 m out r0 r1 r2 r3, execute_store m out frame fuel r0 r1 r2 r3, ?_⟩
  intro address
  rw [store4_bytes m (byteMemory initial) h out r0 r1 r2 r3 address, store4_value]

theorem execute_store_at (m : Memory) (out frame fuel : Nat) (r0 r1 r2 r3 : W64)
    (hf : 40 ≤ fuel) :
    run Extracted.program fuel 4 0
      [.object out, .i64 r0, .i64 r1, .i64 r2, .i64 r3] frame [] m =
        some (store4 m out r0 r1 r2 r3, []) := by
  have he : fuel = (fuel - 40) + 40 := by omega
  rw [he]
  exact execute_store m out frame (fuel - 40) r0 r1 r2 r3
theorem execute_small_no_carry (m : Memory) (base out frame fuel : Nat) (a : Limbs) (b : W64)
    (hr : ∀ i : Fin 4, read64 m (.byte (base + 8*i.val)) = some (.i64 (a i)))
    (hnc : ¬ a 0 + b < a 0) :
    ∃ final, run Extracted.program (fuel + 200) 2 0
      [.object base, .i64 b, .object out] frame [] m = some (final, [.i32 0]) ∧
      ∀ address, final (.byte address) = store4 m out (a 0 + b) (a 1) (a 2) (a 3) (.byte address) := by
  have hr0 := hr 0
  have hr1 := hr 1
  have hr2 := hr 2
  have hr3 := hr 3
  simp only [Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hr0 hr1
  change read64 m (.byte (base + 16)) = some (.i64 (a 2)) at hr2
  change read64 m (.byte (base + 24)) = some (.i64 (a 3)) at hr3
  repeat
    rw [run]
    simp [step, Extracted.program, Extracted.method2, Extracted.method4, binary, truth, write64, write_local_read_local,
      show (3 : Fin 4).val = 3 from rfl,
      initLocals, hr0, hr1, hr2, hr3, hnc]
  simp [store4]

theorem execute_small_carry1 (m : Memory) (base out frame fuel : Nat) (a : Limbs) (b : W64)
    (hr : ∀ i : Fin 4, read64 m (.byte (base + 8*i.val)) = some (.i64 (a i)))
    (hc : a 0 + b < a 0) (h1 : a 1 + 1 ≠ 0) :
    ∃ final, run Extracted.program (fuel + 200) 2 0
      [.object base, .i64 b, .object out] frame [] m = some (final, [.i32 0]) ∧
      ∀ address, final (.byte address) = store4 m out (a 0 + b) (a 1 + 1) (a 2) (a 3) (.byte address) := by
  have hr0 := hr 0
  have hr1 := hr 1
  have hr2 := hr 2
  have hr3 := hr 3
  simp only [Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hr0 hr1
  change read64 m (.byte (base + 16)) = some (.i64 (a 2)) at hr2
  change read64 m (.byte (base + 24)) = some (.i64 (a 3)) at hr3
  change a 1 + BitVec.ofNat 64 1 ≠ BitVec.ofNat 64 0 at h1
  repeat
    rw [run]
    simp [step, Extracted.program, Extracted.method2, Extracted.method4, binary, truth, write64, write_local_read_local,
      show (3 : Fin 4).val = 3 from rfl, initLocals, hr0, hr1, hr2, hr3, hc, h1]
  simp [store4]

theorem execute_small_carry2 (m : Memory) (base out frame fuel : Nat) (a : Limbs) (b : W64)
    (hr : ∀ i : Fin 4, read64 m (.byte (base + 8*i.val)) = some (.i64 (a i)))
    (hc : a 0 + b < a 0) (h1 : a 1 + 1 = 0) (h2 : a 2 + 1 ≠ 0) :
    ∃ final, run Extracted.program (fuel + 200) 2 0
      [.object base, .i64 b, .object out] frame [] m = some (final, [.i32 0]) ∧
      ∀ address, final (.byte address) = store4 m out (a 0 + b) 0 (a 2 + 1) (a 3) (.byte address) := by
  have hr0 := hr 0
  have hr1 := hr 1
  have hr2 := hr 2
  have hr3 := hr 3
  simp only [Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hr0 hr1
  change read64 m (.byte (base + 16)) = some (.i64 (a 2)) at hr2
  change read64 m (.byte (base + 24)) = some (.i64 (a 3)) at hr3
  change a 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 at h1
  change a 2 + BitVec.ofNat 64 1 ≠ BitVec.ofNat 64 0 at h2
  repeat
    rw [run]
    simp [step, Extracted.program, Extracted.method2, Extracted.method4, binary, truth, write64,
      write_local_read_local, show (3 : Fin 4).val = 3 from rfl,
      initLocals, hr0, hr1, hr2, hr3, hc, h1, h2]
  simp [store4]

theorem execute_small_carry3 (m : Memory) (base out frame fuel : Nat) (a : Limbs) (b : W64)
    (hr : ∀ i : Fin 4, read64 m (.byte (base + 8*i.val)) = some (.i64 (a i)))
    (hc : a 0 + b < a 0) (h1 : a 1 + 1 = 0) (h2 : a 2 + 1 = 0) (h3 : a 3 + 1 ≠ 0) :
    ∃ final, run Extracted.program (fuel + 200) 2 0
      [.object base, .i64 b, .object out] frame [] m = some (final, [.i32 0]) ∧
      ∀ address, final (.byte address) = store4 m out (a 0 + b) 0 0 (a 3 + 1) (.byte address) := by
  have hr0 := hr 0
  have hr1 := hr 1
  have hr2 := hr 2
  have hr3 := hr 3
  simp only [Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hr0 hr1
  change read64 m (.byte (base + 16)) = some (.i64 (a 2)) at hr2
  change read64 m (.byte (base + 24)) = some (.i64 (a 3)) at hr3
  change a 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 at h1
  change a 2 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 at h2
  change a 3 + BitVec.ofNat 64 1 ≠ BitVec.ofNat 64 0 at h3
  repeat
    rw [run]
    simp [step, Extracted.program, Extracted.method2, Extracted.method4, binary, truth, write64,
      write_local_read_local, show (3 : Fin 4).val = 3 from rfl,
      initLocals, hr0, hr1, hr2, hr3, hc, h1, h2, h3]
  simp [store4]

theorem execute_small_overflow (m : Memory) (base out frame fuel : Nat) (a : Limbs) (b : W64)
    (hr : ∀ i : Fin 4, read64 m (.byte (base + 8*i.val)) = some (.i64 (a i)))
    (hc : a 0 + b < a 0) (h1 : a 1 + 1 = 0) (h2 : a 2 + 1 = 0) (h3 : a 3 + 1 = 0) :
    ∃ final, run Extracted.program (fuel + 200) 2 0
      [.object base, .i64 b, .object out] frame [] m = some (final, [.i32 1]) ∧
      ∀ address, final (.byte address) = store4 m out (a 0 + b) 0 0 0 (.byte address) := by
  have hr0 := hr 0
  have hr1 := hr 1
  have hr2 := hr 2
  have hr3 := hr 3
  simp only [Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hr0 hr1
  change read64 m (.byte (base + 16)) = some (.i64 (a 2)) at hr2
  change read64 m (.byte (base + 24)) = some (.i64 (a 3)) at hr3
  change a 1 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 at h1
  change a 2 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 at h2
  change a 3 + BitVec.ofNat 64 1 = BitVec.ofNat 64 0 at h3
  repeat
    rw [run]
    simp [step, Extracted.program, Extracted.method2, Extracted.method4, binary, truth, write64,
      write_local_read_local, show (3 : Fin 4).val = 3 from rfl,
      initLocals, hr0, hr1, hr2, hr3, hc, h1, h2, h3]
  simp [store4]
theorem execute_carry (m : Memory) (frame fuel : Nat) (ca ra : Address) (x y c : W64)
    (h : m ca = some (.i64 c))
    (hc0 : ca ≠ .local frame 0) (hc1 : ca ≠ .local frame 1)
    (hca : ∃ f i, ca = .local f i) (hra : ∃ f i, ra = .local f i) :
    run Extracted.program (fuel + 40) 3 0 [.i64 x, .i64 y, .ref ca, .ref ra] frame [] m =
      some (write (write
        (write (write m (.local frame 0) (.i64 (x + y))) (.local frame 1) (.i64 (x + y + c)))
        ca (.i64 (carry x y c))) ra (.i64 (x + y + c)), []) := by
  rcases hca with ⟨cf, ci, rfl⟩
  rcases hra with ⟨rf, ri, rfl⟩
  have hc0' : ¬ (cf = frame ∧ ci = 0) := by simpa using hc0
  have hc1' : ¬ (frame = cf ∧ 1 = ci) := by
    rintro ⟨rfl, rfl⟩
    exact hc1 rfl
  simp only [Nat.add_succ, Nat.add_zero]
  repeat
    rw [run]
    simp [step, Extracted.program, Extracted.method3, binary, write, read64, write64, h, hc0', hc1']
  by_cases hxy : x + y < x <;> by_cases hrc : x + y + c < x + y
  all_goals simp only [carry, hxy, hrc, ↓reduceIte]; rfl

theorem execute_carry_at (m : Memory) (frame fuel : Nat) (ca ra : Address) (x y c : W64)
    (hf : 40 ≤ fuel) (h : m ca = some (.i64 c))
    (hc0 : ca ≠ .local frame 0) (hc1 : ca ≠ .local frame 1)
    (hca : ∃ f i, ca = .local f i) (hra : ∃ f i, ra = .local f i) :
    run Extracted.program fuel 3 0 [.i64 x, .i64 y, .ref ca, .ref ra] frame [] m =
      some (write (write
        (write (write m (.local frame 0) (.i64 (x + y))) (.local frame 1) (.i64 (x + y + c)))
        ca (.i64 (carry x y c))) ra (.i64 (x + y + c)), []) := by
  have he : fuel = (fuel - 40) + 40 := by omega
  rw [he]
  exact execute_carry m frame (fuel - 40) ca ra x y c h hc0 hc1 hca hra

def carryState (m : Memory) (frame index : Nat) (x y c : W64) : Memory :=
  write (write (write (write (initLocals m (frame+1) Extracted.method3.locals)
    (.local (frame+1) 0) (.i64 (x+y))) (.local (frame+1) 1) (.i64 (x+y+c)))
    (.local frame 2) (.i64 (carry x y c))) (.local frame index) (.i64 (x+y+c))

@[simp] theorem carryState_bytes (m : Memory) (frame index address : Nat) (x y c : W64) :
    carryState m frame index x y c (.byte address) = m (.byte address) := by
  simp [carryState, initLocals_bytes]

@[simp] theorem read64_carryState_byte (m : Memory) (frame index base : Nat) (x y c : W64) :
    read64 (carryState m frame index x y c) (.byte base) = read64 m (.byte base) := by
  simp [carryState]

theorem execute_parent_carry (m : Memory) (frame index fuel : Nat) (x y c : W64)
    (hf : 40 ≤ fuel) (h : m (.local frame 2) = some (.i64 c)) :
    run Extracted.program fuel 3 0
      [.i64 x, .i64 y, .ref (.local frame 2), .ref (.local frame index)] (frame+1) []
      (initLocals m (frame+1) Extracted.method3.locals) =
        some (carryState m frame index x y c, []) := by
  unfold carryState
  apply execute_carry_at
  · exact hf
  · simp [initLocals, Extracted.method3, write, h]
  · intro he
    have hn := Address.local.inj he
    omega
  · intro he
    have hn := Address.local.inj he
    omega
  · exact ⟨frame, 2, rfl⟩
  · exact ⟨frame, index, rfl⟩

@[simp] theorem carryState_carry (m : Memory) (frame index : Nat) (x y c : W64) (hn : index ≠ 2) :
    carryState m frame index x y c (.local frame 2) = some (.i64 (carry x y c)) := by
  simp [carryState, write_local_read_local, Ne.symm hn]

@[simp] theorem carryState_sum (m : Memory) (frame index : Nat) (x y c : W64) :
    carryState m frame index x y c (.local frame index) = some (.i64 (x+y+c)) := by
  simp [carryState, write_local_read_local]

@[simp] theorem carryState_other (m : Memory) (frame index other : Nat) (x y c : W64)
    (hi : other ≠ index) (hc : other ≠ 2) :
    carryState m frame index x y c (.local frame other) = m (.local frame other) := by
  simp [carryState, write_local_read_local, hi, hc, initLocals_other_frame]

end UInt256Proof
