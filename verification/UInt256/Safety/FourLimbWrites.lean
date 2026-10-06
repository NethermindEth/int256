import UInt256.Safety.OutputAccess
import CIL.Safety.AccessBelow

namespace UInt256Model.Safety

open CIL.Safety

/-- Four checked writes and their shared permission, footprint and readback facts.
    Execution proofs must still establish the actual instructions perform them. -/
theorem write_four_limbs (program : CIL.Program) (memory : Memory)
    (inputs : List Reference) (output : Reference) (w0 w1 w2 w3 : BitVec 64)
    (call : CallingConditions program memory inputs [output]) :
    ∃ m1 m2 m3 result,
      write memory output (numberBytes w0.toNat 8) 1 = .ok m1 ∧
      write m1 { output with offset := output.offset + 8 } (numberBytes w1.toNat 8) 1 = .ok m2 ∧
      write m2 { output with offset := output.offset + 16 } (numberBytes w2.toNat 8) 1 = .ok m3 ∧
      write m3 { output with offset := output.offset + 24 } (numberBytes w3.toNat 8) 1 = .ok result ∧
      CallingConditions program m1 inputs [output] ∧
      CallingConditions program m2 inputs [output] ∧
      CallingConditions program m3 inputs [output] ∧
      CallingConditions program result inputs [output] ∧
      (∀ id offset, OutsideOutput output id offset → result.cells id offset = memory.cells id offset) ∧
      AccessBelow memory.nextIdentity memory result ∧
      read result output 8 1 = .ok (numberBytes w0.toNat 8) ∧
      read result { output with offset := output.offset + 8 } 8 1 = .ok (numberBytes w1.toNat 8) ∧
      read result { output with offset := output.offset + 16 } 8 1 = .ok (numberBytes w2.toNat 8) ∧
      read result { output with offset := output.offset + 24 } 8 1 = .ok (numberBytes w3.toNat 8) := by
  have length (word : BitVec 64) : (numberBytes word.toNat 8).length = 8 := by simp [numberBytes]
  obtain ⟨m1, h0, c1, p0, r0⟩ := call.write_output_slice (output := output) (by simp) 0 (numberBytes w0.toNat 8)
    (by rw [length]; decide) (by rw [length]; decide)
  obtain ⟨m2, h1, c2, p1, r1⟩ := c1.write_output_slice (output := output) (by simp) 8 (numberBytes w1.toNat 8)
    (by rw [length]; decide) (by rw [length]; decide)
  obtain ⟨m3, h2, c3, p2, r2⟩ := c2.write_output_slice (output := output) (by simp) 16 (numberBytes w2.toNat 8)
    (by rw [length]; decide) (by rw [length]; decide)
  obtain ⟨m4, h3, c4, p3, r3⟩ := c3.write_output_slice (output := output) (by simp) 24 (numberBytes w3.toNat 8)
    (by rw [length]; decide) (by rw [length]; decide)
  simp only [Nat.add_zero] at h0
  refine ⟨m1, m2, m3, m4, h0, h1, h2, h3, c1, c2, c3, c4, ?_,
    (write_preserves_access_below h0 _).trans ((write_preserves_access_below h1 _).trans
      ((write_preserves_access_below h2 _).trans (write_preserves_access_below h3 _))), ?_⟩

  · intro id offset outside
    exact (p3 id offset outside).trans ((p2 id offset outside).trans
      ((p1 id offset outside).trans (p0 id offset outside)))

  · have keep0_1 := write_preserves_disjoint_read h1 r0 (Or.inr (Or.inl (by simp [length])))
    have keep0_2 := write_preserves_disjoint_read h2 keep0_1 (Or.inr (Or.inl (by simp [length])))
    have keep0_3 := write_preserves_disjoint_read h3 keep0_2 (Or.inr (Or.inl (by simp [length])))
    have keep1_2 := write_preserves_disjoint_read h2 r1 (Or.inr (Or.inl (by simp [length])))
    have keep1_3 := write_preserves_disjoint_read h3 keep1_2 (Or.inr (Or.inl (by simp [length])))
    have keep2_3 := write_preserves_disjoint_read h3 r2 (Or.inr (Or.inl (by simp [length])))
    simpa only [length, Nat.add_zero] using And.intro keep0_3 (And.intro keep1_3 (And.intro keep2_3 r3))

#print axioms write_four_limbs

end UInt256Model.Safety
