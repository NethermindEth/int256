import UInt256.Methods.Multiply.WordSoftwareUpper

namespace UInt256Proof.Multiply.Safety
open CIL.Safety

def partialProduct (a b : BitVec 64) (index : Fin 3) : BitVec 64 :=
  if index = 0 then softwareLower a b
  else if index = 1 then softwareMiddle a b else softwareUpper a b

def ProductHomes (memory : Memory) (frame : Frame) (a b : BitVec 64) : Prop :=
  ∀ i : Fin 3, ∃ reference, frame.locals[3 + i.val]? = some (.bytes .word64 reference) ∧
    read memory reference 8 1 = .ok (numberBytes (partialProduct a b i).toNat 8)

theorem word_prior_read (entered before after : Memory) (boundary : Nat) (frame : Frame)
    (homes : WritableHomes entered boundary wordBody.localKinds frame.locals)
    (i j : Nat) (ordered : i < j) (kind : CIL.LocalKind) (source target : Reference)
    (sourceSlot : frame.locals[i]? = some (.bytes kind source))
    (targetSlot : frame.locals[j]? = some (.bytes .word64 target))
    (writtenBytes bytes : List (BitVec 8)) (width : Nat)
    (written : write before target writtenBytes 1 = .ok after)
    (loaded : read before source width 1 = .ok bytes) :
    read after source width 1 = .ok bytes :=
  write_preserves_disjoint_read written loaded
    (Or.inl (Nat.ne_of_lt (homes.ordered i j kind .word64 source target ordered sourceSlot targetSlot)))

theorem digits_after_product_store (entered before after : Memory) (boundary : Nat) (frame : Frame)
    (homes : WritableHomes entered boundary wordBody.localKinds frame.locals)
    (a b : BitVec 64) (digits : DigitHomes before frame a b)
    (index : Nat) (later : 3 ≤ index) (reference : Reference)
    (slot : frame.locals[index]? = some (.bytes .word64 reference)) (bytes : List (BitVec 8))
    (written : write before reference bytes 1 = .ok after) : DigitHomes after frame a b := by
  intro i
  obtain ⟨r, found, loaded⟩ := digits i
  exact ⟨r, found, word_prior_read entered before after boundary frame homes i.val index
    (by omega) .word32 r reference found slot bytes _ 4 written loaded⟩

/-- Execute all three partial-product calculations, preserving the input digits
    and initialized earlier products across the later private writes. -/
theorem software_products (entered current : Memory) (boundary : Nat) (frame : Frame)
    (a b : BitVec 64) (output : Reference) (enteredWF : entered.WellFormed)
    (currentWF : current.WellFormed)
    (homes : WritableHomes entered boundary wordBody.localKinds frame.locals)
    (authority : AccessBelow entered.nextIdentity entered current)
    (digits : DigitHomes current frame a b)
    (post : Memory → List Value → Prop)
    (continuation : ∀ after,
      DigitHomes after frame a b → ProductHomes after frame a b → after.WellFormed →
      MemoryBelow boundary current after → AccessBelow entered.nextIdentity entered after →
      ∃ fuel final returned,
        run Extracted.program fuel wordIndex 62
          [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)] frame [] after =
          .ok (final, returned) ∧ post final returned) :
    ∃ fuel final returned,
      run Extracted.program fuel wordIndex 37
        [.scalar (.i64 a), .scalar (.i64 b), .reference (.address output)] frame
        [.scalar (.i32 (a.setWidth 32))] current = .ok (final, returned) ∧ post final returned := by
  obtain ⟨r3, s3, bound3, ready3⟩ := homes.home_at 3 .word64 (by rfl)
  obtain ⟨r4, s4, bound4, ready4⟩ := homes.home_at 4 .word64 (by rfl)
  obtain ⟨r5, s5, bound5, ready5⟩ := homes.home_at 5 .word64 (by rfl)
  have available (r : Reference) (ready : access entered r 8 1 true = .ok ()) :
      access current r 8 1 true = .ok () := by
    obtain ⟨allocation, requirements⟩ := access_requirements ready
    exact authority.access ready (enteredWF.1 _ _ requirements.present).1
  obtain ⟨allocation4, access4⟩ := access_requirements (available r4 ready4)
  obtain ⟨allocation5, access5⟩ := access_requirements (available r5 ready5)
  apply software_lower current frame a b output r3 digits s3 (available r3 ready3) post
  intro m3 w3 read3
  have digits3 := digits_after_product_store entered current m3 boundary frame homes a b digits
    3 (by decide) r3 s3 _ w3
  apply software_middle m3 frame a b output r4 r3 digits3 s3 read3 s4 (access4.after_write w3).access post
  intro m4 w4 read4
  have digits4 := digits_after_product_store entered m3 m4 boundary frame homes a b digits3
    4 (by decide) r4 s4 _ w4
  apply software_upper m4 frame a b output r5 r4 digits4 s4 read4 s5
    ((access5.after_write w3).after_write w4).access post
  intro m5 w5 read5
  have digits5 := digits_after_product_store entered m4 m5 boundary frame homes a b digits4
    5 (by decide) r5 s5 _ w5
  have products : ProductHomes m5 frame a b := by
    intro i
    have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases cases with rfl | rfl | rfl
    · refine ⟨r3, s3, ?_⟩
      apply word_prior_read entered m4 m5 boundary frame homes 3 5 (by decide) .word64 r3 r5 s3 s5 _ _ 8 w5
      exact word_prior_read entered m3 m4 boundary frame homes 3 4 (by decide) .word64 r3 r4 s3 s4 _ _ 8 w4 read3
    · exact ⟨r4, s4, word_prior_read entered m4 m5 boundary frame homes 4 5 (by decide) .word64 r4 r5 s4 s5 _ _ 8 w5 read4⟩
    · exact ⟨r5, s5, read5⟩
  exact continuation m5 digits5 products
    (write_preserves_wellFormed _ _ _ _ _
      (write_preserves_wellFormed _ _ _ _ _ (write_preserves_wellFormed _ _ _ _ _ currentWF w3) w4) w5)
    (((write_preserves_memory_below _ _ _ _ _ _ bound3 w3).trans
      (write_preserves_memory_below _ _ _ _ _ _ bound4 w4)).trans
      (write_preserves_memory_below _ _ _ _ _ _ bound5 w5))
    (((authority.trans (write_preserves_access_below w3 _)).trans (write_preserves_access_below w4 _)).trans
      (write_preserves_access_below w5 _))

#print axioms software_products
end UInt256Proof.Multiply.Safety
