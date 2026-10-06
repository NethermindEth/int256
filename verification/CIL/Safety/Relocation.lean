import CIL.Safety.MemoryLemmas

namespace CIL.Safety

/-- Concrete placement is an interpretation of identity, not part of a byref. -/
abbrev Placement := AllocationId → Nat

def Placement.Valid (p : Placement) (m : Memory) : Prop :=
  (∀ id a, m.allocations id = some a → a.live = true →
    0 < p id ∧ p id + a.layout.size < nativeLimit ∧
      p id % a.layout.alignment = 0) ∧
  (∀ left right a b, left ≠ right → m.allocations left = some a →
    m.allocations right = some b → a.live = true → b.live = true →
    p left + a.layout.size ≤ p right ∨ p right + b.layout.size ≤ p left)

/-- Relocation changes placement while abstract allocation identity, content,
    initialization, authority and lifetime remain unchanged. -/
def LegalRelocation (m : Memory) (before after : Placement) : Prop :=
  before.Valid m ∧ after.Valid m

def concreteAddress (p : Placement) (r : Reference) : BitVec 64 :=
  BitVec.ofNat 64 (p r.allocation + r.offset)

structure PlacedMemory where
  memory : Memory
  placement : Placement

def relocate (m : PlacedMemory) (placement : Placement) : PlacedMemory :=
  { m with placement }

def PlacedMemory.read (m : PlacedMemory) (r : Reference) (width alignment : Nat) :=
  Safety.read m.memory r width alignment

def PlacedMemory.form (m : PlacedMemory) (r : Reference) :=
  Safety.form m.memory r

def PlacedMemory.add (m : PlacedMemory) (r : Reference) (size : Nat) (offset : BitVec 64) :=
  Safety.add m.memory r size offset

theorem relocation_preserves_reference_validity (m : PlacedMemory) (after : Placement) (r : Reference) :
    (relocate m after).form r = m.form r := rfl

theorem relocation_preserves_read (m : PlacedMemory) (after : Placement) (r : Reference)
    (width alignment : Nat) : (relocate m after).read r width alignment = m.read r width alignment := rfl

theorem relocation_preserves_reference_arithmetic (m : PlacedMemory) (after : Placement)
    (r : Reference) (size : Nat) (offset : BitVec 64) :
    (relocate m after).add r size offset = m.add r size offset := rfl

/-- Only guaranteed allocation alignment and the offset justify an aligned
    access; this remains true at every legal placement. -/
theorem guaranteed_alignment_at_placement (p : Placement) (m : Memory)
    (hp : p.Valid m) (r : Reference) (a : Allocation)
    (ha : m.allocations r.allocation = some a) (hlive : a.live = true)
    (hoffset : r.offset % a.layout.alignment = 0) :
    (p r.allocation + r.offset) % a.layout.alignment = 0 := by
  have hbase := (hp.1 r.allocation a ha hlive).2.2
  simp [Nat.add_mod, hbase, hoffset]

end CIL.Safety
