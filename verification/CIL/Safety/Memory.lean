import Std

/- Allocation-aware storage. This layer is independent of UInt256 and of the
   extracted program. Its checked operations are not yet a production certificate. -/
namespace CIL.Safety

abbrev AllocationId := Nat

inductive StorageKind where
  | managedHeap | callerStack | frame (activation : Nat) | immutableStatic
  deriving DecidableEq, Repr

structure Layout where
  size : Nat
  alignment : Nat
  /-- GC-sensitive fields can occur elsewhere in a larger containing object.
      Only accesses intersecting these byte intervals are unsupported. -/
  referenceSlots : List (Nat × Nat) := []
  deriving DecidableEq, Repr

structure Allocation where
  kind : StorageKind
  layout : Layout
  live : Bool := true
  /-- Only specified field/array end positions may be used as sentinels. -/
  sentinels : List Nat := []
  deriving DecidableEq, Repr

structure Reference where
  allocation : AllocationId
  offset : Nat
  deriving DecidableEq, Repr

inductive ManagedReference where
  | null | address (reference : Reference)
  deriving DecidableEq, Repr

structure Cell where
  bits : BitVec 8
  initialized : Bool
  deriving DecidableEq, Repr

structure View where
  allocation : AllocationId
  start : Nat
  length : Nat
  readable : Bool
  writable : Bool
  deriving DecidableEq, Repr

structure Memory where
  allocations : AllocationId → Option Allocation
  cells : AllocationId → Nat → Cell
  views : List View
  /-- Never decreases; allocation identities are not recycled when frames return. -/
  nextIdentity : Nat
  /-- Loaded assembly fields retain identity independently of their contents. -/
  staticBindings : List (Nat × Reference) := []

inductive Fault where
  | nullDereference | missingAllocation | expiredLifetime | invalidReference
  | outsideAllocation | unreadable | unwritable | uninitialized
  | unsupportedLayout | alignment | identityReuse
  | malformedAllocation
  deriving DecidableEq, Repr

abbrev Checked := Except Fault

def nativeLimit : Nat := 2^64

def Allocation.WellFormed (a : Allocation) : Prop :=
  a.layout.size < nativeLimit ∧ 0 < a.layout.alignment ∧
    (∀ offset ∈ a.sentinels, offset ≤ a.layout.size) ∧
    ∀ slot ∈ a.layout.referenceSlots, slot.1 + slot.2 ≤ a.layout.size

def Allocation.valid (a : Allocation) : Bool :=
  decide (a.layout.size < nativeLimit) && decide (0 < a.layout.alignment) &&
    a.sentinels.all (fun offset => decide (offset ≤ a.layout.size)) &&
    a.layout.referenceSlots.all (fun slot => decide (slot.1 + slot.2 ≤ a.layout.size))

def Memory.WellFormed (m : Memory) : Prop :=
  (∀ id a, m.allocations id = some a → id < m.nextIdentity ∧ a.WellFormed) ∧
  ∀ view ∈ m.views, ∃ a, m.allocations view.allocation = some a ∧
    view.start + view.length ≤ a.layout.size

def liveAllocation (m : Memory) (id : AllocationId) : Checked Allocation := do
  let some a := m.allocations id | .error .missingAllocation
  if a.live then return a else .error .expiredLifetime

def validPosition (a : Allocation) (offset : Nat) : Bool :=
  decide (offset < nativeLimit) &&
    (decide (offset < a.layout.size) || (decide (offset ≤ a.layout.size) && a.sentinels.contains offset))

/-- Formation checks do not require access permission or initialized bytes. -/
def form (m : Memory) (r : Reference) : Checked Reference := do
  let a ← liveAllocation m r.allocation
  if validPosition a r.offset then return r else .error .invalidReference

def validManagedReference (m : Memory) : ManagedReference → Bool
  | .null => true
  | .address r => match form m r with | .ok _ => true | .error _ => false

/-- Offset multiplication and addition wrap at native width. A wrapped result
    retains its allocation identity and must pass formation validity anew. -/
def add (m : Memory) (r : Reference) (elementSize : Nat) (offset : BitVec 64) : Checked Reference := do
  let _ ← form m r
  form m { r with offset :=
    (BitVec.ofNat 64 r.offset + BitVec.ofNat 64 elementSize * offset).toNat }

def viewContains (view : View) (r : Reference) : Bool :=
  decide (view.allocation = r.allocation ∧ view.start ≤ r.offset ∧ r.offset < view.start + view.length)

def permitted (m : Memory) (write : Bool) (r : Reference) : Bool :=
  m.views.any fun view => viewContains view r && (if write then view.writable else view.readable)

/-- Access bounds and API authority are distinct from formation validity. The
    required alignment is supplied by the particular instruction, not its width. -/
def access (m : Memory) (r : Reference) (width alignment : Nat) (write : Bool) : Checked Unit := do
  let _ ← form m r
  let a ← liveAllocation m r.allocation
  if a.layout.referenceSlots.any (fun slot =>
      decide (r.offset < slot.1 + slot.2 ∧ slot.1 < r.offset + width))
    then .error .unsupportedLayout else pure ()
  if r.offset + width ≤ a.layout.size then pure () else .error .outsideAllocation
  if alignment > 0 && a.layout.alignment % alignment == 0 && r.offset % alignment == 0
    then pure () else .error .alignment
  if write && a.kind == .immutableStatic then .error .unwritable else pure ()
  if (List.range width).all (fun i => permitted m write { r with offset := r.offset + i })
    then pure () else .error (if write then .unwritable else .unreadable)

def read (m : Memory) (r : Reference) (width alignment : Nat) : Checked (List (BitVec 8)) := do
  access m r width alignment false
  let cells := (List.range width).map fun i => m.cells r.allocation (r.offset + i)
  if cells.all (·.initialized) then return cells.map (·.bits) else .error .uninitialized

def dereference (m : Memory) (reference : ManagedReference) (width alignment : Nat) :
    Checked (List (BitVec 8)) :=
  match reference with
  | .null => .error .nullDereference
  | .address r => read m r width alignment

def write (m : Memory) (r : Reference) (bytes : List (BitVec 8)) (alignment : Nat) : Checked Memory := do
  access m r bytes.length alignment true
  -- A method may read its own initialized output. This grants no write authority
  -- and exposes exactly the interval whose original write authority was checked.
  return { m with
    views := ⟨r.allocation, r.offset, bytes.length, true, false⟩ :: m.views
    cells := (fun id offset =>
    if id = r.allocation ∧ r.offset ≤ offset then
      (match bytes[offset - r.offset]? with
      | some bits => { bits, initialized := true }
      | none => m.cells id offset)
    else m.cells id offset) }

/-- A snapshot is obtained before any destination change, preserving overlap. -/
def copy (m : Memory) (source target : Reference) (width : Nat) : Checked Memory := do
  let bytes ← read m source width 1
  write m target bytes 1

/-- SkipInit does not initialize or erase anything. -/
def skipInit (m : Memory) (r : Reference) : Checked Memory := do
  let _ ← form m r
  return m

def expire (m : Memory) (id : AllocationId) : Memory :=
  { m with allocations := fun other =>
      if other = id then (m.allocations other).map fun a => { a with live := false }
      else m.allocations other }

/-- Fresh activation storage has unknown bytes, even if a physical stack slot
    held initialized data in an earlier activation. -/
def allocate (m : Memory) (a : Allocation) : Checked (AllocationId × Memory) :=
  if !a.valid then .error .malformedAllocation else
  if (m.allocations m.nextIdentity).isSome then .error .identityReuse else
    .ok (m.nextIdentity, { m with
      allocations := fun id => if id = m.nextIdentity then some a else m.allocations id
      cells := fun id offset => if id = m.nextIdentity then { bits := 0, initialized := false }
        else m.cells id offset
      nextIdentity := m.nextIdentity + 1 })

end CIL.Safety
