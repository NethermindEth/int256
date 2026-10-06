import CIL.Safety.WordHomes

namespace CIL.Safety

/-- A reference initializer creates an initialized null root at its metadata index. -/
theorem WordHomes.root_at {memory : Memory} {lower : Nat} {specs slots}
    (homes : WordHomes memory lower specs slots) (index : Nat)
    (specified : specs[index]? = some none) :
    slots[index]? = some (.root (some .null)) := by
  induction homes generalizing index with
  | nil => simp at specified
  | root tail ih =>
    cases index with
    | zero => rfl
    | succ index => simpa using ih index (by simpa using specified)
  | word reference initial fresh loaded writable tail ih =>
    cases index with
    | zero => simp at specified
    | succ index => simpa using ih index (by simpa using specified)

#print axioms WordHomes.root_at
end CIL.Safety
