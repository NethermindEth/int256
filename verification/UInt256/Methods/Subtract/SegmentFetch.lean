import CIL.Safety.StepComposition

namespace UInt256Proof.Subtract.Profile

/-- A segment placed after `base` leading instructions is fetched by its local index. -/
theorem segment_fetch {body : CIL.Method} {leading seg tail : List CIL.Op} {base : Nat}
    (code : body.code = leading ++ seg ++ tail) (leadingLength : leading.length = base) (i : Nat) :
    body.code[base + i]? = (seg ++ tail)[i]? := by
  rw [code, List.append_assoc, ← leadingLength, List.getElem?_append_right (by omega)]
  simp

theorem segment_fetch_zero {body : CIL.Method} {leading seg tail : List CIL.Op} {base : Nat}
    (code : body.code = leading ++ seg ++ tail) (leadingLength : leading.length = base) :
    body.code[base]? = (seg ++ tail)[0]? := by
  simpa using segment_fetch code leadingLength 0

/-- Fetch an instruction at `base + k` (or `base`) from a segment equation and its leading length. -/
macro "seg_fetch " code:term:max leadingLength:term:max : tactic => `(tactic| (
  first
  | (rw [segment_fetch $code $leadingLength]; rfl)
  | (rw [segment_fetch_zero $code $leadingLength]; rfl)
  | (simp only [Nat.add_assoc, Nat.reduceAdd]
     first
     | (rw [segment_fetch $code $leadingLength]; rfl)
     | (rw [segment_fetch_zero $code $leadingLength]; rfl))))

#print axioms segment_fetch
#print axioms segment_fetch_zero
end UInt256Proof.Subtract.Profile
