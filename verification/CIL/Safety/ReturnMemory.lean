import CIL.Safety.FrameMemoryBelow

namespace CIL.Safety

/-- Teardown expires only owned identities; it preserves all earlier memory
    metadata, bytes, initialization and access authority. -/
theorem leaveFrame_preserves_memory_below (frame : Frame) (memory : Memory) (watermark : Nat)
    (owned : ∀ id ∈ frame.owned, watermark ≤ id) :
    MemoryBelow watermark memory (leaveFrame frame memory) := by
  have retained := expireAll_retained_fields frame.owned memory
  refine ⟨leaveFrame_preserves_older_allocations frame memory watermark owned, ?_, ?_⟩
  · intro id _ offset
    exact congrFun (congrFun retained.1 id) offset
  · intro id _ offset writing
    simp only [permitted, leaveFrame, retained.2.1]

#print axioms leaveFrame_preserves_memory_below

end CIL.Safety
