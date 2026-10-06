import CIL.Safety.InstructionReferences
import CIL.Safety.StaticInitialization

namespace CIL.Safety

theorem access_reference_valid (m : Memory) (r : Reference) (width alignment : Nat)
    (writing : Bool) (h : access m r width alignment writing = .ok ()) : form m r = .ok r := by
  unfold access at h
  cases hf : form m r with
  | error fault => simp [hf, Bind.bind, Except.bind] at h
  | ok formed =>
    have same := form_returns_input _ _ _ hf
    subst formed
    rfl

theorem read_reference_valid (m : Memory) (r : Reference) (width alignment : Nat)
    (bytes : List (BitVec 8)) (h : read m r width alignment = .ok bytes) : form m r = .ok r := by
  unfold read at h
  cases ha : access m r width alignment false with
  | error fault => simp [ha, Bind.bind, Except.bind] at h
  | ok accessed =>
    cases accessed
    exact access_reference_valid _ _ _ _ _ ha

theorem StaticBindingValid.reference_valid {m : Memory} {descriptor : CIL.StaticDescriptor}
    {reference : Reference} (valid : StaticBindingValid m descriptor reference) :
    form m reference = .ok reference := by
  obtain ⟨_, _, _, _, _, _, bytes⟩ := valid
  exact read_reference_valid _ _ _ _ _ bytes

theorem staticReference_reference_valid (descriptor : CIL.StaticDescriptor) (m result : Memory)
    (reference : Reference) (h : staticReference descriptor m = .ok (result, reference)) :
    form result reference = .ok reference := by
  cases hc : m.staticBindings.find? (fun binding => binding.1 == descriptor.identity) with
  | none => exact (staticReference_new_binding_valid _ _ _ _ hc h).reference_valid
  | some binding =>
    obtain ⟨key, cached⟩ := binding
    obtain ⟨rfl, rfl, bytes⟩ := cached_static_reference_checked _ _ _ _ _ _ hc h
    exact read_reference_valid _ _ _ _ _ bytes

theorem formValue_reference_valid (m : Memory) (r : ManagedReference) (value : Value)
    (h : formValue m r = .ok value) : (Value.reference r).Valid m := by
  have valid := formValue_result_valid _ _ _ h
  rw [formValue_returns_input _ _ _ h] at valid
  exact valid

theorem staticInstruction_values_valid (body : CIL.Method) (pc : Nat) (operation : CIL.MemoryOp)
    (stack values : List Value) (m result : Memory) (hm : m.WellFormed)
    (valid : ValuesValid m stack)
    (h : staticInstruction body pc operation stack m = .ok (result, values)) :
    ValuesValid result values := by
  have retained := valid.preserve hm (staticInstruction_extends_allocations _ _ _ _ _ _ _ h)
  unfold staticInstruction at h
  split at h <;> try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat' first
      | solve | apply memoryInstruction_values_valid _ _ _ _ _ hm valid; assumption
      | solve |
          apply ValuesValid.cons
          · first
            | exact True.intro
            | exact retained.tail.head
            | solve | apply staticReference_reference_valid; assumption
            | solve | apply formValue_reference_valid; assumption
          · first | exact retained | exact retained.tail | exact retained.tail.tail
      | cases h
      | split at h

#print axioms access_reference_valid
#print axioms staticReference_reference_valid
#print axioms staticInstruction_values_valid

end CIL.Safety
