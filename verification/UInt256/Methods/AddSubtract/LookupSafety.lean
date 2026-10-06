import UInt256.Methods.AddSubtract.VectorMemory
import CIL.Safety.StaticMemoryBelow
import CIL.Safety.StepComposition

namespace UInt256Proof.AddSubtract.Safety
open CIL.Safety UInt256Model.Safety

def lookupIndex : Nat := Extracted.program.findIdx fun body => !body.staticSites.isEmpty

def lookupBody : CIL.Method := Extracted.program[lookupIndex]?.getD
  { code := [], locals := [], returnsValue := false }

def lookupDescriptor : CIL.StaticDescriptor := match lookupBody.staticSites with
  | (_, descriptor) :: _ => descriptor
  | [] => ⟨0, "", []⟩

theorem lookup_descriptor_length : lookupDescriptor.bytes.length = 512 := by decide +kernel

theorem lookup_descriptor_member : lookupDescriptor ∈ programStaticDescriptors Extracted.program := by
  apply program_static_sites_valid Extracted.program lookupIndex lookupBody (by rfl) (0, lookupDescriptor)
  have sites : lookupBody.staticSites = [(0, lookupDescriptor)] := by rfl
  simp only [sites, List.mem_singleton]

/-- Execute the actual static-span getter for both cached and newly allocated
    table storage, retaining all earlier memory and validating its exact bytes. -/
theorem lookup_getter_checked (memory : Memory) (inputs outputs : List Reference)
    (call : CallingConditions Extracted.program memory inputs outputs) :
    ∃ result reference,
      invoke Extracted.program 4 lookupIndex [] memory = .ok (result, [.span (.address reference) 512]) ∧
      StaticBindingValid result lookupDescriptor reference ∧
      MemoryBelow memory.nextIdentity memory result ∧
      CallingConditions Extracted.program result inputs outputs := by
  obtain ⟨result, reference, resolved, world, valid⟩ := staticReference_valid_result lookupDescriptor
    (programStaticDescriptors Extracted.program) memory call.1.1 call.2 lookup_descriptor_member
  have preserved := staticReference_preserves_memory_below _ _ _ _ resolved
  have wf := staticReference_preserves_wellFormed _ _ _ _ call.1.1 resolved
  refine ⟨result, reference, ?_, valid, preserved, call.after_memory_below preserved wf world⟩
  have formed := valid.reference_valid
  obtain ⟨offset, allocation, present, live, kind, size, bytes⟩ := valid
  have length := lookup_descriptor_length
  have liveLookup : liveAllocation result reference.allocation = .ok allocation := by
    simp [liveAllocation, present, live, Pure.pure, Except.pure]
  have sites : lookupBody.staticSites = [(0, lookupDescriptor)] := by rfl
  have found : Extracted.program[lookupIndex]? = some lookupBody := by rfl
  let frame : Frame := ⟨memory.nextIdentity, [], [], []⟩
  have setup : enterFrame lookupBody [] memory = .ok (frame, memory) := by rfl
  simp only [invoke, found, List.mapM_nil, Except.mapError, Bind.bind, Except.bind,
    setup, Pure.pure, Except.pure]
  have first : step lookupBody (.memory (.staticAddress lookupDescriptor.bytes)) 0 [] frame [] memory =
      .ok (.next 1 [.reference (.address reference)] frame result) := by
    simp only [step, staticInstruction, sites, List.find?_cons, beq_self_eq_true,
      List.find?_nil, Bool.true_eq, ite_true, resolved, checkedAt,
      Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have second : step lookupBody (.const32 512) 1 [] frame [.reference (.address reference)] result =
      .ok (.next 2 [.scalar (.i32 512), .reference (.address reference)] frame result) := by
    rfl
  have third : step lookupBody (.memory .spanCreate) 2 [] frame
      [.scalar (.i32 512), .reference (.address reference)] result =
      .ok (.next 3 [.span (.address reference) 512] frame result) := by
    simp [step, staticInstruction, liveLookup, kind, offset, size, length,
      formValue, formed, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [run_next found (by rfl) first, run_next found (by rfl) second, run_next found (by rfl) third]
  have fetched : lookupBody.code[3]? = some .ret := by rfl
  have returns : lookupBody.returnsValue = true := by rfl
  simp [run, found, fetched, returns, step, checkedValue, formValue, formed,
    frame, leaveFrame, checkedAt, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms lookup_descriptor_member
#print axioms lookup_descriptor_length
#print axioms lookup_getter_checked
end UInt256Proof.AddSubtract.Safety
