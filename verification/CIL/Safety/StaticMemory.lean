import CIL.Safety.InstructionMemory

namespace CIL.Safety

/-- Static initialization occurs before exposing the readonly view. Existing
    bindings are checked against the freshly extracted field bytes, lifetime
    and layout; cached contents are never trusted just because names match. -/
def staticReference (descriptor : CIL.StaticDescriptor) (m : Memory) :
    ExecutionResult (Memory × Reference) := do
  match m.staticBindings.find? (fun binding => binding.1 == descriptor.identity) with
  | some (_, reference) =>
    let allocation ← checkedAt (.address reference) descriptor.bytes.length
      (liveAllocation m reference.allocation)
    if allocation.kind == .immutableStatic && reference.offset == 0 &&
        allocation.layout.size == descriptor.bytes.length then pure () else .error .invalidState
    let bytes ← checkedAt (.address reference) descriptor.bytes.length
      (read m reference descriptor.bytes.length 1)
    if bytes == descriptor.bytes then return (m, reference) else .error .invalidState
  | none =>
    let (id, memory) ← checkedAt .null descriptor.bytes.length (allocate m {
      kind := .immutableStatic
      layout := ⟨descriptor.bytes.length, 1, []⟩
      sentinels := [descriptor.bytes.length] })
    let reference : Reference := ⟨id, 0⟩
    return ({ memory with
      cells := fun other offset => if other == id then
        match descriptor.bytes[offset]? with
        | some byte => ⟨byte, true⟩
        | none => ⟨0, false⟩
        else memory.cells other offset
      views := ⟨id, 0, descriptor.bytes.length, true, false⟩ :: memory.views
      staticBindings := (descriptor.identity, reference) :: memory.staticBindings }, reference)

def staticInstruction (body : CIL.Method) (pc : Nat) (operation : CIL.MemoryOp)
    (stack : List Value) (m : Memory) : ExecutionResult (Memory × List Value) := do
  match operation, stack with
  | .staticAddress bytes, _ =>
    let some (_, descriptor) := body.staticSites.find? (fun site => site.1 == pc) |
      .error (.unsupported "Missing extracted static field identity")
    if descriptor.bytes == bytes then pure () else .error .invalidState
    let (memory, reference) ← staticReference descriptor m
    return (memory, .reference (.address reference) :: stack)
  | .spanCreate, .scalar (.i32 length) :: .reference (.address reference) :: rest =>
    if length.toInt < 0 then .error .invalidState else pure ()
    let allocation ← checkedAt (.address reference) length.toNat
      (liveAllocation m reference.allocation)
    if allocation.kind == .immutableStatic then pure () else
      .error (.unsupported "Span pointer constructor outside extracted static data")
    let _ ← formValue m (.address reference)
    if reference.offset + length.toNat ≤ allocation.layout.size then pure () else
      .error (.memory .outsideAllocation (.address reference) length.toNat)
    return (m, .span (.address reference) length.toNat :: rest)
  | .spanCreate, .scalar (.i32 length) :: .reference .null :: rest =>
    if length == 0 then return (m, .span .null 0 :: rest)
    else .error (.memory .nullDereference .null length.toNat)
  | _, _ => memoryInstruction operation stack m

end CIL.Safety
