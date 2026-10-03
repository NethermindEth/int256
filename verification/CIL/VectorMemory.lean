import CIL.Memory

/- Exact overload references (.NET 10):
   https://learn.microsoft.com/dotnet/api/system.runtime.compilerservices.unsafe.add?view=net-10.0
   https://learn.microsoft.com/dotnet/api/system.runtime.compilerservices.unsafe.bitcast?view=net-10.0
   https://learn.microsoft.com/dotnet/api/system.runtime.interopservices.memorymarshal.getreference?view=net-10.0
   https://learn.microsoft.com/dotnet/api/system.readonlyspan-1.-ctor?view=net-10.0
   Unsafe.Add scales by element size. BitCast preserves storage bits.
   The supported span constructor is the observed byte pointer/Int32 overload;
   empty-span GetReference is deliberately unsupported because dereferencing its
   result has no valid element. Static bytes come from the extracted RVA field. -/

namespace CIL

/-- Vector values are snapshots; references continue to name the underlying bytes.
    No alignment assumption is imposed on caller accesses. -/
def read128 (m : Memory) : Address → Option Value
  | .byte base => do return .v128 (BitVec.ofNat 128 (← readBytes m base 16))
  | .local frame index => do
    let .v128 bits ← m (.local frame index) | none
    return .v128 bits
  | .static bytes base => do return .v128 (BitVec.ofNat 128 (← readStaticBytes bytes base 16))
  | .home frame kind index offset =>
    if offset + 16 ≤ 32 then do
      return .v128 (BitVec.ofNat 128 (← readHomeBytes m frame kind index offset 16))
    else none

def read256 (m : Memory) : Address → Option Value
  | .byte base => do return .v256 (BitVec.ofNat 256 (← readBytes m base 32))
  | .local frame index => do
    let .v256 bits ← m (.local frame index) | none
    return .v256 bits
  | .static bytes base => do return .v256 (BitVec.ofNat 256 (← readStaticBytes bytes base 32))
  | .home frame kind index offset =>
    if offset + 32 ≤ 32 then do
      return .v256 (BitVec.ofNat 256 (← readHomeBytes m frame kind index offset 32))
    else none

def write128 (m : Memory) (address : Address) (bits : BitVec 128) : Option Memory :=
  match address with
  | .byte base => some (writeBytes m base bits.toNat 16)
  | .local frame index => some (write m (.local frame index) (.v128 bits))
  | .static _ _ => none
  | .home frame kind index offset =>
    if offset + 16 ≤ 32 then some (writeHomeBytes m frame kind index offset bits.toNat 16)
    else none

def write256 (m : Memory) (address : Address) (bits : BitVec 256) : Option Memory :=
  match address with
  | .byte base => some (writeBytes m base bits.toNat 32)
  | .local frame index => some (write m (.local frame index) (.v256 bits))
  | .static _ _ => none
  | .home frame kind index offset =>
    if offset + 32 ≤ 32 then some (writeHomeBytes m frame kind index offset bits.toNat 32)
    else none

/-- Only actual pointer representations may be reinterpreted as managed refs.
    In particular, a vector snapshot cannot become a pointer to caller storage. -/
def unsafeAsRef : Value → Option Value
  | .object base => some (.ref (.byte base))
  | .ref address => some (.ref address)
  | _ => none

/-- Byte-address arithmetic is unbounded, as in the existing scalar memory
    model. Negative offsets must remain nonnegative. Local slots are typed
    storage, so offsetting into neighboring slots is explicitly unsupported. -/
def unsafeAdd (sizeBytes : Nat) (offset : Int) : Address → Option Address
  | .byte base =>
    let address := (base : Int) + (sizeBytes : Int) * offset
    if 0 ≤ address then some (.byte address.toNat) else none
  | .local frame index =>
    if offset = 0 then some (.local frame index) else none
  | .static bytes base =>
    let address := (base : Int) + (sizeBytes : Int) * offset
    if 0 ≤ address then some (.static bytes address.toNat) else none
  | .home frame kind index base =>
    let address := (base : Int) + (sizeBytes : Int) * offset
    if 0 ≤ address ∧ address ≤ 32 then some (.home frame kind index address.toNat) else none

@[simp ↓] theorem unsafeAdd_byte_natural (size base offset : Nat) :
    unsafeAdd size (offset : Int) (.byte base) = some (.byte (base + size * offset)) := by
  simp [unsafeAdd, ← Int.natCast_mul, ← Int.natCast_add]

/-- Exact memory calls and object opcodes supported by the reachable vector
    bodies. Widths and signedness are fixed by the validated overload. -/
inductive MemoryOp where
  | load128 | load256 | store128 | store256 | init256
  | asRef | add (sizeBytes : Nat) (signed : Bool)
  | bitcast256 | bitcastByteBool | skipInit
  | dataToken (bytes : List (BitVec 8)) | createSpan | spanReference
  | staticAddress (bytes : List (BitVec 8)) | spanCreate
  deriving Repr

/-- The observed overloads are signed Int32 and unsigned native UIntPtr on
    the declared 64-bit runtime. Other overloads need their own typed model. -/
def offsetValue (signed : Bool) (value : Value) : Option Int :=
  match signed, value with
  | true, .i32 bits => some bits.toInt
  | false, .i64 bits => some (bits.toNat : Int)
  | _, _ => none

def evalMemory (op : MemoryOp) (stack : List Value) (m : Memory) :
    Option (Memory × List Value) := do
  match op, stack with
  | .load128, .ref address :: rest => return (m, (← read128 m address) :: rest)
  | .load256, .ref address :: rest => return (m, (← read256 m address) :: rest)
  | .load256, .object base :: rest => return (m, (← read256 m (.byte base)) :: rest)
  | .store128, .v128 bits :: .ref address :: rest =>
    return (← write128 m address bits, rest)
  | .store256, .v256 bits :: .ref address :: rest =>
    return (← write256 m address bits, rest)
  | .store256, .v256 bits :: .object base :: rest =>
    return (← write256 m (.byte base) bits, rest)
  | .init256, .ref address :: rest => return (← write256 m address 0, rest)
  | .init256, .object base :: rest => return (← write256 m (.byte base) 0, rest)
  | .asRef, v :: rest => return (m, (← unsafeAsRef v) :: rest)
  | .add size signed, offset :: .ref address :: rest =>
    return (m, .ref (← unsafeAdd size (← offsetValue signed offset) address) :: rest)
  | .bitcast256, .v256 bits :: rest => return (m, .v256 bits :: rest)
  | .bitcastByteBool, .i32 bits :: rest =>
    if bits.toNat < 256 then return (m, .i32 bits :: rest) else none
  | .bitcastByteBool, .i8 bits :: rest =>
    return (m, .i32 (bits.zeroExtend 32) :: rest)
  | .skipInit, .object _ :: rest | .skipInit, .ref _ :: rest => return (m, rest)
  | .dataToken bytes, _ => return (m, .dataToken bytes :: stack)
  | .createSpan, .dataToken bytes :: rest =>
    return (m, .span (.static bytes 0) bytes.length :: rest)
  | .staticAddress bytes, _ => return (m, .ref (.static bytes 0) :: stack)
  | .spanCreate, .i32 length :: .ref (.static bytes offset) :: rest =>
    if 0 ≤ length.toInt ∧ offset + length.toNat ≤ bytes.length then
      return (m, .span (.static bytes offset) length.toNat :: rest)
    else none
  | .spanReference, .span address length :: rest =>
    if length = 0 then none else return (m, .ref address :: rest)
  | _, _ => none

end CIL
