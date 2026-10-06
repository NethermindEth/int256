# Memory-safety boundary

The allocation-aware layer checks reference and memory safety throughout the
execution of extracted CIL, together with the independent mathematical result,
finite normal termination and caller-memory footprint. Combined coverage includes
all 87 selected APIs and all valid feature profiles; the
[verification README](../../README.md) lists the 256 method/profile representatives.

`--safety` requires arithmetic and safety gates against the same fresh extraction.
Arithmetic-only reports cannot certify this layer. An exact-profile safety
report covers only its extracted configuration. Extending coverage requires a
kernel-checked transport theorem for the complete invocation certificate,
including intermediate-state validity; arithmetic execution equivalence alone
is insufficient. Reports bind the selected contract, profile and theorem audits.

Contracts distinguish reference inputs from values. By-value wrappers establish
initialized private argument homes before taking their addresses and retire
those homes after the checked child call. Read-only methods preserve every
pre-existing caller cell. Output methods retain initial-operand arithmetic,
arbitrary valid overlap and bytes outside the output; reporting methods also
bind the mathematical overflow or underflow flag. Signed and unsigned wrapper
conversions are checked separately from the leaf operation's interpretation.

These guarantees concern the modeled CIL. They do not establish JIT correctness,
GC root maps or concurrent execution. The native overlapping-copy discrepancy
remains an explicit boundary, described below and in the README.

**Alignment scope:** ordinary reference-free scalar, vector and aggregate
accesses use the target CoreCLR x64/ARM64 normal-memory convention, with hardware
alignment traps disabled. `ordinaryAccessAlignment` is one byte; caller offsets
and overlaps remain unrestricted. This is not a portable CLI guarantee:
[`ldind.i8`](https://learn.microsoft.com/en-us/dotnet/api/system.reflection.emit.opcodes.ldind_i8?view=net-10.0)
specifies natural alignment unless modified by `unaligned.`. The
[alignment audit](ALIGNMENT.md) records the target instruction-selection evidence,
kernel enforcement lemmas and remaining runtime assumptions. Reports retain this
correspondence boundary explicitly. Aligned memory APIs, volatile/atomic accesses
and device memory are excluded; ordinary accesses cannot establish their safety.

## References and specification choices

The target remains a 64-bit little-endian .NET 10 environment. Primary references:

- [ECMA-335, sixth edition, June 2012](https://ecma-international.org/wp-content/uploads/ECMA-335_6th_edition_june_2012.pdf):
  I.12.1.1.2 (managed pointers), II.14.4.2 (permitted locations),
  III.4.13/III.4.29 (`ldobj`/`stobj`) and III.2.5 (`unaligned.`).
- [CLI addendum at runtime revision d90dbf43](https://github.com/dotnet/runtime/blob/d90dbf43be153cc7ba7f49bb271e0b7e56a81891/docs/design/specs/Ecma-335-Augments.md),
  II.14.4.2: includes null references and field-end positions. A non-dereferenceable
  reference is not necessarily invalid to represent.
- [Unsafe implementation at the same revision](https://github.com/dotnet/runtime/blob/d90dbf43be153cc7ba7f49bb271e0b7e56a81891/src/libraries/System.Private.CoreLib/src/System/Runtime/CompilerServices/Unsafe.cs):
  exact `Add`, `As`, `AsRef`, `BitCast` and `SkipInit` overloads. The extraction
  allowlist still binds .NET 10 assembly identities; this source is supporting
  implementation evidence, not a new library-version assumption.
- [Unsafe-code guidance](https://learn.microsoft.com/en-us/dotnet/standard/unsafe-code/best-practices)
  and [vectorization guidance at d90dbf43](https://github.com/dotnet/runtime/blob/d90dbf43be153cc7ba7f49bb271e0b7e56a81891/docs/coding-guidelines/vectorization-guidelines.md):
  GC holes, bounds, initialization, alignment and lifetime hazards. Guidance is
  not a formal semantics or a proof that our semantics matches the runtime.
- [.NET 10 `Unsafe.Add`](https://learn.microsoft.com/en-us/dotnet/api/system.runtime.compilerservices.unsafe.add?view=net-10.0)
  specifies element-scaled offsets; its overloads distinguish signed and unsigned
  native offsets. [`Unsafe.ReadUnaligned`](https://learn.microsoft.com/en-us/dotnet/api/system.runtime.compilerservices.unsafe.readunaligned?view=net-10.0)
  removes the alignment requirement, but still requires the complete readable
  byte range. These contracts do not authorize out-of-allocation accesses.
- [`newobj` semantics](https://learn.microsoft.com/en-us/dotnet/api/system.reflection.emit.opcodes.newobj?view=net-10.0)
  and ECMA-335 III.4.21: new instances receive zero/null field initialization
  before constructor execution. This is separate from `SkipInit` and from
  constructor calls on existing storage.

These references distinguish specification requirements from runtime guidance.
The alignment convention above is target-specific; model-level execution
certificates do not establish correspondence with every CLR rule or JIT version.

## Storage and authority

Each allocation has a stable identity, extent, storage kind, lifetime and layout.
References pair that identity with an offset. Adjacent allocations stay distinct;
arithmetic cannot adopt another allocation because a numerical address happens to
land inside it. Caller allocations may be larger than UInt256 and contain several
overlapping views. The reusable model contains no fixed 32-byte allocation size.

Byte values, initialization and permissions are separate. A byte can contain a
possible bit pattern while remaining uninitialized and therefore unreadable.
Permissions describe method authority within the containing allocation. An access
must satisfy both the allocation extent and the permitted view footprint.

The UInt256 consumer defines `CallingConditions` in
`UInt256/Safety/Calling.lean`: live initialized 32-byte input views, live writable
32-byte output views, supported access layouts and a static world matching the
selected program. It does not constrain allocation size to 32 bytes or require
disjoint views. Output storage need not start initialized or readable.
A successful checked write grants read authority for exactly its written bytes
without expanding write authority. Overlap derives
initialization from the same underlying input bytes. Input/output views may alias
exactly or partially within one allocation; disjoint objects have distinct
identities. The contract contains no future-execution assumption.
`AccessRequirements` states present/live allocation, valid position, interval,
layout, alignment and per-byte authority conditions independently of instruction
execution; its theorem establishes the checked access. Consumer snapshot lemmas
connect the actual shared input bytes to the existing little-endian mathematical
`byteValue`, and prove a checked aggregate load has exactly that value.
`CallerExamples.lean` constructs valid disjoint, exact-alias and partial-overlap
calls for arbitrary shared byte contents, with only input bytes initialized.
These are nonvacuity and representation results, not production execution proofs.

## Operation requirements

| Operation family | Required checks |
| --- | --- |
| Argument/local/field addresses, `As`/`AsRef` | Preserve provenance; require a live permitted reference position. Reference reinterpretation does not read or initialize the referent. Only the exact reference-free representations admitted by extraction are supported. |
| `Unsafe.Add` | Validate the source and each intermediate result. Element scaling and addition use native-width wrapping; Int32 offsets are sign-extended and UIntPtr offsets are unsigned. A result outside its original allocation fails immediately. |
| Scalar/vector/aggregate load | Validate reference, lifetime, full interval, read authority, layout, initialization and the operation's alignment requirement. Discarding or masking a result does not remove the check. |
| Scalar/vector/aggregate store | Validate full interval, write authority, lifetime, layout and alignment before changing any byte. Initialize exactly the written interval. A later restoring write cannot excuse an earlier forbidden store. |
| `ldobj`/`stobj`, value arguments and copies | Capture the source bytes before modifying destination storage. All source bytes must be initialized. Aliased views share storage and initialization. |
| `SkipInit` | Preserve memory and initialization. It does not promise zeroes or make unknown bytes readable. |
| `initobj`, constructors | Initialize only actual writes. Constructor temporaries and aggregate homes require their own fresh lifetime identities. |
| Calls, locals and returns | Preserve reference provenance. Expire callee-private identities on return; reject any escaping dead reference. Never revive an identity when a physical slot is reused. |
| Static lookup data and spans | Bind contents/layout to extracted RVA metadata, check complete bounds, prohibit mutation. Empty spans and null/end references need formation and access rules separately. |
| Value-only intrinsics | Retain exact ISA availability, width and overload checks. Their surrounding memory operations still require the checks above. |

`Execution.lean` follows actual fetched instructions, branches and nested calls.
`Frames.lean` uses extracted local kinds, fresh numeric homes and byref roots;
aggregate arguments receive private snapshot homes. Frame identities never
revive after teardown. Returned references are checked after expiration. A
`newobj` temporary is caller-owned zero-initialized storage passed to the actual
constructor; a snapshot is read only after its normal void return. The admitted
aggregate operations have UInt256 widths, while allocation storage is generic.

`HomeProgress` and `FrameProgress` justify setup from well-formed memory and
validated local/argument metadata. Fresh private homes carry their own lifetime,
initialization and access authority. `WordMemory`, `WordLocals` and `WordHomes`
connect those homes to checked byte reads and writes; setup alone does not assume
that the method body succeeds.

`WriteEffects` and byte-encoding lemmas establish exact readback and preservation
outside each authorized write. Disjoint writes retain earlier snapshots, while
overlapping output writes require the method proof to preserve initial operands
before overwriting them. `CallComposition` composes actual fetched calls, checked
child setup/execution/teardown and caller continuations with finite fuel.

Consumer proofs under `UInt256/` discharge these obligations against extracted
instruction sequences and connect their results to independent mathematical
contracts. `CIL/Safety/Certificate` connects each successful invocation to actual
execution, valid running and suspended states throughout nested calls, and a
valid returned state. The selected typed gates audit the complete contract;
intermediate helper lemmas alone do not certify a public API. Current
coverage and validation status belong in the verification README.

`StaticMemory.lean` binds instruction sites to extracted RVA fields, including
field identities and exact bytes. Fresh static homes are initialized readonly;
cached fields must match live immutable storage, extent and contents. Span
formation checks lifetime and extent separately from reads. `StaticWorldValid`
requires consistent descriptor identities, distinct registry/storage identities
and matching loaded fields. An empty registry is valid for consistent bounded
descriptors. Its preservation is proved through checked memory instructions,
frame setup/teardown, calls, constructors and observed execution prefixes.
Assembly lifetime remains an explicit runtime boundary.

`LiveState` combines structural memory, valid argument/stack/local references,
live frame ownership and the selected static world. `RunningVisits` preserves
it at actual running and suspended frame boundaries, including prefixes that
later fault. Successful runs have an actual fetched return trace, frame teardown
and separately checked returned state. Older caller allocation identities remain
live through nested calls and constructor continuations. These preservation
results are conditional on the actual checked steps/continuations: they do not
prove that arbitrary code can read unknown bytes, or that valid production calls
avoid every fault and terminate. Production access/initialization proofs and the
full functional connection remain required.

Compiled positive probes check extracted helper execution. Hazardous fixtures
establish valid public-entry starting states, exact classified faults and
impossibility of successful execution for every fuel. `FuelLemmas.lean` preserves
successful returns and semantic faults when fuel increases; exhaustion alone is
not a semantic refutation. These receipts are distinct from combined production
certificates and independent mathematical correctness proofs.

Byte-to-Boolean bitcasts admit only canonical zero/one representations in this
layer. Other representations are explicitly unsupported: CLI Boolean encodings
alone do not justify predictable JIT behaviour for denormalized values (unsafe
code guidance, section 21). This is a conservative verification restriction,
not a theorem that all other encodings cause a memory fault. The selected
production use extracts one bit with BMI1; production safety proofs must derive
its canonical range from that actual extracted execution.

## Formation, alignment and relocation

Null references may be represented but cannot be dereferenced. Interior offsets
are permitted within a live supported allocation. End positions are permitted
only when explicitly justified by its array/field layout, recorded as sentinels;
they confer no permission to access bytes beyond the allocation or API view.
General interior-byte treatment is a model restriction/representation choice for
the admitted reference-free layouts, not a theorem about arbitrary managed types.

Offsets are native-width values. Signed offsets are supplied after the CIL's
actual conversion; multiplication/addition truncate to 64 bits. A native-wrapped
offset does not acquire new provenance. Legal concrete placements must exclude
address-space wrap across each live allocation.

Unaligned operations require only byte alignment. Aligned operations must derive
their alignment from the allocation's guaranteed alignment and reference offset;
vector width alone is not an alignment requirement. The initial implementation
conservatively rejects alignment that is merely accidental at one placement.
The extractor must reject an unsupported aligned API rather than reinterpret it
as an unaligned operation.

Stable allocation identities do not assert stable native addresses. Legal
placements preserve extent and guaranteed alignment, avoid address-space wrap,
and keep live allocation interiors disjoint. Checked address lemmas establish
non-null, non-wrapping addresses, interior-address injectivity and the physical
alignment of every accepted access. End sentinels can coincide with an adjacent
allocation's start without acquiring that allocation's provenance.

The checked interpreter's steps, runs and invocations are independent of physical
placement. Relocation preserves abstract identity, bytes, initialization,
permissions and lifetime; it may change stronger incidental alignment. A checked
example moves an eight-byte-aligned allocation from address 128 to 136, losing
16-byte alignment. Neither position authorizes an instruction requiring an
unsupported 16-byte guarantee.

These are properties of the abstract placement model, not a concrete GC
simulation. The runtime must retain referents and correctly update tracked
managed references during GC; availability of physical storage for future
allocations remains an assumption.

## Explicit limits

This milestone excludes concurrent mutation, tearing, actual GC scheduling/root
maps, collector internals, native-code correctness and asynchronous runtime
failure. Calls still assume sufficient physical runtime stack and completed
supported type initialization. Raw-pointer escapes, pinning mechanisms and
write-barrier-sensitive layouts remain unsupported unless separately justified.
Numerical reference addresses in the old interpreter will require a checked
refinement if that interpreter is used to establish allocation safety; its
total byte map alone cannot do so. Current combined contracts instead prove
arithmetic directly over the allocation-aware interpreter. For example,
`UInt256/Safety/Contract.lean` binds the `InvocationCertificate`, initial operand
values, final output and preserved caller cells to the same memory states.
The separately retained arithmetic-only gate is not the safety argument.

The [native overlapping-copy discrepancy](https://github.com/dotnet/runtime/issues/135183)
remains independent and unresolved. An abstract safety proof must not be reported
as fixing JIT lowering or establishing native arbitrary-overlap correctness.

The [runtime discussion](https://github.com/dotnet/runtime/issues/135183#issuecomment-5980136520)
also questions which guarantees apply to explicitly overlapping storage. Therefore
the interpreter's snapshot rule for aggregate load/store is a specification choice,
not established evidence of a portable CLR partial-overlap guarantee. A combined
model certificate does not discharge this correspondence obligation. Rejecting
every multiword copy would be too broad: disjoint copies do not have this overlap
hazard. Introducing a C# struct temporary alone does not discharge it either;
optimization can remove the temporary. Any production workaround requires fresh
extraction, affected proofs, and native regression/code-generation checks while
preserving the independent arbitrary-valid-overlap contract.
