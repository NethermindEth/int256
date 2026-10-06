# Compiled memory-safety probes

Run `python verification/Tests/Fixtures/Safety/checks.py` from the repository
root with the pinned .NET and Lean toolchains available. Use `--case NAME` to
select affected cases and `--output PATH` to retain the receipt.

Each case builds a fresh fixture DLL and extracts its reachable CIL. The runner
checks that the intended memory operation survived compilation, then generates
and kernel-checks a witness against those instructions. Negative cases include
a valid public starting call, including the static-world requirements for the
extracted program, and a theorem excluding successful execution for every fuel.
Positive probes also check those static-world requirements. Extraction errors and proof failures do not count as successful
safety detections. Positive probes establish their supplied executions, not a
universal production contract.

`MaskedVectorOverread` reads 32 bytes starting eight bytes into a 32-byte input,
then masks away all but the low lane. Its failure is allocation bounds.
`VectorOutsideView` uses identical C# with a 40-byte containing allocation but
only a 32-byte readable input view. Its load fits the allocation and fails read
authority. Both public entries discard the probe result before ordinary Add,
so the extra read cannot be excused by the arithmetic result or lane mask.

`WriteThenRestore` modifies a read-only input limb and restores its original
value. Both stores must survive compilation; the first store fails write
authority, independently of the restored final contents. `InvalidNativeOffset`
uses a native unsigned offset of all ones in vector reference arithmetic. The
32-byte scaling wraps at native width, and the resulting reference fails
formation before its vector load.

`EndThenInterior` forms the permitted one-past-end reference and returns inside
the allocation before loading. `Overread` checks the corresponding forbidden
dereference at the end. `UnalignedVector` loads an initialized 32-byte vector
from offset eight in a 40-byte allocation with eight-byte alignment; its readable
view covers exactly those 32 bytes.

`EscapedLocal` compiles a helper returning a reference to its local through
`Unsafe.AsRef`. Byref-returning helpers are outside the extractor's supported
language. This case requires that exact metadata rejection and no extracted
artifact; its receipt explicitly records no public semantic refutation or
checked starting state. `ReusedLocal` retains the first returned reference across
a second invocation of the same helper and requires the same unsupported-language
rejection. These cases do not substitute for the interpreter’s lifetime and fresh
allocation-identity proofs.

`AlignedLoad` uses `Sse2.LoadAlignedVector128` through `Unsafe.AsPointer`.
Extraction must reject that exact raw-pointer conversion and issue no artifact.
This records an unsupported aligned API, not a semantic alignment refutation.
The target-specific ordinary-access convention and its runtime assumptions are
documented in the [alignment audit](../../../CIL/Safety/ALIGNMENT.md).

The other cases exercise interior references, invalid references repaired before
dereference, aggregate homes, static lookup bounds and vector initialization.
Receipts record artifact identities, actual probe instructions and theorem axiom
audits. Native crashes are not required evidence.

The Overread case also checks a legal adjacent placement: the source allocation's
end has the same numerical address as the output allocation's start. Its
all-fuel public refutation still holds because a reference retains its source
provenance. The separate `AdjacentAudit` binds this placement and access
distinction to the same compiled entry, with mandatory audits and a recorded hash.

The Overread adjacent-placement audit also checks the old interpreter on the same
compiled public entry and byte contents: it returns the initial-input sum modulo
2^256, while the safety interpreter rejects every possible successful fuel.
This is a concrete arithmetic-correct, memory-unsafe witness, not a universal
arithmetic contract for the fixture. Both observations are kernel checked.
