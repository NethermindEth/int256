# Compiled memory-safety probes

Run `dotnet run --file verification/SafetyRegression.cs` (`--case NAME` selects one
case). Each case compiles a fixture whose public `Add` calls a private `Probe` on its
first input, discards the value, then computes the ordinary sum. The runner extracts
the compiled DLL on the scalar profile through the pinned LeanCIL and kernel-checks a
witness over a concrete caller memory (`WitnessTemplate.lean.in`): a read-only input
allocation with nonzero limbs 0 and 1, a writable 32-byte output, and the empty
static world.

- A negative certifies `¬ WrappingBinaryContract (· + ·) Extracted.program 0`: the
  valid public call faults, and the fault is pinned exactly: method (named in
  `Cases.props`), instruction, rule, reference and width (`checked_binary_fault_refuted`).
  The production `AddScalar` proof must then
  fail in proof checking without leaving a certificate. That rejection is structural
  (the program contains a probe call); the semantic evidence is the pinned fault.
- A positive certifies the calling conditions, that the public call returns the
  initial-input sum, and that `Probe` itself returns the value in `Cases.props`.
  Positives establish these concrete executions, not a universal contract.

`VectorOutsideView` reuses the `MaskedVectorOverread` source with a 40-byte input
allocation whose readable view is 32 bytes, so the load fits the allocation and fails
read authority instead of bounds. `UnalignedVector` places the input at offset 8 of
a 40-byte, 8-aligned allocation.

All cases except AlignedLoad are consumer properties (the public Add contract on a
compiled shape) and are ported as `Safety/<Case>`. The upstream column gives the
closest LeanCIL test; partial coverage is drafted in
`verification/artifacts/upstream-fixture-gaps/03-semantic-shape-tests.md`.

| Original case | Kind | Original expectation | Checked at LeanCIL 7aec18e | Upstream |
| --- | --- | --- | --- | --- |
| Interior | positive | probe returns 1 | PASS: probe returns 1 | `Tests/UnsafeReferences.cs:46-52` |
| EndThenInterior | positive | probe returns 1 | PASS: probe returns 1 | partial: `Tests/UnsafeLayouts.cs:64-74` |
| UnalignedVector | positive | probe returns 1 | PASS: probe returns 1 | partial: `CIL/Safety/AccessAlignment.lean:39-50` |
| AggregateHome | positive | probe returns 17 | PASS: probe returns 17 | partial: `Tests/Arguments.cs:69` |
| StaticLookup | positive | probe returns 42 | PASS: probe returns 42 | partial: `Tests/StaticSpans.cs:22-25` |
| InitializedVector | positive | probe returns 7 | PASS: probe returns 7 | partial: `Tests/SkipInitialization.cs:38-44` |
| Overread | negative | `outsideAllocation` at `<0, 32>`, width 8 | PASS: same, `Probe` instruction 5 | `Tests/UnsafeReferences.cs:55-56` |
| InvalidThenRepaired | negative | `invalidReference` at `<0, 0>` | PASS: same, `Probe` instruction 4 | `Tests/UnsafeLayouts.cs:76-77` |
| AggregateOverread | negative | `outsideAllocation` at `<2, 32>`, width 8 | PASS: `<3, 32>`, width 8, `ReadSnapshot` instruction 5 (frame identities are numbered differently) | partial: by-reference overreads only |
| StaticOverread | negative | `outsideAllocation` at `<1, 0>`, width 32 | PASS: `<2, 0>`, width 32, `Probe` instruction 3 (static allocation identity differs) | partial: `Tests/StaticSpans.cs:24-25` |
| UninitializedVector | negative | `uninitialized` at `<1, 0>`, width 32 | PASS: `.invalidState` at the `extract64` intrinsic, `Probe` instruction 12. The load yields a flagged snapshot; extracting even the initialised lane fails | partial: `Tests/SkipInitialization.cs:38-44` |
| MaskedVectorOverread | negative | `outsideAllocation` at `<0, 8>`, width 32 | PASS: same, `Probe` instruction 6 | partial: `Tests/UnsafeReferences.cs:36-42` |
| VectorOutsideView | negative | `unreadable` at `<0, 8>`, width 32 | PASS: same, `Probe` instruction 6 | partial: `Tests/PrimitiveOperations.cs:172` |
| WriteThenRestore | negative | `unwritable` at `<0, 0>`, width 8 | PASS: same, `Probe` instruction 11 | `Tests/PrimitiveOperations.cs:124-125` |
| InvalidNativeOffset | negative | `invalidReference` at `<0, 0>` | PASS: same, `Probe` instruction 6 | partial: `Tests/UnsafeLayouts.cs:71-77` |
| EscapedLocal | extractor rejection of ref returns | metadata rejection, no artifact | now extracts; PASS: `expiredLifetime` at `<2, 0>`, `Expired` instruction 5 (the `ret`) | partial: `Tests/Arguments.cs:71-102` |
| ReusedLocal | extractor rejection of ref returns | metadata rejection, no artifact | now extracts; PASS: same fault as EscapedLocal. The first return already faults, so the second call is never reached and fresh frame identity is not exercised | partial: `Tests/Arguments.cs:71-102` |
| AlignedLoad | extractor rejection | rejection of `Unsafe.AsPointer` aligned load | not run here: `Unsupported generic method signature or body` | gap: `02-unsupported-metadata-tests.md` |
| AdjacentAudit | audit of the Overread placement | reference keeps provenance across adjacent allocations | holds by construction: references are `<allocation, offset>` pairs, so no adjacent placement can alias | not applicable |

AggregateOverread and StaticOverread are pinned to the identities the current
semantics assign; a change in identity numbering will fail them loudly and needs a
reviewed update of `Cases.props`.
