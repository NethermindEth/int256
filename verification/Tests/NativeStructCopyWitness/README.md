This standalone C# witness uses no unsafe code and isolates struct assignment from
UInt256 and multiplication. A 40-byte explicit-layout union places a 32-byte
input at offset zero and its output at offset eight. `Copy` is non-inlined and
contains only `output = input`.

The snapshot-model expectation is `[0, 1, 0, 0]`. A different result or modification outside
the output exits with status 1. JSON records runtime, architecture, vector
capability, offsets, expected/actual words and the method's raw CIL.

Build and run against the affected released runtime:

```powershell
dotnet build verification/Tests/NativeStructCopyWitness -c Release -p:EnforceCodeStyleInBuild=true -p:GenerateDocumentationFile=true
$env:DOTNET_EnableHWIntrinsic = '0'
$env:DOTNET_TieredCompilation = '0'
$env:DOTNET_JitDisasm = 'Program:Copy'
dotnet --fx-version 10.0.12 verification/Tests/NativeStructCopyWitness/bin/Release/net10.0/NativeStructCopyWitness.dll
Remove-Item Env:DOTNET_EnableHWIntrinsic, Env:DOTNET_TieredCompilation, Env:DOTNET_JitDisasm
```

The CIL is `ldarg.1; ldarg.0; ldobj Words; stobj Words; ret`. The disabled-intrinsics
x64 JIT emits the following on both .NET 10.0.12 and the tested runtime `main`:

```asm
movups xmm0, [rcx]
movups [rdx], xmm0
movups xmm0, [rcx+16]
movups [rdx+16], xmm0
```

With `rdx = rcx + 8`, the first store overwrites the next source chunk before its
load. This identifies the native copy sequence that differs from the model
snapshot; multiplication arithmetic is not needed to reproduce the discrepancy. [ECMA-335 III.4.13 and III.4.29](https://www.ecma-international.org/wp-content/uploads/ECMA-335_6th_edition_june_2012.pdf)
describe loading a value onto the evaluation stack and storing that value. The
witness uses no `cpblk` and contains no object references or pointer casts. Those
facts do not by themselves settle the runtime contract for partial overlap; the
[memory-safety boundary](../../CIL/Safety/BOUNDARY.md#explicit-limits) keeps that
correspondence obligation separate from the model proofs.

Observed Windows x64 results, with hardware intrinsics disabled:

| Witness | Runtime | Default tiered execution | Tiering disabled (FullOpts) |
|---|---|---|---|
| Struct copy | .NET 10.0.12 | `[0, 1, 1, 0]` | `[0, 1, 1, 0]` |
| Multiplication | .NET 10.0.12 | `[0, 1, 1, 0]` | `[0, 0, 0, 0]` |
| Struct copy | Tested `main` | `[0, 1, 1, 0]` | `[0, 1, 1, 0]` |
| Multiplication | Tested `main` | `[0, 1, 1, 0]` | `[0, 1, 0, 0]` (correct) |

The tested `main` is `d90dbf43be153cc7ba7f49bb271e0b7e56a81891`, reporting
`.NET 12.0.0-dev`. Its Release JIT, VM, host and CoreLib were freshly built in an
isolated checkout. Other managed framework libraries came from an existing local
testhost. JIT compilation was enabled with `FEATURE_DYNAMIC_CODE_COMPILED=1`;
ReadyToRun was disabled. The source checkout was clean for the final executions.
Native instructions were captured, confirming that `Copy` executed through the
fresh JIT. The same production DLL was used for both runtime multiplication runs.

On the tested AVX-capable machine, enabling hardware intrinsics makes the
non-inlined copy one 32-byte load followed by one store, and the sample passes on
both runtimes. The installed .NET 11.0.0-preview.7.26381.103 also fails the
disabled-intrinsics FullOpts copy. These samples are diagnostics, not universal
native correctness guarantees.

Release-source analysis uses [v10.0.12](https://github.com/dotnet/runtime/tree/v10.0.12),
not an assumed equivalent `main`. The installed 10.0.12 runtime's `.version`
records commit `95017c711e6afc1085133d440e42b4bd78155701`.

The reproduction is tracked in [#135183](https://github.com/dotnet/runtime/issues/135183).
Historical context includes [block-copy issue #7539](https://github.com/dotnet/runtime/issues/7539). A separate
[physical-promotion fix #133877](https://github.com/dotnet/runtime/pull/133877)
addresses overlapping promoted fields; [#134411](https://github.com/dotnet/runtime/pull/134411)
explicitly notes that its regression also encounters #7539. The reproduction
here supplies a reproduction without the old issue's unsafe-pointer conversion.
