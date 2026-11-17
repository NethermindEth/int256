Multiplication contracts describe execution of the extracted CIL, including the
snapshot semantics of `ldobj` and `stobj`. They do not verify the runtime JIT.

The public contract multiplies the initial 256-bit inputs modulo `2^256`,
requires a finite normal return, and specifies every caller byte after the
32-byte output update. Input and output ranges may overlap partially. Execution
proofs derive all four dispatch cases from the generated instructions; helper
summaries are checked against each selected assembly's actual bodies.

Arithmetic feature coverage separates software, BMI2 and ARM widening multiply
from the scalar, AVX2 and AVX512DQ.VL top-limb calculations. Architecture and ISA
prerequisites leave seven arithmetic classes. Each class has two independent
Vector256 storage settings, giving fourteen required representatives. The
instruction checker also validates availability of retained ISA calls.

For all seven selected multiplication APIs, `--safety` additionally checks allocation,
initialization, reference lifetime and intermediate execution validity, with
the same initial-input product and caller-memory guarantees. Its typed gate
binds the extracted public entry and extends each representative to valid
profiles with the same arithmetic class and storage flag. The returning operator
checks its private result storage and preserves every caller byte. Primitive-operand
operators also check conversion, initialization and lifetime of their private operand
copy; their contracts bind the declared scalar width and argument order.

A native .NET 10.0.12 x64 run with hardware intrinsics disabled exposes a
discrepancy for partially overlapping struct copies in `MultiplyByUInt64`.
Multiplying one by limbs `[0, 1, 0, 0]`, with output eight bytes into that input,
produces `[0, 1, 1, 0]` instead of `[0, 1, 0, 0]`. An explicit-layout union
reproduces this without unsafe reference casts. This native counterexample does
not refute the interpreter contract, which models a whole-value snapshot before
the store. That snapshot rule is a model choice; it does not establish a portable
CLR guarantee for partially overlapping struct copies. See the
[memory-safety boundary](../../../CIL/Safety/BOUNDARY.md#explicit-limits).

A standalone 32-byte struct assignment reproduces the failure without UInt256,
arithmetic or unsafe code. Freshly built runtime `main` at
`d90dbf43be153cc7ba7f49bb271e0b7e56a81891` still fails that copy and the default
tiered multiplication witness. Fully optimised multiplication passes on that
commit; the general copy failure remains in that tested build. These observations
cover both the release runtime and that main revision under the recorded settings;
they do not decide which overlap guarantees the runtime promises.

See the [minimal witness and version comparison](../../../Tests/NativeStructCopyWitness/README.md)
for the CIL, native instructions and exact execution settings. The current
upstream report is [dotnet/runtime#135183](https://github.com/dotnet/runtime/issues/135183).
Production code and mathematical contracts remain
unchanged. Production and aggregate coverage reports expose the native limitation
separately from their verified CIL status.

Reproduce against an existing production DLL from PowerShell:

```powershell
dotnet build verification/Tests/NativeMultiplyWitness -c Release -p:VerifiedAssembly=D:/path/to/Nethermind.Int256.dll -p:EnforceCodeStyleInBuild=true -p:GenerateDocumentationFile=true
$env:DOTNET_EnableHWIntrinsic = '0'
dotnet verification/Tests/NativeMultiplyWitness/bin/Release/net10.0/NativeMultiplyWitness.dll
Remove-Item Env:DOTNET_EnableHWIntrinsic
```

The executable records the loaded DLL hash, runtime, feature flags, initial
operands and expected/actual limbs. A wrong result exits with status 1; this is
an independent diagnostic, not an always-passing assertion of the known defect.
