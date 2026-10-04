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

A native .NET 10.0.12 x64 run with hardware intrinsics disabled exposes a
discrepancy for partially overlapping struct copies in `MultiplyByUInt64`.
Multiplying one by limbs `[0, 1, 0, 0]`, with output eight bytes into that input,
produces `[0, 1, 1, 0]` instead of `[0, 1, 0, 0]`. An explicit-layout union
reproduces this without unsafe reference casts. This native counterexample does
not refute the CIL contract, whose whole-value load precedes the store.

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
