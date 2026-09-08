# Int256

[![Tests / Publish](https://github.com/nethermindeth/int256/actions/workflows/test-publish.yml/badge.svg)](https://github.com/nethermindeth/int256/actions/workflows/test-publish.yml)
[![Nethermind.Numerics.Int256](https://img.shields.io/nuget/v/Nethermind.Numerics.Int256)](https://www.nuget.org/packages/Nethermind.Numerics.Int256)

**The fastest 256-bit arithmetic for .NET.**

Int256 provides `UInt256` and `Int256`: unsigned and signed 256-bit value types used by the [Nethermind Ethereum execution client](https://github.com/NethermindEth/nethermind). It brings the arithmetic behind EVM execution to your own .NET applications, from blockchain tooling to binary protocols and numeric workloads that need more than 128 bits.

## Why Int256?

- **256 bits, stored inline.** Readonly structs with a 32-byte representation. Core arithmetic works directly on fixed-width limbs without allocating a backing array for each result.
- **Modular arithmetic that keeps the intermediate bits.** `UInt256.AddMod` and `UInt256.MultiplyMod` reduce the full sum or product, including products up to 512 bits wide.
- **Optimized for the hardware you run.** Specialized x64 and ARM64 paths use hardware intrinsics where available, with software fallbacks. A separate RISC-V zkVM build tunes execution for guest workloads.
- **Made for hot paths.** `in`/`out` arithmetic APIs and span-based byte conversion let callers control copies and buffers.
- **Continuously maintained and optimized.** Ongoing development improves arithmetic algorithms and tunes performance for evolving .NET runtimes, CPU architectures, and RISC-V zkVM workloads.
- **Correctness you can inspect.** Tests compare arithmetic against `System.Numerics.BigInteger`, and CI exercises Windows, Linux, macOS, ARM64, and configurations with hardware intrinsics disabled.
- **MIT licensed.** Use it in open-source or commercial projects.

## Get started

Requires **.NET 10**.

```sh
dotnet add package Nethermind.Numerics.Int256
```

The package name is `Nethermind.Numerics.Int256`; the C# namespace is `Nethermind.Int256`.

```csharp
using System;
using Nethermind.Int256;

UInt256 amount = UInt256.Parse("1000000000000000000");
UInt256 total = amount * 3UL;
Console.WriteLine(total); // 3000000000000000000

Int256 delta = -42L;
Console.WriteLine(delta + (Int256)10L); // -32

// Reduce the full 512-bit product, without truncating it to 256 bits first.
UInt256 modulus = 97UL;
UInt256.MultiplyMod(UInt256.MaxValue, UInt256.MaxValue, modulus, out UInt256 remainder);
Console.WriteLine(remainder); // 11

// Write directly into a caller-owned buffer and read it back.
Span<byte> bytes = stackalloc byte[32];
total.ToBigEndian(bytes);
UInt256 decoded = new(bytes, isBigEndian: true);
Console.WriteLine(decoded == total); // True
```

## Choose the right arithmetic

| Need | API |
| --- | --- |
| Unsigned values from 0 to 2²⁵⁶ − 1 | `UInt256` |
| Signed values from −2²⁵⁵ to 2²⁵⁵ − 1 | `Int256` |
| Arithmetic, comparisons, bitwise operations, and shifts | Operators and named methods; see [`UInt256`](https://github.com/NethermindEth/int256/blob/main/src/Nethermind.Int256/UInt256.cs) and [`Int256`](https://github.com/NethermindEth/int256/blob/main/src/Nethermind.Int256/Int256.cs) |
| Detect unsigned overflow or underflow | `UInt256.AddOverflow` / `UInt256.SubtractUnderflow` |
| Modular addition, multiplication, or exponentiation | `AddMod`, `MultiplyMod`, `ExpMod` |
| Read or write binary values | Byte-span constructor, `ToBigEndian(Span<byte>)`, `ToLittleEndian(Span<byte>)` |
| Interoperate with arbitrary-precision code | Explicit conversions to and from `BigInteger` |

The arithmetic has explicit fixed-width semantics. For `UInt256`:

- `+` and `*` retain the low 256 bits on overflow.
- The `-` operator throws on underflow; `Subtract` returns the wrapped result, while `SubtractUnderflow` also reports whether underflow occurred.
- Division by zero throws `DivideByZeroException`.
- `AddMod` and `MultiplyMod` preserve the full intermediate value before reduction and throw for a zero modulus. `(a * b) % m` can therefore differ from `MultiplyMod(a, b, m, out result)`.

Use `BigInteger` when you need values of unbounded size. Use Int256 when 256 bits are part of your data model and fixed-width behavior matters.

## Performance

The [BenchmarkDotNet suite](https://github.com/NethermindEth/int256/tree/main/src/Nethermind.Int256.Benchmark) includes comparisons against `BigInteger` for arithmetic and modular operations, plus targeted benchmarks for operand widths, comparisons, and byte conversion.

Run the suite on your hardware, or select an operation:

```sh
dotnet run -c Release --project src/Nethermind.Int256.Benchmark -- --list flat
dotnet run -c Release --project src/Nethermind.Int256.Benchmark -- --filter '*MultiplyModUnsigned*'
```

Results depend on operand size, CPU instruction support, and runtime version. When sharing measurements, include those details, the commit, and the benchmark command so others can reproduce them.

## RISC-V zkVM variant

The NuGet package includes standard and RISC-V zkVM implementations with the same assembly identity. The standard implementation is selected by default. To select the RISC-V zkVM implementation, set the existing `EnableZkEvm` property in your project or shared `Directory.Build.props`:

```xml
<PropertyGroup>
  <EnableZkEvm>true</EnableZkEvm>
</PropertyGroup>
```

This is a build-time choice for RISC-V zkVM guest workloads; ordinary .NET applications can use the default.

## Build and contribute

Use the SDK specified in [`global.json`](https://github.com/NethermindEth/int256/blob/main/global.json). From the repository root:

```sh
dotnet build src/Nethermind.Int256/Nethermind.Int256.csproj -c Release
dotnet test --project src/Nethermind.Int256.Tests/Nethermind.Int256.Tests.csproj -c Release
```

Bug reports, regression tests, and performance improvements are welcome. For arithmetic bugs, include the operands, operation, expected result, and actual result. For optimizations, include reproducible before/after benchmarks and coverage for boundary values.

## Contributors

Thanks to everyone who helps maintain and improve Int256.

[![Int256 contributors](https://contrib.rocks/image?repo=NethermindEth/int256)](https://github.com/NethermindEth/int256/graphs/contributors)

## License

[MIT](https://github.com/NethermindEth/int256/blob/main/LICENSE). See [NOTICE](https://github.com/NethermindEth/int256/blob/main/NOTICE) for third-party notices.
