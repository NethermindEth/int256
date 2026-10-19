# Int256

[![Tests / Publish](https://github.com/nethermindeth/int256/actions/workflows/test-publish.yml/badge.svg)](https://github.com/nethermindeth/int256/actions/workflows/test-publish.yml)
[![Nethermind.Numerics.Int256](https://img.shields.io/nuget/v/Nethermind.Numerics.Int256)](https://www.nuget.org/packages/Nethermind.Numerics.Int256)

**High-performance 256-bit arithmetic for .NET.**

Int256 provides `UInt256` and `Int256`: unsigned and signed 256-bit value types used by the [Nethermind Ethereum execution client](https://github.com/NethermindEth/nethermind). Bring the arithmetic behind EVM execution to your own .NET applications, from blockchain tooling to binary protocols and numeric workloads that need up to 256 bits.

## Why Int256?

- **256 bits, stored inline.** Readonly structs with a 32-byte representation. Core arithmetic works directly on fixed-width limbs without allocating a backing array for each result.
- **Full-width modular arithmetic.** `UInt256.AddMod` and `UInt256.MultiplyMod` preserve the intermediate sum or product before reduction, including products up to 512 bits wide.
- **Optimized for the hardware you run.** Specialized x64 and ARM64 paths use hardware intrinsics where available, with software fallbacks. A separate RISC-V zkVM build tunes execution for guest workloads.
- **Made for hot paths.** `in`/`out` arithmetic APIs and span-based byte conversion let callers control copies and buffers.
- **Correctness you can inspect.** Tests compare arithmetic against `System.Numerics.BigInteger`, and CI exercises Windows, Linux, macOS, ARM64, and configurations with hardware intrinsics disabled.

## Get started

```sh
dotnet add package Nethermind.Numerics.Int256
```

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
| Detect unsigned overflow or underflow | `UInt256.AddOverflow` / `UInt256.SubtractUnderflow` |
| Modular addition, multiplication, or exponentiation | `AddMod`, `MultiplyMod`, `ExpMod` |
| Read or write binary values | Byte-span constructor, `ToBigEndian(Span<byte>)`, `ToLittleEndian(Span<byte>)` |
| Interoperate with arbitrary-precision code | Explicit conversions to and from `BigInteger` |
| Write code generic over number types | `INumber<T>` and `IBinaryInteger<T>`, with `CreateChecked`, `CreateSaturating`, and `CreateTruncating` |

The arithmetic has explicit fixed-width semantics. For `UInt256`:

- `+` and `*` retain the low 256 bits on overflow.
- The `-` operator throws on underflow; `Subtract` returns the wrapped result, while `SubtractUnderflow` also reports whether underflow occurred.
- Division by zero throws `DivideByZeroException`.
- `AddMod` and `MultiplyMod` throw for a zero modulus, and `(a * b) % m` can differ from `MultiplyMod(a, b, m, out result)`.

`Int256` operators wrap in two's complement, including `Int256.MinValue / -1`, which gives `MinValue` as the EVM's `SDIV` does.

`Divide` truncates toward zero and `Mod` takes the sign of the dividend. Both throw `DivideByZeroException` for a zero divisor.

In a `checked` context, or a project built with `CheckForOverflowUnderflow`, the operators that would otherwise wrap throw `OverflowException` instead, as they do for `long` and `Int128`. So does the explicit conversion of a negative `Int256` to `UInt256`.

Code written against `INumber<T>` or `IBinaryInteger<T>` gets the same semantics. Shifts follow EVM rules there too: a count of 256 or more gives zero (or the sign fill for `Int256 >>`) rather than being masked to the width.

Both types are `ISpanFormattable` and `IUtf8SpanFormattable`. The `D`, `G`, `X`, and `B` formats are written directly from the limbs, as `UInt128` and `Int128` write them, without allocating when formatting into a span; a negative `Int256` shows all 256 bits under `X` and `B`. The culture formats (`N`, `C`, `E`, `F`, `P`, `G` with a precision, and custom formats) go through `BigInteger` in the standard build and throw `FormatException` in the RISC-V zkVM build, which keeps `BigInteger` out of guest images.

See [`UInt256`](https://github.com/NethermindEth/int256/blob/main/src/Nethermind.Int256/UInt256.cs) and [`Int256`](https://github.com/NethermindEth/int256/blob/main/src/Nethermind.Int256/Int256.cs) for the full API.

## Performance

The [BenchmarkDotNet suite](https://github.com/NethermindEth/int256/tree/main/src/Nethermind.Int256.Benchmark) includes comparisons against `BigInteger` for arithmetic and modular operations, plus targeted benchmarks for operand widths, comparisons, and byte conversion.

Run the suite on your hardware, or select an operation:

```sh
dotnet run -c Release --project src/Nethermind.Int256.Benchmark -- --list flat
dotnet run -c Release --project src/Nethermind.Int256.Benchmark -- --filter '*MultiplyModUnsigned*'
```

Results depend on operand size, CPU instruction support, and runtime version.

## RISC-V zkVM variant

The NuGet package includes standard and RISC-V zkVM implementations with the same assembly identity, selected at build time. The standard implementation is the default. For RISC-V zkVM guest workloads, set `EnableZkEvm` in your project or a shared `Directory.Build.props`:

```xml
<PropertyGroup>
  <EnableZkEvm>true</EnableZkEvm>
</PropertyGroup>
```

## Build and contribute

Use the SDK specified in [`global.json`](https://github.com/NethermindEth/int256/blob/main/global.json). From the repository root:

```sh
dotnet build src/Nethermind.Int256/Nethermind.Int256.csproj -c Release
dotnet test --project src/Nethermind.Int256.Tests/Nethermind.Int256.Tests.csproj -c Release
```

Bug reports, regression tests, and performance improvements are welcome. For arithmetic bugs, include the operands, operation, expected result, and actual result. For optimizations, include before/after benchmarks with the hardware, runtime version, commit, and benchmark command, plus coverage for boundary values.

## License

This project is licensed under the [MIT](https://github.com/NethermindEth/int256/blob/main/LICENSE) license.

Portions of `UInt256` incorporate material from [uint256](https://github.com/holiman/uint256), used under BSD-3-Clause. See [THIRD-PARTY-NOTICES](https://github.com/NethermindEth/int256/blob/main/THIRD-PARTY-NOTICES) for the full text.
