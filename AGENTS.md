# AGENTS instructions

High-performance 256-bit integer types for .NET. See [global.json](./global.json) and [src](./src/) directory for the project requirements and configuration.

## Project structure

- [src/Nethermind.Int256](./src/Nethermind.Int256/): The main codebase. `UInt256` is the core implementation; `Int256` wraps it.
- [src/Nethermind.Int256.Tests](./src/Nethermind.Int256.Tests/): The tests. Arithmetic is verified against `System.Numerics.BigInteger`.
- [src/Nethermind.Int256.Benchmark](./src/Nethermind.Int256.Benchmark/): The BenchmarkDotNet suite.
- [test-publish.yml](./.github/workflows/test-publish.yml): Runs the tests across platforms and hardware intrinsics configurations, and optionally publishes on NuGet.
- [benchmark.yml](./.github/workflows/benchmark.yml): Runs selected benchmarks on demand.

## Coding guidelines

- Follow [.editorconfig](./.editorconfig).
- Do not assume; measure, research, ask if unsure.
- Keep comments short and to the point.
- Add tests for new code and bug fixes; cover boundary values.
- Use conventional commits; keep scoped and imperative.
- Keep the standard (`*.std.cs`) and RISC-V zkVM (`*.zkevm.cs`) variants in sync; [Directory.Build.targets](./src/Directory.Build.targets) selects one per build and the package ships both.
- Treat Arm64 as a first-class target alongside x64: hardware-accelerated paths must cover both architectures, unless benchmarks show acceleration is slower on one of them.
- Keep the software fallbacks correct; CI also runs the tests with hardware intrinsics disabled.
- Back performance changes with reproducible before/after benchmarks.
- Prefer the latest versions of GitHub Actions and runners.
- Update [THIRD-PARTY-NOTICES](./THIRD-PARTY-NOTICES) when introducing a dependency if needed.
- Keep [AGENTS.md](./AGENTS.md) in sync with the ongoing development.
