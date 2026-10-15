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
- Do not change [global.json](./global.json) unless asked.
- Keep `UInt256`'s `u0`..`u3` fields in declaration order (sequential layout, little-endian limbs): span casts and vector loads depend on it.
- Pass operands by `in` and results by `out` on hot paths, following the existing `Add(in a, in b, out res)` style.
- Keep the standard (`*.std.cs`) and RISC-V zkVM (`*.zkevm.cs`) variants in sync; [Directory.Build.targets](./src/Directory.Build.targets) selects one per build and the package ships both.
- Treat ARM64 as a first-class target alongside x64: hardware-accelerated paths must cover both architectures, unless benchmarks show acceleration is slower on one of them.
- Keep the software fallbacks correct; CI also runs the tests with hardware intrinsics disabled.
- Implement generic math (`INumber<T>`, `*.numerics.cs`) as explicit interface members that forward to the public `in` operators; a public by-value overload would rebind existing callers.
  - Unchecked members keep the public operators' semantics (`UInt256` subtraction throws on underflow); checked members throw on any overflow.
  - The interfaces pass operands by value; the JIT keeps those copies off the stack only while each is read one way (all limbs or all vectors). When touching shared kernels, check the generic path's disassembly, not just the direct one.
- Keep `BigInteger` off any path an AOT guest can reach from formatting or interpolation, such as `TryFormat`: the zkVM image links whatever those reference.
- Back performance changes with reproducible before/after benchmarks.
- Prefer the latest versions of GitHub Actions and runners.
- Update [THIRD-PARTY-NOTICES](./THIRD-PARTY-NOTICES) when introducing a dependency if needed.
- Keep [AGENTS.md](./AGENTS.md) in sync with the ongoing development.

## Testing

- Put tests for a new kernel or concern in their own file; use `UInt256TestsTemplate<T>` and the `TestNumbers`/`*Ops` case sources for broad checks against `BigInteger` that should also cover `Int256`.
- Match the file's naming style; use NUnit `Assert.That` constraints and no Arrange/Act/Assert comments.
- Do not leave tests disabled or commented out.
- Run from `src/Nethermind.Int256.Tests` with `dotnet test`; add `-p:EnableZkEvm=true` for the zkVM variant and set `DOTNET_EnableHWIntrinsic=0` for the software fallbacks. When filtering, check the run count to confirm tests actually ran.
## Verification

- Consume pinned LeanCIL from `verification/lakefile.toml`; keep CIL infrastructure upstream.
- Register completed method/profile proofs in `verification/manifests/gates.json`.
- Validate gates with `verification/Verify.ps1 -Action Verify -Method <id> -Profile <profile>`; a supporting-library build or successful extraction is not a compiled-method certificate.
- Preserve independent arithmetic, overlap, finite-return, and caller-memory contracts when porting proofs. Report unsupported extraction or composition upstream instead of changing production C# to suit a proof.
