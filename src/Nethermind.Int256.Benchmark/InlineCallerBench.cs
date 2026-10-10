// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Runtime.CompilerServices;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Configs;
using BenchmarkDotNet.Jobs;

namespace Nethermind.Int256.Benchmark;

/// <summary>
/// Shifts and wrapping subtraction called from a caller that is not inlined, as an EVM opcode handler calls them:
/// whether the library call stays a call in that caller.
/// </summary>
/// <remarks>
/// With PGO the JIT inlines a hot call site whatever the attributes. The NoPGO job shows a caller compiled from
/// size heuristics alone, as the EVM handlers are (explicit tail calls switch them straight to FullOpts).
/// </remarks>
[Config(typeof(Config))]
public class InlineCallerBench
{
    private const int N = 16;

    private sealed class Config : ManualConfig
    {
        public Config()
        {
            AddJob(Job.Default.WithWarmupCount(3).WithIterationCount(10).WithId("PGO"));
            AddJob(Job.Default.WithWarmupCount(3).WithIterationCount(10).WithEnvironmentVariables(new EnvironmentVariable("DOTNET_TieredPGO", "0")).WithId("NoPGO"));
        }
    }

    private readonly UInt256[] _values = new UInt256[N];
    private readonly UInt256[] _results = new UInt256[N];
    private readonly UInt256[] _wideA = new UInt256[N];
    private readonly UInt256[] _wideB = new UInt256[N];
    private readonly UInt256[] _cascadeA = new UInt256[N];
    private readonly UInt256[] _cascadeB = new UInt256[N];

    // Shift counts as Solidity emits them (byte multiples for selectors, addresses and packed fields) plus a few odd ones.
    private readonly int[] _counts = [8, 16, 32, 64, 96, 128, 160, 192, 224, 248, 1, 255, 72, 136, 200, 3];

    [GlobalSetup]
    public void Setup()
    {
        Random random = new(0x5B1F7);
        for (int i = 0; i < N; i++)
        {
            _values[i] = new UInt256(Next(random), Next(random), Next(random), Next(random));
            // Four random limbs each side, no underflow
            _wideA[i] = new UInt256(Next(random), Next(random), Next(random), Next(random) | (1UL << 63));
            _wideB[i] = new UInt256(Next(random), Next(random), Next(random), Next(random) >> 1);
            // Borrow that must ripple through a zero limb
            _cascadeA[i] = new UInt256(Next(random) >> 1, 0, Next(random) | 1, Next(random));
            _cascadeB[i] = new UInt256(Next(random) | (1UL << 63));
        }
    }

    private static ulong Next(Random random) => ((ulong)random.NextInt64() << 1) | (uint)random.Next(2);

    [Benchmark(OperationsPerInvoke = N)]
    public void Lsh()
    {
        for (int i = 0; i < N; i++) ShiftLeft(in _values[i], _counts[i], out _results[i]);
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void Rsh()
    {
        for (int i = 0; i < N; i++) ShiftRight(in _values[i], _counts[i], out _results[i]);
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void SubtractWide()
    {
        for (int i = 0; i < N; i++) Subtract(in _wideA[i], in _wideB[i], out _results[i]);
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void SubtractBorrowThroughZeroLimb()
    {
        for (int i = 0; i < N; i++) Subtract(in _cascadeA[i], in _cascadeB[i], out _results[i]);
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void ShiftLeft(in UInt256 x, int n, out UInt256 res) => UInt256.Lsh(in x, n, out res);

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void ShiftRight(in UInt256 x, int n, out UInt256 res) => UInt256.Rsh(in x, n, out res);

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void Subtract(in UInt256 a, in UInt256 b, out UInt256 res) => UInt256.Subtract(in a, in b, out res);
}
