// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Runtime.CompilerServices;
using BenchmarkDotNet.Attributes;

namespace Nethermind.Int256.Benchmark;

/// <summary>
/// Platform-neutral subtraction shapes (the operand widths that dominate EVM traffic, the case that forces a
/// borrow through a zero limb, and a dependent chain) across the library's internal subtraction paths.
/// Runs on every ISA, so it is safe for the ARM benchmark CI suite (<c>--filter '*SubtractShapes*'</c>).
/// </summary>
/// <remarks>
/// Every variant sits behind a NoInlining wrapper so each is exactly one call, as production callers see it.
/// <c>Chain</c> is the scalar borrow chain that origin/main runs without AVX2, <c>Ladder</c> adds the one-limb
/// branch ladder, <c>V128</c> is the two-half vector path, <c>Hybrid</c> is the ladder in front of the vector
/// path and <c>HybridV</c> is the same with 16-byte stores in the ladder.
/// </remarks>
[WarmupCount(3)]
[IterationCount(10)]
[DisassemblyDiagnoser(maxDepth: 2, printSource: false)]
public class SubtractShapesBench
{
    private const int N = 16;

    private readonly UInt256[] _oneLimbA = new UInt256[N];
    private readonly UInt256[] _oneLimbB = new UInt256[N];
    private readonly UInt256[] _wideA = new UInt256[N];
    private readonly UInt256[] _wideB = new UInt256[N];
    private readonly UInt256[] _cascadeA = new UInt256[N];
    private readonly UInt256[] _cascadeB = new UInt256[N];
    private readonly UInt256[] _chainB = new UInt256[N];

    [GlobalSetup]
    public void Setup()
    {
        Random random = new(0x5AB7);
        for (int i = 0; i < N; i++)
        {
            // Wide left operand, one-limb right operand, no borrow out of the low limb
            _oneLimbA[i] = new UInt256(Next(random) | (1UL << 63), Next(random), Next(random), Next(random));
            _oneLimbB[i] = new UInt256(Next(random) >> 1);
            // Four random limbs each side, no underflow
            _wideA[i] = new UInt256(Next(random), Next(random), Next(random), Next(random) | (1UL << 63));
            _wideB[i] = new UInt256(Next(random), Next(random), Next(random), Next(random) >> 1);
            // Borrow that must ripple through a zero limb
            _cascadeA[i] = new UInt256(Next(random) >> 1, 0, Next(random) | 1, Next(random));
            _cascadeB[i] = new UInt256(Next(random) | (1UL << 63));
            // Small subtrahends so a chain starting at MaxValue never underflows
            _chainB[i] = new UInt256(Next(random) >> 8);
        }
    }

    private static ulong Next(Random random) => ((ulong)random.NextInt64() << 1) | (uint)random.Next(2);

    [Benchmark(OperationsPerInvoke = N)] public UInt256 OneLimb_Chain() => Run<ChainSub>(_oneLimbA, _oneLimbB);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 OneLimb_Ladder() => Run<LadderSub>(_oneLimbA, _oneLimbB);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 OneLimb_V128() => Run<V128Sub>(_oneLimbA, _oneLimbB);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 OneLimb_Hybrid() => Run<HybridSub>(_oneLimbA, _oneLimbB);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 OneLimb_HybridV() => Run<HybridVSub>(_oneLimbA, _oneLimbB);

    [Benchmark(OperationsPerInvoke = N)] public UInt256 Wide_Chain() => Run<ChainSub>(_wideA, _wideB);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 Wide_Ladder() => Run<LadderSub>(_wideA, _wideB);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 Wide_V128() => Run<V128Sub>(_wideA, _wideB);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 Wide_Hybrid() => Run<HybridSub>(_wideA, _wideB);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 Wide_HybridV() => Run<HybridVSub>(_wideA, _wideB);

    [Benchmark(OperationsPerInvoke = N)] public UInt256 ZeroLimbBorrow_Chain() => Run<ChainSub>(_cascadeA, _cascadeB);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 ZeroLimbBorrow_Ladder() => Run<LadderSub>(_cascadeA, _cascadeB);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 ZeroLimbBorrow_V128() => Run<V128Sub>(_cascadeA, _cascadeB);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 ZeroLimbBorrow_Hybrid() => Run<HybridSub>(_cascadeA, _cascadeB);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 ZeroLimbBorrow_HybridV() => Run<HybridVSub>(_cascadeA, _cascadeB);

    [Benchmark(OperationsPerInvoke = N)] public UInt256 DependentChain_Chain() => RunChain<ChainSub>(_chainB);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 DependentChain_Ladder() => RunChain<LadderSub>(_chainB);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 DependentChain_V128() => RunChain<V128Sub>(_chainB);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 DependentChain_Hybrid() => RunChain<HybridSub>(_chainB);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 DependentChain_HybridV() => RunChain<HybridVSub>(_chainB);

    private static UInt256 Run<TSub>(UInt256[] a, UInt256[] b) where TSub : struct, ISub
    {
        UInt256 acc = default;
        ulong flags = 0;
        for (int i = 0; i < N; i++)
        {
            flags += TSub.Sub(in a[i], in b[i], out UInt256 r) ? 1UL : 0UL;
            acc ^= r;
        }
        return acc ^ new UInt256(flags);
    }

    private static UInt256 RunChain<TSub>(UInt256[] b) where TSub : struct, ISub
    {
        UInt256 x = UInt256.MaxValue;
        for (int i = 0; i < N; i++)
        {
            TSub.Sub(in x, in b[i], out x);
        }
        return x;
    }

    private interface ISub
    {
        static abstract bool Sub(in UInt256 a, in UInt256 b, out UInt256 res);
    }

    private struct ChainSub : ISub
    {
        [MethodImpl(MethodImplOptions.NoInlining)]
        public static bool Sub(in UInt256 a, in UInt256 b, out UInt256 res) => UInt256.SubtractScalarChain(in a, in b, out res);
    }

    private struct LadderSub : ISub
    {
        [MethodImpl(MethodImplOptions.NoInlining)]
        public static bool Sub(in UInt256 a, in UInt256 b, out UInt256 res) => UInt256.SubtractScalar(in a, in b, out res);
    }

    private struct V128Sub : ISub
    {
        [MethodImpl(MethodImplOptions.NoInlining)]
        public static bool Sub(in UInt256 a, in UInt256 b, out UInt256 res) => UInt256.SubtractVector128(in a, in b, out res);
    }

    private struct HybridSub : ISub
    {
        [MethodImpl(MethodImplOptions.NoInlining)]
        public static bool Sub(in UInt256 a, in UInt256 b, out UInt256 res) => UInt256.SubtractHybrid(in a, in b, out res);
    }

    private struct HybridVSub : ISub
    {
        [MethodImpl(MethodImplOptions.NoInlining)]
        public static bool Sub(in UInt256 a, in UInt256 b, out UInt256 res) => UInt256.SubtractHybridVectorStore(in a, in b, out res);
    }
}
