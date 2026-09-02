// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Runtime.CompilerServices;
using BenchmarkDotNet.Attributes;

namespace Nethermind.Int256.Benchmark;

/// <summary>
/// Platform-neutral subtraction shapes: the operand widths that dominate EVM traffic, the case that forces a
/// borrow through a zero limb, and a dependent chain. Runs on every ISA, so it is safe for the ARM benchmark
/// CI suite (<c>--filter '*SubtractShapes*'</c>).
/// </summary>
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

    [Benchmark(OperationsPerInvoke = N)]
    public UInt256 OneLimbRight() => Run(_oneLimbA, _oneLimbB);

    [Benchmark(OperationsPerInvoke = N)]
    public UInt256 Wide() => Run(_wideA, _wideB);

    [Benchmark(OperationsPerInvoke = N)]
    public UInt256 BorrowThroughZeroLimb() => Run(_cascadeA, _cascadeB);

    [Benchmark(OperationsPerInvoke = N)]
    public UInt256 DependentChain()
    {
        UInt256 x = UInt256.MaxValue;
        for (int i = 0; i < N; i++)
        {
            Subtract(in x, in _chainB[i], out x);
        }
        return x;
    }

    private static UInt256 Run(UInt256[] a, UInt256[] b)
    {
        UInt256 acc = default;
        ulong flags = 0;
        for (int i = 0; i < N; i++)
        {
            flags += Subtract(in a[i], in b[i], out UInt256 r) ? 1UL : 0UL;
            acc ^= r;
        }
        return acc ^ new UInt256(flags);
    }

    // One real call per operation, as production callers see it
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static bool Subtract(in UInt256 a, in UInt256 b, out UInt256 res) => UInt256.SubtractUnderflow(in a, in b, out res);
}
