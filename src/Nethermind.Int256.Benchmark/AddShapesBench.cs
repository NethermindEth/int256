// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Runtime.CompilerServices;
using BenchmarkDotNet.Attributes;

namespace Nethermind.Int256.Benchmark;

/// <summary>
/// Platform-neutral addition shapes: the operand widths that dominate EVM traffic, the case that forces a
/// carry through a full limb, and a dependent chain. Runs on every ISA, so it is safe for the ARM benchmark
/// CI suite (<c>--filter '*AddShapes*'</c>).
/// </summary>
[WarmupCount(3)]
[IterationCount(10)]
[DisassemblyDiagnoser(maxDepth: 2, printSource: false)]
public class AddShapesBench
{
    private const int N = 16;

    private readonly UInt256[] _oneLimbA = new UInt256[N];
    private readonly UInt256[] _oneLimbB = new UInt256[N];
    private readonly UInt256[] _oneLimbRightA = new UInt256[N];
    private readonly UInt256[] _oneLimbRightB = new UInt256[N];
    private readonly UInt256[] _oneLimbLeftA = new UInt256[N];
    private readonly UInt256[] _oneLimbLeftB = new UInt256[N];
    private readonly UInt256[] _wideA = new UInt256[N];
    private readonly UInt256[] _wideB = new UInt256[N];
    private readonly UInt256[] _cascadeA = new UInt256[N];
    private readonly UInt256[] _cascadeB = new UInt256[N];
    private readonly UInt256[] _chainB = new UInt256[N];

    [GlobalSetup]
    public void Setup()
    {
        Random random = new(0xADD);
        for (int i = 0; i < N; i++)
        {
            // Both operands fit in one limb; the sum may carry into the second
            _oneLimbA[i] = new UInt256(Next(random));
            _oneLimbB[i] = new UInt256(Next(random));
            // Wide left operand, one-limb right operand, no carry out of the low limb
            _oneLimbRightA[i] = new UInt256(Next(random) >> 1, Next(random), Next(random), Next(random));
            _oneLimbRightB[i] = new UInt256(Next(random) >> 1);
            // One-limb left operand, wide right operand: the same ladder with the operands swapped
            _oneLimbLeftA[i] = new UInt256(Next(random) >> 1);
            _oneLimbLeftB[i] = new UInt256(Next(random) >> 1, Next(random), Next(random), Next(random));
            // Four random limbs each side, no overflow
            _wideA[i] = new UInt256(Next(random), Next(random), Next(random), Next(random) >> 1);
            _wideB[i] = new UInt256(Next(random), Next(random), Next(random), Next(random) >> 1);
            // Carry that must ripple through a full limb
            _cascadeA[i] = new UInt256(Next(random) | (1UL << 63), ulong.MaxValue, Next(random), Next(random) >> 1);
            _cascadeB[i] = new UInt256(Next(random) | (1UL << 63));
            // Small addends so a chain starting at zero stays far from overflow
            _chainB[i] = new UInt256(Next(random) >> 8);
        }
    }

    private static ulong Next(Random random) => ((ulong)random.NextInt64() << 1) | (uint)random.Next(2);

    [Benchmark(OperationsPerInvoke = N)]
    public UInt256 OneLimbBoth() => Run(_oneLimbA, _oneLimbB);

    [Benchmark(OperationsPerInvoke = N)]
    public UInt256 OneLimbRight() => Run(_oneLimbRightA, _oneLimbRightB);

    [Benchmark(OperationsPerInvoke = N)]
    public UInt256 OneLimbLeft() => Run(_oneLimbLeftA, _oneLimbLeftB);

    [Benchmark(OperationsPerInvoke = N)]
    public UInt256 Wide() => Run(_wideA, _wideB);

    [Benchmark(OperationsPerInvoke = N)]
    public UInt256 CarryThroughFullLimb() => Run(_cascadeA, _cascadeB);

    [Benchmark(OperationsPerInvoke = N)]
    public UInt256 DependentChain()
    {
        UInt256 x = UInt256.Zero;
        for (int i = 0; i < N; i++)
        {
            Add(in x, in _chainB[i], out x);
        }
        return x;
    }

    private static UInt256 Run(UInt256[] a, UInt256[] b)
    {
        UInt256 acc = default;
        ulong flags = 0;
        for (int i = 0; i < N; i++)
        {
            flags += Add(in a[i], in b[i], out UInt256 r) ? 1UL : 0UL;
            acc ^= r;
        }
        return acc ^ new UInt256(flags);
    }

    // One real call per operation, as production callers see it
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static bool Add(in UInt256 a, in UInt256 b, out UInt256 res) => UInt256.AddOverflow(in a, in b, out res);
}
