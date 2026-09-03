// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Runtime.CompilerServices;
using BenchmarkDotNet.Attributes;

namespace Nethermind.Int256.Benchmark;

/// <summary>
/// Platform-neutral remainder shapes: one per (dividend width, divisor width) pair, since the number of
/// Knuth digits is the difference between them, plus the power-of-two divisors, the answers that come
/// straight from the entry compare, and a mixed corpus that has to predict its way through all of them.
/// Runs on every ISA, so it is safe for the ARM benchmark CI suite (<c>--filter '*ModShapes*'</c>).
/// </summary>
[WarmupCount(3)]
[IterationCount(10)]
[DisassemblyDiagnoser(maxDepth: 2, printSource: false)]
public class ModShapesBench
{
    private const int N = 64;

    private readonly UInt256[][] _dividends = new UInt256[(int)Shape.Count][];
    private readonly UInt256[][] _divisors = new UInt256[(int)Shape.Count][];

    private enum Shape
    {
        FourByFour, FourByThree, FourByTwo, FourByOne,
        ThreeByThree, ThreeByTwo, TwoByTwo, TwoByOne, OneByOne,
        DivisorAboveHalf, PowerOfTwo, DividendBelowDivisor, Mixed,
        Count,
    }

    [GlobalSetup]
    public void Setup()
    {
        Random random = new(0x40D5);
        for (int shape = 0; shape < (int)Shape.Count; shape++)
        {
            _dividends[shape] = new UInt256[N];
            _divisors[shape] = new UInt256[N];
        }

        for (int i = 0; i < N; i++)
        {
            Fill(Shape.FourByFour, i, 4, 4, random);
            Fill(Shape.FourByThree, i, 4, 3, random);
            Fill(Shape.FourByTwo, i, 4, 2, random);
            Fill(Shape.FourByOne, i, 4, 1, random);
            Fill(Shape.ThreeByThree, i, 3, 3, random);
            Fill(Shape.ThreeByTwo, i, 3, 2, random);
            Fill(Shape.TwoByTwo, i, 2, 2, random);
            Fill(Shape.TwoByOne, i, 2, 1, random);
            Fill(Shape.OneByOne, i, 1, 1, random);

            // A divisor at or above 2^255 makes the quotient 1, so the remainder is one subtract
            UInt256 big = new(Next(random), Next(random), Next(random), Next(random) | (1UL << 63));
            UInt256 bigger = new(Next(random), Next(random), Next(random), Next(random) | (1UL << 63));
            Order(ref bigger, ref big);
            _dividends[(int)Shape.DivisorAboveHalf][i] = bigger;
            _divisors[(int)Shape.DivisorAboveHalf][i] = big;

            // One power-of-two divisor per limb, so every masking path is exercised
            _dividends[(int)Shape.PowerOfTwo][i] = new UInt256(Next(random), Next(random), Next(random), Next(random));
            _divisors[(int)Shape.PowerOfTwo][i] = PowerOfTwo(1 + (i * 61 % 255));

            // Answered by the entry compare, without reaching a kernel
            UInt256 small = new(Next(random), Next(random), Next(random), Next(random));
            UInt256 large = new(Next(random), Next(random), Next(random), Next(random));
            Order(ref large, ref small);
            _dividends[(int)Shape.DividendBelowDivisor][i] = small;
            _divisors[(int)Shape.DividendBelowDivisor][i] = large;
        }

        // Every shape above, interleaved
        for (int i = 0; i < N; i++)
        {
            int source = i % (int)Shape.Mixed;
            _dividends[(int)Shape.Mixed][i] = _dividends[source][i];
            _divisors[(int)Shape.Mixed][i] = _divisors[source][i];
        }
    }

    private void Fill(Shape shape, int i, int dividendLimbs, int divisorLimbs, Random random)
    {
        UInt256 x = Random(dividendLimbs, random);
        UInt256 y = Random(divisorLimbs, random);
        if (dividendLimbs == divisorLimbs)
        {
            Order(ref x, ref y);
        }

        _dividends[(int)shape][i] = x;
        _divisors[(int)shape][i] = y;
    }

    // Leaves the larger value in x, and never equal, so every shape really divides
    private static void Order(ref UInt256 x, ref UInt256 y)
    {
        if (x < y)
        {
            (x, y) = (y, x);
        }

        if (x == y)
        {
            x |= UInt256.One;
            y &= ~UInt256.One;
        }
    }

    private static UInt256 Random(int limbs, Random random)
    {
        ulong u0 = Next(random);
        ulong u1 = limbs >= 2 ? Next(random) : 0;
        ulong u2 = limbs >= 3 ? Next(random) : 0;
        ulong u3 = limbs >= 4 ? Next(random) : 0;

        // Force the top limb non-zero so the value has the width the shape names, and keep a
        // four-limb divisor below 2^255 so it reaches Knuth rather than the single-subtract shortcut
        switch (limbs)
        {
            case 1: u0 |= 2; break;
            case 2: u1 |= 1; break;
            case 3: u2 |= 1; break;
            default: u3 = (u3 | 1) & ~(1UL << 63); break;
        }

        return new UInt256(u0, u1, u2, u3);
    }

    private static UInt256 PowerOfTwo(int bit) => bit < 64
        ? new UInt256(1UL << bit)
        : bit < 128 ? new UInt256(0, 1UL << (bit - 64))
        : bit < 192 ? new UInt256(0, 0, 1UL << (bit - 128))
        : new UInt256(0, 0, 0, 1UL << (bit - 192));

    private static ulong Next(Random random) => ((ulong)random.NextInt64() << 1) | (uint)random.Next(2);

    [Benchmark(OperationsPerInvoke = N)] public UInt256 FourByFour() => Run(Shape.FourByFour);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 FourByThree() => Run(Shape.FourByThree);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 FourByTwo() => Run(Shape.FourByTwo);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 FourByOne() => Run(Shape.FourByOne);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 ThreeByThree() => Run(Shape.ThreeByThree);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 ThreeByTwo() => Run(Shape.ThreeByTwo);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 TwoByTwo() => Run(Shape.TwoByTwo);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 TwoByOne() => Run(Shape.TwoByOne);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 OneByOne() => Run(Shape.OneByOne);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 DivisorAboveHalf() => Run(Shape.DivisorAboveHalf);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 PowerOfTwoDivisor() => Run(Shape.PowerOfTwo);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 DividendBelowDivisor() => Run(Shape.DividendBelowDivisor);
    [Benchmark(OperationsPerInvoke = N)] public UInt256 MixedCorpus() => Run(Shape.Mixed);

    [Benchmark(OperationsPerInvoke = N)]
    public UInt256 SignedMixedCorpus()
    {
        UInt256[] a = _dividends[(int)Shape.Mixed];
        UInt256[] b = _divisors[(int)Shape.Mixed];
        Int256 acc = default;
        for (int i = 0; i < N; i++)
        {
            SignedMod(in Unsafe.As<UInt256, Int256>(ref a[i]), in Unsafe.As<UInt256, Int256>(ref b[i]), out Int256 r);
            acc = new Int256(Unsafe.As<Int256, UInt256>(ref acc) ^ Unsafe.As<Int256, UInt256>(ref r));
        }
        return Unsafe.As<Int256, UInt256>(ref acc);
    }

    private UInt256 Run(Shape shape)
    {
        UInt256[] a = _dividends[(int)shape];
        UInt256[] b = _divisors[(int)shape];
        UInt256 acc = default;
        for (int i = 0; i < N; i++)
        {
            Mod(in a[i], in b[i], out UInt256 r);
            acc ^= r;
        }
        return acc;
    }

    // One real call per operation, as production callers see it
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void Mod(in UInt256 x, in UInt256 y, out UInt256 res) => UInt256.Mod(in x, in y, out res);

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void SignedMod(in Int256 x, in Int256 y, out Int256 res) => Int256.Mod(in x, in y, out res);
}
