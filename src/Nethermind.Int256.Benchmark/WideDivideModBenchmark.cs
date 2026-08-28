// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Reflection;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Jobs;
using Nethermind.Int256;

namespace Nethermind.Int256.Benchmark;

public enum WideDivideShape
{
    Limb1PowerOfTwo,
    Limb2PowerOfTwo,
    Limb3PowerOfTwo,
    NonPowerOfTwo,
    CorpusWeighted,
}

/// <summary>
/// Compares the public divide and modulus paths for wide power-of-two divisors,
/// including a non-power-of-two miss and a mixed workload.
/// </summary>
[HideColumns("Job", "RatioSD", "Error")]
[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 3, warmupCount: 3, iterationCount: 10)]
[NoIntrinsicsJob(RuntimeMoniker.Net10_0, launchCount: 3, warmupCount: 3, iterationCount: 10)]
public class WideDivideModBenchmark
{
    private delegate void DivideDelegate(in UInt256 x, in UInt256 y, out UInt256 quotient, out UInt256 remainder);

    private const int BatchSize = 1024;

    private readonly UInt256[] _values = new UInt256[BatchSize];
    private readonly UInt256[] _divisors = new UInt256[BatchSize];
    private DivideDelegate _current = null!;
    private DivideDelegate _legacy128X86 = null!;
    private DivideDelegate _legacy128 = null!;
    private DivideDelegate _legacy192 = null!;
    private DivideDelegate _legacy256 = null!;

    [Params(
        WideDivideShape.Limb1PowerOfTwo,
        WideDivideShape.Limb2PowerOfTwo,
        WideDivideShape.Limb3PowerOfTwo,
        WideDivideShape.NonPowerOfTwo,
        WideDivideShape.CorpusWeighted)]
    public WideDivideShape Shape { get; set; }

    [GlobalSetup]
    public void Setup()
    {
        _current = Bind("DivideImpl");
        _legacy128X86 = Bind("DivideBy128BitsX86Base");
        _legacy128 = Bind("DivideBy128Bits");
        _legacy192 = Bind("DivideBy192Bits");
        _legacy256 = Bind("DivideBy256Bits");

        Random random = new(0x44495632);
        for (int i = 0; i < BatchSize; i++)
        {
            WideDivideShape shape = Shape == WideDivideShape.CorpusWeighted
                ? CorpusWeightedShape(i)
                : Shape;

            int shift = shape switch
            {
                WideDivideShape.Limb1PowerOfTwo => 64 + (i & 63),
                WideDivideShape.Limb2PowerOfTwo => 128 + (i & 63),
                WideDivideShape.Limb3PowerOfTwo => 192 + (i & 63),
                WideDivideShape.NonPowerOfTwo => (i % 3) switch
                {
                    0 => 127,
                    1 => 191,
                    _ => 255,
                },
                _ => throw new ArgumentOutOfRangeException(),
            };

            UInt256 divisor = PowerOfTwo(shift);
            if (shape == WideDivideShape.NonPowerOfTwo)
            {
                divisor = new UInt256(divisor.u0 + 3, divisor.u1, divisor.u2, divisor.u3);
            }

            _values[i] = RandomValueAbove(random, divisor);
            _divisors[i] = divisor;
        }

        for (int i = 0; i < BatchSize; i++)
        {
            _current(in _values[i], in _divisors[i], out UInt256 currentQuotient, out UInt256 currentRemainder);
            Legacy(in _values[i], in _divisors[i], out UInt256 legacyQuotient, out UInt256 legacyRemainder);
            if (!currentQuotient.Equals(legacyQuotient) || !currentRemainder.Equals(legacyRemainder))
            {
                throw new InvalidOperationException($"Division mismatch at index {i} for {Shape}.");
            }
        }
    }

    [Benchmark(Baseline = true, OperationsPerInvoke = BatchSize)]
    public ulong Divide_CurrentPath()
    {
        ulong checksum = 0;
        for (int i = 0; i < BatchSize; i++)
        {
            _current(in _values[i], in _divisors[i], out UInt256 quotient, out _);
            checksum ^= Fold(quotient);
        }

        return checksum;
    }

    [Benchmark(OperationsPerInvoke = BatchSize)]
    public ulong Divide_LegacyPath()
    {
        ulong checksum = 0;
        for (int i = 0; i < BatchSize; i++)
        {
            Legacy(in _values[i], in _divisors[i], out UInt256 quotient, out _);
            checksum ^= Fold(quotient);
        }

        return checksum;
    }

    [Benchmark(OperationsPerInvoke = BatchSize)]
    public ulong Mod_CurrentPath()
    {
        ulong checksum = 0;
        for (int i = 0; i < BatchSize; i++)
        {
            _current(in _values[i], in _divisors[i], out _, out UInt256 remainder);
            checksum ^= Fold(remainder);
        }

        return checksum;
    }

    [Benchmark(OperationsPerInvoke = BatchSize)]
    public ulong Mod_LegacyPath()
    {
        ulong checksum = 0;
        for (int i = 0; i < BatchSize; i++)
        {
            Legacy(in _values[i], in _divisors[i], out _, out UInt256 remainder);
            checksum ^= Fold(remainder);
        }

        return checksum;
    }

    private static DivideDelegate Bind(string name)
        => (DivideDelegate)typeof(UInt256)
            .GetMethod(name, BindingFlags.NonPublic | BindingFlags.Static)!
            .CreateDelegate(typeof(DivideDelegate));

    private void Legacy(in UInt256 value, in UInt256 divisor, out UInt256 quotient, out UInt256 remainder)
    {
        if (divisor.u3 != 0)
        {
            _legacy256(in value, in divisor, out quotient, out remainder);
        }
        else if (divisor.u2 != 0)
        {
            _legacy192(in value, in divisor, out quotient, out remainder);
        }
        else
        {
            if (System.Runtime.Intrinsics.X86.X86Base.X64.IsSupported)
            {
                _legacy128X86(in value, in divisor, out quotient, out remainder);
            }
            else
            {
                _legacy128(in value, in divisor, out quotient, out remainder);
            }
        }
    }

    private static WideDivideShape CorpusWeightedShape(int index)
    {
        // 717/1024 = 70.02% power-of-two hits, with the remainder covering
        // non-power-of-two 128-, 192-, and 256-bit divisors.
        int slot = (index * 37) & (BatchSize - 1);
        return slot < 717
            ? (slot % 6) switch
            {
                0 or 1 => WideDivideShape.Limb1PowerOfTwo,
                2 or 3 => WideDivideShape.Limb2PowerOfTwo,
                _ => WideDivideShape.Limb3PowerOfTwo,
            }
            : WideDivideShape.NonPowerOfTwo;
    }

    private static UInt256 PowerOfTwo(int shift)
    {
        int limb = shift >> 6;
        ulong value = 1UL << (shift & 63);
        return limb switch
        {
            1 => new UInt256(0, value),
            2 => new UInt256(0, 0, value),
            3 => new UInt256(0, 0, 0, value),
            _ => throw new ArgumentOutOfRangeException(nameof(shift)),
        };
    }

    private static UInt256 RandomValueAbove(Random random, in UInt256 divisor)
    {
        ulong u3 = NextUInt64(random) | divisor.u3 | 1UL;
        if (u3 <= divisor.u3)
        {
            u3 = divisor.u3 + 1;
        }

        return new UInt256(NextUInt64(random), NextUInt64(random), NextUInt64(random), u3);
    }

    private static ulong NextUInt64(Random random)
        => (ulong)random.NextInt64() ^ ((ulong)random.NextInt64() << 32);

    private static ulong Fold(in UInt256 value)
        => value.u0 ^ value.u1 ^ value.u2 ^ value.u3;
}
