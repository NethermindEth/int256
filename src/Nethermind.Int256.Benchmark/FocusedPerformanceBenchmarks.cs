// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
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
    Weighted,
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
    private const int BatchSize = 1024;

    private readonly UInt256[] _values = new UInt256[BatchSize];
    private readonly UInt256[] _divisors = new UInt256[BatchSize];

    [Params(
        WideDivideShape.Limb1PowerOfTwo,
        WideDivideShape.Limb2PowerOfTwo,
        WideDivideShape.Limb3PowerOfTwo,
        WideDivideShape.NonPowerOfTwo,
        WideDivideShape.Weighted)]
    public WideDivideShape Shape { get; set; }

    [GlobalSetup]
    public void Setup()
    {
        Random random = new(0x44495632);
        for (int i = 0; i < BatchSize; i++)
        {
            WideDivideShape shape = Shape == WideDivideShape.Weighted
                ? (WideDivideShape)(i % 4)
                : Shape;

            int shift = shape switch
            {
                WideDivideShape.Limb1PowerOfTwo => 65,
                WideDivideShape.Limb2PowerOfTwo => 129,
                WideDivideShape.Limb3PowerOfTwo => 193,
                WideDivideShape.NonPowerOfTwo => 129,
                _ => throw new ArgumentOutOfRangeException(),
            };

            UInt256 divisor = PowerOfTwo(shift);
            if (shape == WideDivideShape.NonPowerOfTwo)
            {
                divisor = new UInt256(divisor.u0 + 3, divisor.u1, divisor.u2, divisor.u3);
            }

            _values[i] = RandomValue(random);
            _divisors[i] = divisor;
        }
    }

    [Benchmark(OperationsPerInvoke = BatchSize)]
    public ulong Divide()
    {
        ulong checksum = 0;
        for (int i = 0; i < BatchSize; i++)
        {
            UInt256.Divide(in _values[i], in _divisors[i], out UInt256 quotient);
            checksum ^= Fold(quotient);
        }

        return checksum;
    }

    [Benchmark(OperationsPerInvoke = BatchSize)]
    public ulong Mod()
    {
        ulong checksum = 0;
        for (int i = 0; i < BatchSize; i++)
        {
            UInt256.Mod(in _values[i], in _divisors[i], out UInt256 remainder);
            checksum ^= Fold(remainder);
        }

        return checksum;
    }

    [Benchmark(OperationsPerInvoke = BatchSize)]
    public ulong DivideAndMod()
    {
        ulong checksum = 0;
        for (int i = 0; i < BatchSize; i++)
        {
            UInt256.Divide(in _values[i], in _divisors[i], out UInt256 quotient);
            UInt256.Mod(in _values[i], in _divisors[i], out UInt256 remainder);
            checksum ^= Fold(quotient) ^ Fold(remainder);
        }

        return checksum;
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

    private static UInt256 RandomValue(Random random)
        => new(NextUInt64(random), NextUInt64(random), NextUInt64(random), NextUInt64(random));

    private static ulong NextUInt64(Random random)
        => (ulong)random.NextInt64() ^ ((ulong)random.NextInt64() << 32);

    private static ulong Fold(in UInt256 value)
        => value.u0 ^ value.u1 ^ value.u2 ^ value.u3;
}
