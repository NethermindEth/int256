// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Reflection;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Jobs;
using Nethermind.Int256;

namespace Nethermind.Int256.Benchmark;

public enum NarrowMultiplyShape
{
    OneByTwo,
    TwoByTwo,
    ThreeByOne,
    ThreeByTwo,
    FullWidth,
    Weighted,
}

/// <summary>
/// Compares the production 256-to-512-bit multiplication dispatch with its
/// full-width fallback, including a full-width miss and a mixed workload.
/// </summary>
[HideColumns("Job", "RatioSD", "Error")]
[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 3, warmupCount: 3, iterationCount: 10)]
[NoIntrinsicsJob(RuntimeMoniker.Net10_0, launchCount: 3, warmupCount: 3, iterationCount: 10)]
public class NarrowMultiplyModBenchmark
{
    private delegate void MultiplyDelegate(in UInt256 x, in UInt256 y, out UInt256 low, out UInt256 high);

    private const int BatchSize = 1024;

    private readonly UInt256[] _left = new UInt256[BatchSize];
    private readonly UInt256[] _right = new UInt256[BatchSize];
    private MultiplyDelegate _current = null!;
    private MultiplyDelegate _large = null!;

    [Params(
        NarrowMultiplyShape.OneByTwo,
        NarrowMultiplyShape.TwoByTwo,
        NarrowMultiplyShape.ThreeByOne,
        NarrowMultiplyShape.ThreeByTwo,
        NarrowMultiplyShape.FullWidth,
        NarrowMultiplyShape.Weighted)]
    public NarrowMultiplyShape Shape { get; set; }

    [GlobalSetup]
    public void Setup()
    {
        _current = (MultiplyDelegate)typeof(UInt256)
            .GetMethod("Multiply256To512Bit", BindingFlags.NonPublic | BindingFlags.Static)!
            .CreateDelegate(typeof(MultiplyDelegate));
        _large = (MultiplyDelegate)typeof(UInt256)
            .GetMethod("Multiply256To512BitLarge", BindingFlags.NonPublic | BindingFlags.Static)!
            .CreateDelegate(typeof(MultiplyDelegate));

        Random random = new(0x4D554C54);

        for (int i = 0; i < BatchSize; i++)
        {
            NarrowMultiplyShape shape = Shape == NarrowMultiplyShape.Weighted
                ? (NarrowMultiplyShape)(i % 4)
                : Shape;

            (int leftWidth, int rightWidth) = shape switch
            {
                NarrowMultiplyShape.OneByTwo => (1, 2),
                NarrowMultiplyShape.TwoByTwo => (2, 2),
                NarrowMultiplyShape.ThreeByOne => (3, 1),
                NarrowMultiplyShape.ThreeByTwo => (3, 2),
                NarrowMultiplyShape.FullWidth => (4, 4),
                _ => throw new ArgumentOutOfRangeException(),
            };

            _left[i] = RandomValue(random, leftWidth);
            _right[i] = RandomValue(random, rightWidth);
        }

        for (int i = 0; i < BatchSize; i++)
        {
            _current(in _left[i], in _right[i], out UInt256 currentLow, out UInt256 currentHigh);
            _large(in _left[i], in _right[i], out UInt256 largeLow, out UInt256 largeHigh);
            if (!currentLow.Equals(largeLow) || !currentHigh.Equals(largeHigh))
            {
                throw new InvalidOperationException($"Product mismatch at index {i} for {Shape}.");
            }
        }
    }

    [Benchmark(Baseline = true, OperationsPerInvoke = BatchSize)]
    public ulong Multiply_CurrentDispatch()
    {
        ulong checksum = 0;
        for (int i = 0; i < BatchSize; i++)
        {
            _current(in _left[i], in _right[i], out UInt256 low, out UInt256 high);
            checksum ^= Fold(low) ^ Fold(high);
        }

        return checksum;
    }

    [Benchmark(OperationsPerInvoke = BatchSize)]
    public ulong Multiply_LargeFallback()
    {
        ulong checksum = 0;
        for (int i = 0; i < BatchSize; i++)
        {
            _large(in _left[i], in _right[i], out UInt256 low, out UInt256 high);
            checksum ^= Fold(low) ^ Fold(high);
        }

        return checksum;
    }

    private static UInt256 RandomValue(Random random, int width)
    {
        ulong u0 = NextUInt64(random);
        ulong u1 = width > 1 ? NextUInt64(random) : 0;
        ulong u2 = width > 2 ? NextUInt64(random) : 0;
        ulong u3 = width > 3 ? NextUInt64(random) : 0;

        switch (width)
        {
            case 1 when u0 == 0: u0 = 1; break;
            case 2 when u1 == 0: u1 = 1; break;
            case 3 when u2 == 0: u2 = 1; break;
            case 4 when u3 == 0: u3 = 1; break;
        }

        return new UInt256(u0, u1, u2, u3);
    }

    private static ulong NextUInt64(Random random)
        => (ulong)random.NextInt64() ^ ((ulong)random.NextInt64() << 32);

    private static ulong Fold(in UInt256 value)
        => value.u0 ^ value.u1 ^ value.u2 ^ value.u3;
}
