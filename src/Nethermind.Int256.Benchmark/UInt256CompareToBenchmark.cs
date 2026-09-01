// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Numerics;
using System.Runtime.CompilerServices;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Jobs;
using Nethermind.Int256;

namespace Nethermind.Int256.Benchmark;

public enum UInt256CompareToCase
{
    Equal,
    DifferentLimb3,
    DifferentLimb2,
    DifferentLimb1,
    DifferentLimb0,
    Random,
}

/// <summary>
/// Compares UInt256.CompareTo with the pre-optimization comparison dispatch for equal values and
/// every possible first differing limb. No corpus weighting is included because no CompareTo incidence
/// capture is available.
/// </summary>
[HideColumns("Job", "RatioSD", "Error")]
[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 3, warmupCount: 3, iterationCount: 10)]
[NoIntrinsicsJob(RuntimeMoniker.Net10_0, launchCount: 3, warmupCount: 3, iterationCount: 10)]
public class UInt256CompareToBenchmark
{
    private const int BatchSize = 1024;

    private readonly UInt256[] _left = new UInt256[BatchSize];
    private readonly UInt256[] _right = new UInt256[BatchSize];

    [Params(
        UInt256CompareToCase.Equal,
        UInt256CompareToCase.DifferentLimb3,
        UInt256CompareToCase.DifferentLimb2,
        UInt256CompareToCase.DifferentLimb1,
        UInt256CompareToCase.DifferentLimb0,
        UInt256CompareToCase.Random)]
    public UInt256CompareToCase Case { get; set; }

    [GlobalSetup]
    public void Setup()
    {
        Random random = new(0xC0_4D_50);
        for (int i = 0; i < BatchSize; i++)
        {
            UInt256 left = RandomValue(random);
            _left[i] = left;
            _right[i] = CreateRight(random, left, i);

            int expected = Math.Sign(((BigInteger)left).CompareTo((BigInteger)_right[i]));
            int current = left.CompareTo(_right[i]);
            int legacy = LegacyCompareTo(in left, in _right[i]);
            if (current != expected || legacy != expected)
            {
                throw new InvalidOperationException($"Comparison mismatch at index {i} for {Case}.");
            }
        }
    }

    [Benchmark(Baseline = true, OperationsPerInvoke = BatchSize)]
    public int CompareTo_Legacy()
    {
        int checksum = 0;
        for (int i = 0; i < BatchSize; i++)
        {
            checksum = unchecked(checksum * 31 + LegacyCompareTo(in _left[i], in _right[i]));
        }

        return checksum;
    }

    [Benchmark(OperationsPerInvoke = BatchSize)]
    public int CompareTo_Current()
    {
        int checksum = 0;
        for (int i = 0; i < BatchSize; i++)
        {
            checksum = unchecked(checksum * 31 + _left[i].CompareTo(_right[i]));
        }

        return checksum;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static int LegacyCompareTo(in UInt256 a, in UInt256 b)
        => a < b ? -1 : a.Equals(b) ? 0 : 1;

    private UInt256 CreateRight(Random random, UInt256 left, int index)
    {
        switch (Case)
        {
            case UInt256CompareToCase.Equal:
                return left;
            case UInt256CompareToCase.DifferentLimb3:
                return new UInt256(left.u0, left.u1, left.u2, left.u3 ^ (1UL << (index & 63)));
            case UInt256CompareToCase.DifferentLimb2:
                return new UInt256(left.u0, left.u1, left.u2 ^ (1UL << (index & 63)), left.u3);
            case UInt256CompareToCase.DifferentLimb1:
                return new UInt256(left.u0, left.u1 ^ (1UL << (index & 63)), left.u2, left.u3);
            case UInt256CompareToCase.DifferentLimb0:
                return new UInt256(left.u0 ^ (1UL << (index & 63)), left.u1, left.u2, left.u3);
            case UInt256CompareToCase.Random:
                return RandomValue(random);
            default:
                throw new ArgumentOutOfRangeException();
        }
    }

    private static UInt256 RandomValue(Random random)
        => new(NextUInt64(random), NextUInt64(random), NextUInt64(random), NextUInt64(random));

    private static ulong NextUInt64(Random random)
        => (ulong)random.NextInt64() ^ ((ulong)random.NextInt64() << 32);
}
