// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Collections.Generic;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

/// <summary>Covers seed replacement and collision resistance across runs.</summary>
/// <remarks>Not parallelizable because installing a seed changes process-wide hash state.</remarks>
[NonParallelizable]
public class UInt256HashSeedTests
{
    private const int SampleCount = 4096;
    private static readonly UInt256 Sample = new(0xAB, 0xCD, 0xEF, 0x01);

    private static readonly UInt256 FirstSeed = new(0xAC320C7E23EBA0EFUL, 0x2E2473DDDBD55172UL,
        0x0C564BCB0D425343UL, 0x21FAE39C24D6EB90UL);
    private static readonly UInt256 SecondSeed = new(0x219B4AD604915E33UL, 0x28811B0595AE539EUL,
        0x5D38E6AFF0752500UL, 0xC8AEAC7F08A75C3DUL);

    /// <summary>Checks that each seed limb affects the public hash.</summary>
    [TestCase(0)]
    [TestCase(1)]
    [TestCase(2)]
    [TestCase(3)]
    public void SeedHashes_UsesEveryLimb(int limb)
    {
        UInt256.SeedHashes(FirstSeed);
        int before = Sample.GetHashCode();
        UInt256 changed = WithLimb(FirstSeed, limb, FirstSeed[limb] ^ 0x8000000000000000UL);
        UInt256.SeedHashes(changed);
        Assert.That(Sample.GetHashCode(), Is.Not.EqualTo(before));
    }

    /// <summary>Checks that reinstalling a seed reproduces its hashes.</summary>
    [Test]
    public void SeedHashes_DependsOnlyOnTheLastSeed()
    {
        UInt256.SeedHashes(FirstSeed);
        int first = Sample.GetHashCode();
        UInt256.SeedHashes(SecondSeed);
        UInt256.SeedHashes(FirstSeed);
        Assert.That(Sample.GetHashCode(), Is.EqualTo(first));
    }

    /// <summary>Checks sequential and linearly related inputs in each input limb.</summary>
    [TestCase(0, false)]
    [TestCase(1, false)]
    [TestCase(2, false)]
    [TestCase(3, false)]
    [TestCase(0, true)]
    [TestCase(1, true)]
    [TestCase(2, true)]
    [TestCase(3, true)]
    public void SeedHashes_DistributesInputs(int limb, bool structuredInputs)
    {
        foreach (UInt256 seed in new[] { FirstSeed, SecondSeed })
        {
            UInt256.SeedHashes(seed);
            HashSet<int> publicHashes = new(SampleCount);
            HashSet<int> multiplyHashes = new(SampleCount);
            for (int value = 0; value < SampleCount; value++)
            {
                ulong input = (uint)value;
                if (structuredInputs)
                {
                    input = 0;
                    // XOR combinations of shifted copies exercise linearly related inputs.
                    for (int bit = 0; bit < 12; bit++)
                        if ((value & (1 << bit)) != 0) input ^= 0x105EC76F1UL << bit;
                }
                UInt256 key = WithLimb(default, limb, input);
                publicHashes.Add(key.GetHashCode());
                multiplyHashes.Add(key.GetMultiplyHashCode(seed));
            }
            using (Assert.EnterMultipleScope())
            {
                Assert.That(publicHashes.Count, Is.GreaterThan(SampleCount - 32), "public hash");
                Assert.That(multiplyHashes.Count, Is.GreaterThan(SampleCount - 32), "scalar mixer");
            }
        }
    }

    /// <summary>Checks that replacing the full seed breaks a seed-specific cancellation attack.</summary>
    [TestCase(0)]
    [TestCase(1)]
    [TestCase(2)]
    [TestCase(3)]
    public void MultiplyHash_ReseedingBreaksCollisionSet(int cancelledLimb)
    {
        HashSet<int> before = new(SampleCount);
        HashSet<int> after = new(SampleCount);
        for (int value = 0; value < SampleCount; value++)
        {
            UInt256 key = WithLimb(default, cancelledLimb, FirstSeed[cancelledLimb]);
            key = WithLimb(key, cancelledLimb ^ 1, (uint)value);
            before.Add(key.GetMultiplyHashCode(FirstSeed));
            after.Add(key.GetMultiplyHashCode(SecondSeed));
        }
        using (Assert.EnterMultipleScope())
        {
            Assert.That(before.Count, Is.EqualTo(1), "constructed collision set");
            Assert.That(after.Count, Is.GreaterThan(SampleCount - 32), "replacement seed");
        }
    }

    /// <summary>Checks the scalar mixer against an independent widening-product reference.</summary>
    [Test]
    public void MultiplyHash_MatchesBigIntegerReference()
    {
        foreach (UInt256 value in new[] { UInt256.Zero, UInt256.One, UInt256.MaxValue, Sample, FirstSeed })
        {
            ulong a = ReferenceFold(value.u0 ^ FirstSeed.u0, value.u1 ^ FirstSeed.u1);
            ulong b = ReferenceFold(value.u2 ^ FirstSeed.u2, value.u3 ^ FirstSeed.u3);
            ulong hash = ReferenceFold(a ^ 0x9E3779B97F4A7C15UL, b ^ 0xBF58476D1CE4E5B9UL);
            int expected = unchecked((int)(hash ^ (hash >> 32)));
            Assert.That(value.GetMultiplyHashCode(FirstSeed), Is.EqualTo(expected), $"input {value}");
        }
    }

    private static ulong ReferenceFold(ulong a, ulong b)
    {
        BigInteger product = (BigInteger)a * b;
        return (ulong)(product & ulong.MaxValue) ^ (ulong)(product >> 64);
    }

    private static UInt256 WithLimb(in UInt256 value, int limb, ulong replacement) => new(
        limb == 0 ? replacement : value.u0, limb == 1 ? replacement : value.u1,
        limb == 2 ? replacement : value.u2, limb == 3 ? replacement : value.u3);
}
