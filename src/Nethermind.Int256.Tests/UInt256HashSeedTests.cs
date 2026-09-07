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

    public static IEnumerable<TestCaseData> SeedBits()
    {
        for (int bit = 0; bit < 256; bit++)
        {
            yield return new TestCaseData(bit, false);
            yield return new TestCaseData(bit, true);
        }
    }

    /// <summary>Checks individual bits and paired changes that cancel when the seed halves are XOR-folded.</summary>
    [TestCaseSource(nameof(SeedBits))]
    public void SeedHashes_UsesEverySeedBit(int bit, bool paired)
    {
        UInt256.SeedHashes(FirstSeed);
        int before = Sample.GetHashCode();
        UInt256 changed = FirstSeed ^ (UInt256.One << bit);
        if (paired) changed ^= UInt256.One << ((bit + 128) % 256);
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

    /// <summary>Checks that matching the seed in one limb does not erase the limb folded with it.</summary>
    /// <remarks>
    /// <c>low ^ high</c> of a widening product is zero whenever either factor is, so a key matching the
    /// seed in one limb used to collapse every value of that limb's partner onto one hash, and matching
    /// one limb of each half collapsed every key onto a single value. Reseeding does not answer it: the
    /// guest's seed is the public payload root, so the set is constructible for the payload in hand.
    /// <c>MultiplyFold</c> carries its factors past the product to prevent it.
    /// </remarks>
    [TestCase(0)]
    [TestCase(1)]
    [TestCase(2)]
    [TestCase(3)]
    public void MultiplyHash_MatchingTheSeedDoesNotCancelALimb(int matchedLimb)
    {
        HashSet<int> partnerVaries = new(SampleCount);
        HashSet<int> bothHalvesMatched = new(SampleCount);
        for (int value = 0; value < SampleCount; value++)
        {
            UInt256 key = WithLimb(default, matchedLimb, FirstSeed[matchedLimb]);
            partnerVaries.Add(WithLimb(key, matchedLimb ^ 1, (uint)value).GetMultiplyHashCode(FirstSeed));

            // Both halves pinned to the seed, so only the partner limbs carry the key.
            UInt256 pinned = WithLimb(WithLimb(default, matchedLimb, FirstSeed[matchedLimb]),
                (matchedLimb + 2) % 4, FirstSeed[(matchedLimb + 2) % 4]);
            bothHalvesMatched.Add(WithLimb(pinned, matchedLimb ^ 1, (uint)value).GetMultiplyHashCode(FirstSeed));
        }
        using (Assert.EnterMultipleScope())
        {
            Assert.That(partnerVaries.Count, Is.GreaterThan(SampleCount - 32), "partner limb");
            Assert.That(bothHalvesMatched.Count, Is.GreaterThan(SampleCount - 32), "both halves matched");
        }
    }

    /// <summary>Checks that a half's two seed-masked words are not interchangeable.</summary>
    /// <remarks>
    /// The widening product is commutative, so folding a pair without position-separating constants gave
    /// a half the same value when its two seed-masked words were exchanged - a colliding pair for every
    /// key, once the seed is known. The pairs go through <c>MumFold</c>'s asymmetric constants instead.
    /// </remarks>
    [TestCase(0)]
    [TestCase(2)]
    public void MultiplyHash_ExchangingAHalfsWordsChangesTheHash(int lowLimb)
    {
        for (int value = 1; value <= SampleCount; value++)
        {
            ulong first = (uint)value;
            ulong second = ~first;
            UInt256 key = WithLimb(WithLimb(default, lowLimb, first ^ FirstSeed[lowLimb]),
                lowLimb + 1, second ^ FirstSeed[lowLimb + 1]);
            UInt256 exchanged = WithLimb(WithLimb(default, lowLimb, second ^ FirstSeed[lowLimb]),
                lowLimb + 1, first ^ FirstSeed[lowLimb + 1]);

            Assert.That(key.GetMultiplyHashCode(FirstSeed),
                Is.Not.EqualTo(exchanged.GetMultiplyHashCode(FirstSeed)), $"value {value}");
        }
    }

    /// <summary>Checks the scalar mixer against an independent widening-product reference.</summary>
    [Test]
    public void MultiplyHash_MatchesBigIntegerReference()
    {
        foreach (UInt256 value in new[] { UInt256.Zero, UInt256.One, UInt256.MaxValue, Sample, FirstSeed })
        {
            ulong a = ReferenceMum(value.u0 ^ FirstSeed.u0, value.u1 ^ FirstSeed.u1);
            ulong b = ReferenceMum(value.u2 ^ FirstSeed.u2, value.u3 ^ FirstSeed.u3);
            ulong hash = ReferenceMum(a, b);
            int expected = unchecked((int)(hash ^ (hash >> 32)));
            Assert.That(value.GetMultiplyHashCode(FirstSeed), Is.EqualTo(expected), $"input {value}");
        }
    }

    private static ulong ReferenceMum(ulong a, ulong b)
        => ReferenceFold(a ^ 0x9E3779B97F4A7C15UL, b ^ 0xBF58476D1CE4E5B9UL);

    private static ulong ReferenceFold(ulong a, ulong b)
    {
        BigInteger product = (BigInteger)a * b;
        return (ulong)(product & ulong.MaxValue) ^ (ulong)(product >> 64) ^ a ^ b;
    }

    private static UInt256 WithLimb(in UInt256 value, int limb, ulong replacement) => new(
        limb == 0 ? replacement : value.u0, limb == 1 ? replacement : value.u1,
        limb == 2 ? replacement : value.u2, limb == 3 ? replacement : value.u3);
}
