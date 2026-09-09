// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Collections.Generic;
using System.Numerics;
using System.Security.Cryptography;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

/// <summary>Covers seed replacement and collision resistance across runs.</summary>
/// <remarks>Not parallelizable because installing a seed changes process-wide hash state.</remarks>
[NonParallelizable]
public class UInt256HashSeedTests
{
    private const int SampleCount = 4096;
    private static readonly UInt256 Sample = new(0xAB, 0xCD, 0xEF, 0x01);

    // The mixer's fold constants, needed to construct the inputs that zero a fold's factors.
    private const ulong FirstFactorConstant = 0x9E3779B97F4A7C15UL;
    private const ulong SecondFactorConstant = 0xBF58476D1CE4E5B9UL;
    private const ulong ClosingFactorConstant = 0x94D049BB133111EBUL;

    private static readonly UInt256 FirstSeed = new(0xAC320C7E23EBA0EFUL, 0x2E2473DDDBD55172UL,
        0x0C564BCB0D425343UL, 0x21FAE39C24D6EB90UL);
    private static readonly UInt256 SecondSeed = new(0x219B4AD604915E33UL, 0x28811B0595AE539EUL,
        0x5D38E6AFF0752500UL, 0xC8AEAC7F08A75C3DUL);

    /// <summary>Leaves the process hashing under fresh randomness rather than a seed pinned here.</summary>
    /// <remarks>
    /// <see cref="UInt256.SeedHashes"/> is write-only, so the seed this fixture replaced cannot be put
    /// back; drawing a new one keeps later fixtures off a seed whose hashes are known.
    /// </remarks>
    [OneTimeTearDown]
    public void DrawFreshSeed()
    {
        Span<byte> bytes = stackalloc byte[32];
        RandomNumberGenerator.Fill(bytes);
        UInt256.SeedHashes(new UInt256(bytes));
    }

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

    /// <summary>Checks that zeroing a fold's factor does not erase the word folded with it.</summary>
    /// <remarks>
    /// <c>low ^ high</c> of a widening product is zero whenever either factor is, and a factor is the
    /// limb masked with both the seed and the fold's constant, so a key hitting that value used to
    /// collapse every value of its partner onto one hash - and zeroing one factor in each half collapsed
    /// every key onto a single value. Reseeding does not answer it: the guest's seed is the public
    /// payload root, so the set is constructible for the payload in hand. <c>MultiplyFold</c> carries
    /// its factors past the product to prevent it.
    /// </remarks>
    [TestCase(0)]
    [TestCase(1)]
    [TestCase(2)]
    [TestCase(3)]
    public void MultiplyHash_ZeroingAFoldFactorDoesNotEraseItsPartner(int zeroedLimb)
    {
        HashSet<int> partnerVaries = new(SampleCount);
        HashSet<int> bothHalvesZeroed = new(SampleCount);
        int otherHalf = (zeroedLimb + 2) % 4;
        for (int value = 0; value < SampleCount; value++)
        {
            UInt256 key = WithLimb(default, zeroedLimb, Cancelling(zeroedLimb));
            partnerVaries.Add(WithLimb(key, zeroedLimb ^ 1, (uint)value).GetMultiplyHashCode(FirstSeed));

            // A factor zeroed in each half, so only the partner limbs carry the key.
            UInt256 pinned = WithLimb(key, otherHalf, Cancelling(otherHalf));
            bothHalvesZeroed.Add(WithLimb(pinned, zeroedLimb ^ 1, (uint)value).GetMultiplyHashCode(FirstSeed));
        }
        using (Assert.EnterMultipleScope())
        {
            Assert.That(partnerVaries.Count, Is.GreaterThan(SampleCount - 32), "partner limb");
            Assert.That(bothHalvesZeroed.Count, Is.GreaterThan(SampleCount - 32), "both halves zeroed");
        }
    }

    /// <summary>Checks that zeroing every fold's factor in turn does not reduce the hash to one limb.</summary>
    /// <remarks>
    /// A zero factor leaves <c>MultiplyFold</c> returning its other factor verbatim, so a known seed
    /// admits a key that chains three of them: <c>u0</c> and <c>u2</c> zero each half's first factor and
    /// <c>u1</c> carries the low half's output onto the outer fold's constant, leaving the hash an
    /// invertible function of <c>u3</c>. The values below all hashed to <c>0</c> before <c>FoldHash</c>
    /// closed with a fold of its own.
    /// </remarks>
    [Test]
    public void MultiplyHash_ChainingZeroedFoldFactorsDoesNotCollapse()
    {
        HashSet<int> hashes = new(SampleCount);
        for (int value = 0; value < SampleCount; value++)
        {
            // The last limb walks the values the closing XOR fold used to take to zero.
            ulong steered = (uint)value | ((ulong)(uint)value << 32);
            UInt256 key = new(Cancelling(0), FirstSeed.u1 ^ SecondFactorConstant ^ FirstFactorConstant,
                Cancelling(2), FirstSeed.u3 ^ steered);
            hashes.Add(key.GetMultiplyHashCode(FirstSeed));
        }
        Assert.That(hashes.Count, Is.GreaterThan(SampleCount - 32));
    }

    /// <summary>Checks that no small fold factor lets a limb erase the limb folded with it.</summary>
    /// <remarks>
    /// Carrying the factors past the product by XOR cancels when a factor is small: at <c>1</c> the
    /// product is the partner itself, so the fold returned a constant and every partner collided. The
    /// neighbours leaked too - this sweep left 609 of 4096 distinct at <c>3</c>. Adding the factors
    /// instead has no such value, so every case here spreads.
    /// </remarks>
    [Test]
    public void MultiplyHash_NoSmallFoldFactorErasesItsPartner(
        [Values(0, 1, 2, 3)] int limb,
        [Values(0UL, 1UL, 2UL, 3UL, 5UL, 9UL, ulong.MaxValue)] ulong factor)
    {
        int partner = limb ^ 1;
        UInt256 pinned = WithLimb(default, limb, FactorValue(limb, factor));
        HashSet<int> hashes = new(SampleCount);
        for (int value = 0; value < SampleCount; value++)
        {
            hashes.Add(WithLimb(pinned, partner, FirstSeed[partner] ^ ((ulong)(uint)value << 11))
                .GetMultiplyHashCode(FirstSeed));
        }
        Assert.That(hashes.Count, Is.GreaterThan(SampleCount - 32));
    }

    /// <summary>Checks that an inner fold's output cannot steer the outer fold into erasing a half.</summary>
    /// <remarks>
    /// Zeroing a half's first factor leaves the half equal to its second factor, so a known seed picks
    /// the half's value outright - including the one whose outer factor is <c>1</c>, which made the hash
    /// constant for every key in the other half. Same chain as
    /// <see cref="MultiplyHash_ChainingZeroedFoldFactorsDoesNotCollapse"/>, steered one past the
    /// constant that fold reaches for.
    /// </remarks>
    [Test]
    public void MultiplyHash_SteeringTheOuterFoldDoesNotEraseAHalf()
    {
        HashSet<int> hashes = new(SampleCount);
        for (int value = 0; value < SampleCount; value++)
        {
            UInt256 key = new(Cancelling(0),
                FirstSeed.u1 ^ SecondFactorConstant ^ FirstFactorConstant ^ 1UL,
                FirstSeed.u2 ^ (ulong)(uint)value,
                FirstSeed.u3 ^ ~(ulong)(uint)value);
            hashes.Add(key.GetMultiplyHashCode(FirstSeed));
        }
        Assert.That(hashes.Count, Is.GreaterThan(SampleCount - 32));
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
            ulong hash = ReferenceMum(ReferenceMum(a, b), ClosingFactorConstant);
            int expected = unchecked((int)(hash ^ (hash >> 32)));
            Assert.That(value.GetMultiplyHashCode(FirstSeed), Is.EqualTo(expected), $"input {value}");
        }
    }

    private static ulong ReferenceMum(ulong a, ulong b)
        => ReferenceFold(a ^ FirstFactorConstant, b ^ SecondFactorConstant);

    private static ulong ReferenceFold(ulong a, ulong b)
    {
        BigInteger product = (BigInteger)a * b;
        return unchecked(((ulong)(product & ulong.MaxValue) ^ (ulong)(product >> 64)) + a + b);
    }

    /// <summary>The limb value that zeroes the factor it is folded as, under <see cref="FirstSeed"/>.</summary>
    private static ulong Cancelling(int limb) => FactorValue(limb, 0);

    /// <summary>The limb value giving the factor it is folded as, under <see cref="FirstSeed"/>.</summary>
    private static ulong FactorValue(int limb, ulong factor)
        => FirstSeed[limb] ^ (limb % 2 == 0 ? FirstFactorConstant : SecondFactorConstant) ^ factor;

    private static UInt256 WithLimb(in UInt256 value, int limb, ulong replacement) => new(
        limb == 0 ? replacement : value.u0, limb == 1 ? replacement : value.u1,
        limb == 2 ? replacement : value.u2, limb == 3 ? replacement : value.u3);
}
