// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Collections.Generic;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

/// <summary>Covers <see cref="UInt256.SeedHashes(uint)"/>, which both builds honour.</summary>
/// <remarks>
/// Not parallelizable: the seed is process-wide state, and these are the only tests that move it. They
/// leave the last one installed rather than restoring a default they cannot name - the standard build's
/// is drawn per process - which nothing else in the suite minds, since no test pins a hash to a literal.
/// </remarks>
[NonParallelizable]
public class UInt256HashSeedTests
{
    private const int SampleCount = 4096;

    private static readonly UInt256 Sample = new(0xAB, 0xCD, 0xEF, 0x01);

    [TestCase(1u)]
    [TestCase(0xDEADBEEFu)]
    [TestCase(uint.MaxValue)]
    public void SeedHashes_MovesTheHashOfAGivenValue(uint seed)
    {
        int before = Sample.GetHashCode();

        UInt256.SeedHashes(seed);

        Assert.That(Sample.GetHashCode(), Is.Not.EqualTo(before));
    }

    [Test]
    public void SeedHashes_SeparatesTwoRuns()
    {
        UInt256.SeedHashes(1);
        int first = Sample.GetHashCode();

        UInt256.SeedHashes(2);

        Assert.That(Sample.GetHashCode(), Is.Not.EqualTo(first));
    }

    /// <remarks>
    /// The seed replaces what came before rather than accumulating onto it, so a run is defined by its
    /// last seed alone and two runs given the same one agree - whatever either did beforehand.
    /// </remarks>
    [Test]
    public void SeedHashes_DependsOnlyOnTheLastSeed()
    {
        UInt256.SeedHashes(1);
        int first = Sample.GetHashCode();

        UInt256.SeedHashes(2);
        UInt256.SeedHashes(1);

        Assert.That(Sample.GetHashCode(), Is.EqualTo(first));
    }

    /// <remarks>
    /// A seed that reached only the final fold would leave the distribution to the constants behind it;
    /// this is the sweep <c>UInt256Tests</c> gives the built-in seeds, run against an installed one.
    /// </remarks>
    [Test]
    public void SeedHashes_KeepsHashesDistributed()
    {
        UInt256.SeedHashes(0xDEADBEEF);

        HashSet<int> hashes = new(SampleCount);
        for (int value = 0; value < SampleCount; value++)
        {
            hashes.Add(new UInt256(0, 0, 0, (uint)value).GetHashCode());
        }

        Assert.That(hashes.Count, Is.GreaterThan(SampleCount - 32),
            $"seeded hashing produced {hashes.Count}/{SampleCount} distinct hashes");
    }
}
