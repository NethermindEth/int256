// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

/// <summary>
/// Covers the 128-by-64 reciprocal division that ARM64 and the zkVM use for each quotient digit: the seed table
/// lookup of the reciprocal and both corrections of the digit. Every expected value comes from
/// <see cref="BigInteger"/>.
/// </summary>
/// <remarks>
/// The divisors cover every seed table entry (the top nine bits of the normalised divisor) with low bits at both
/// ends and random, at every normalisation shift. Dividends with remainders next to the divisor and next to zero
/// take each correction both ways.
/// </remarks>
[Parallelizable(ParallelScope.All)]
public class ReciprocalDivisionTests
{
    private static readonly BigInteger TwoPow256 = BigInteger.One << 256;

    [Test]
    public void Every_seed_entry_matches_BigInteger()
    {
        Random random = new(0x2B71);
        for (ulong entry = 256; entry < 512; entry++)
        {
            ulong top = entry << 55;
            foreach (ulong low in new[] { 0UL, (1UL << 55) - 1, NextUlong(random) & ((1UL << 55) - 1) })
            {
                ulong normalised = top | low;
                int shift = (int)(entry % 64);
                ulong divisor = Math.Max(normalised >> shift, 2UL);
                AssertDivisor(random, divisor);
            }
        }
    }

    [Test]
    public void Random_divisors_match_BigInteger()
    {
        Random random = new(0x2B72);
        for (int i = 0; i < 4_000; i++)
        {
            int bits = 2 + i % 63;
            ulong divisor = (NextUlong(random) >> (64 - bits)) | (1UL << (bits - 1));
            AssertDivisor(random, divisor);
        }
    }

    [Test]
    public void Two_limb_divisors_match_BigInteger()
    {
        Random random = new(0x2B73);
        ulong[] edges = [0, 1, ulong.MaxValue, ulong.MaxValue - 1, 1UL << 63];
        for (int i = 0; i < 6_000; i++)
        {
            int bits = 65 + i % 64;
            BigInteger divisor = RandomBits(random, bits) | (BigInteger.One << (bits - 1));
            if (i % 5 == 0)
            {
                // Limbs at the ends of their range, before and after normalisation.
                BigInteger top = i % 10 == 0 ? ulong.MaxValue : BigInteger.One << 63;
                divisor = ((top << 64) | edges[i / 5 % edges.Length]) >> (i % 64);
                if (divisor < BigInteger.One << 64) continue;
            }

            AssertTwoLimbDivisor(random, divisor);
        }
    }

    private static void AssertTwoLimbDivisor(Random random, BigInteger d)
    {
        BigInteger maxQuotient = (TwoPow256 - 1) / d;
        AssertAll(RandomBits(random, 256), d);
        AssertAll(TwoPow256 - 1, d);
        AssertAll(maxQuotient * d, d);
        AssertAll(maxQuotient * d - 1, d);
        AssertAll(RandomBits(random, 128) * d + (d - 1), d);
        AssertAll(RandomBits(random, 64) * d + 1, d);
        AssertAll(((BigInteger.One << 64) - 1) * d + (d - 1), d);
        AssertAll(d + RandomBits(random, 64), d);
    }

    private static void AssertDivisor(Random random, ulong divisor)
    {
        BigInteger d = divisor;
        BigInteger maxQuotient = (TwoPow256 - 1) / d;
        AssertAll(RandomBits(random, 256), d);
        AssertAll(TwoPow256 - 1, d);
        AssertAll(maxQuotient * d, d);
        AssertAll(maxQuotient * d - 1, d);
        AssertAll(RandomBits(random, 192) * d + (d - 1), d);
        AssertAll(RandomBits(random, 192) * d + 1, d);
        AssertAll(RandomBits(random, 128), d);
    }

    private static void AssertAll(BigInteger dividend, BigInteger divisor)
    {
        if (dividend.Sign < 0 || dividend >= TwoPow256) return;

        UInt256 x = FromBig(dividend);
        UInt256 y = FromBig(divisor);

        UInt256.Divide(in x, in y, out UInt256 quotient);
        Assert.That(ToBig(quotient), Is.EqualTo(dividend / divisor), $"{dividend:x} / {divisor:x}");

        UInt256.Mod(in x, in y, out UInt256 remainder);
        Assert.That(ToBig(remainder), Is.EqualTo(dividend % divisor), $"{dividend:x} % {divisor:x}");

        UInt256 factor = FromBig((dividend >> 7) ^ (TwoPow256 - 1 - dividend));
        UInt256.MultiplyMod(in x, in factor, in y, out UInt256 product);
        Assert.That(ToBig(product), Is.EqualTo(dividend * ToBig(factor) % divisor), $"{dividend:x} * {ToBig(factor):x} % {divisor:x}");
    }

    private static ulong NextUlong(Random random) => ((ulong)random.NextInt64() << 1) | (uint)random.Next(2);

    private static BigInteger RandomBits(Random random, int bits)
    {
        byte[] bytes = new byte[(bits + 7) / 8 + 1];
        random.NextBytes(bytes);
        bytes[^1] = 0;
        return new BigInteger(bytes) & ((BigInteger.One << bits) - 1);
    }

    private static BigInteger ToBig(in UInt256 v)
        => v.u0 | ((BigInteger)v.u1 << 64) | ((BigInteger)v.u2 << 128) | ((BigInteger)v.u3 << 192);

    private static UInt256 FromBig(BigInteger v) => new(
        (ulong)(v & ulong.MaxValue), (ulong)((v >> 64) & ulong.MaxValue),
        (ulong)((v >> 128) & ulong.MaxValue), (ulong)((v >> 192) & ulong.MaxValue));
}
