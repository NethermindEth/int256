// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

/// <summary>
/// Covers <see cref="UInt256.Divide"/> and <see cref="UInt256.Mod"/> by a divisor that fits one limb, where a
/// leading limb below the divisor is a zero quotient digit and its divide is skipped. Every expected value
/// comes from <see cref="BigInteger"/>.
/// </summary>
/// <remarks>
/// A divide is skipped only while the running remainder is zero and the limb is below the divisor. The cases
/// put the dividend's top limb on both sides of the divisor, and on it, at every limb position and for divisors
/// of every bit length.
/// </remarks>
[Parallelizable(ParallelScope.All)]
public class DivideByOneLimbTopTests
{
    private static readonly BigInteger TwoPow256 = BigInteger.One << 256;

    [Test]
    public void Divisor_top_limb_boundaries_match_BigInteger()
    {
        const int bits = 64;
        Random random = new(0x0D1F + bits);
        for (int shift = 0; shift < 64; shift++)
        {
            int divisorBits = bits - shift;
            for (int sample = 0; sample < 8; sample++)
            {
                BigInteger divisor = RandomBits(random, divisorBits) | (BigInteger.One << (divisorBits - 1)) | BigInteger.One;
                if (divisor < 2) continue;
                for (int position = 0; divisorBits + 64 * position <= 256; position++)
                {
                    BigInteger aligned = divisor << (64 * position);
                    foreach (int delta in new[] { -2, -1, 0, 1, 2 })
                    {
                        AssertDivide(aligned + delta, divisor);
                        AssertDivide((aligned >> 1) + delta, divisor);
                        AssertDivide((aligned << 1) + delta, divisor);
                    }

                    AssertDivide(aligned - (aligned >> 64) - 1, divisor);
                    AssertDivide(aligned + divisor - 1, divisor);
                }
            }
        }
    }

    [Test]
    public void Short_dividends_match_BigInteger()
    {
        const int bits = 64;
        Random random = new(0x5D1F + bits);
        for (int i = 0; i < 20_000; i++)
        {
            int divisorBits = bits - (i % 64);
            BigInteger divisor = RandomBits(random, divisorBits) | (BigInteger.One << (divisorBits - 1));
            if (divisor < 2) continue;
            int dividendBits = divisorBits + random.Next(0, 257 - divisorBits);
            BigInteger dividend = (i % 3) switch
            {
                0 => RandomBits(random, dividendBits) | (BigInteger.One << (dividendBits - 1)),
                1 => RandomBits(random, dividendBits - divisorBits + 1) * divisor + (i % 2 == 0 ? BigInteger.Zero : divisor - 1),
                _ => RandomBits(random, dividendBits),
            };
            AssertDivide(dividend, divisor);
        }
    }

    private static void AssertDivide(BigInteger dividend, BigInteger divisor)
    {
        if (dividend.Sign < 0 || dividend >= TwoPow256) return;

        UInt256 x = FromBig(dividend);
        UInt256 y = FromBig(divisor);
        BigInteger expected = dividend / divisor;

        UInt256.Divide(in x, in y, out UInt256 quotient);
        if (ToBig(quotient) != expected)
        {
            Assert.Fail($"{dividend:x} / {divisor:x}\n  expected {expected:x}\n  actual   {ToBig(quotient):x}");
        }

        UInt256 aliasX = x;
        UInt256.Divide(in aliasX, in y, out aliasX);
        Assert.That(ToBig(aliasX), Is.EqualTo(expected), $"{dividend:x} / {divisor:x} into the dividend");

        UInt256 aliasY = y;
        UInt256.Divide(in x, in aliasY, out aliasY);
        Assert.That(ToBig(aliasY), Is.EqualTo(expected), $"{dividend:x} / {divisor:x} into the divisor");

        UInt256.Mod(in x, in y, out UInt256 remainder);
        Assert.That(ToBig(remainder), Is.EqualTo(dividend % divisor), $"{dividend:x} % {divisor:x}");
    }

    private static BigInteger RandomBits(Random random, int bits)
    {
        if (bits <= 0) return BigInteger.Zero;
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
