// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

/// <summary>
/// Covers <see cref="UInt256.Negate"/> and the explicit conversions from <see cref="double"/> and
/// <see cref="decimal"/>, which wrap a negative value modulo <c>2^256</c>. Every expected value comes from
/// <see cref="BigInteger"/>.
/// </summary>
[Parallelizable(ParallelScope.All)]
public class NegateTests
{
    private static readonly BigInteger TwoPow256 = BigInteger.One << 256;

    private static readonly double[] DoubleMagnitudes =
    [
        0.5, 1, 1.5, 2, 5, 255.75, 4294967296, 9007199254740993, 1e18,
        Math.ScaleB(1, 63), Math.ScaleB(1, 64) * 3, 1e30, Math.ScaleB(1, 128) + Math.ScaleB(1, 100), 1e60,
        Math.ScaleB(1, 200),
    ];

    private static readonly decimal[] DecimalMagnitudes =
    [
        0.5m, 1m, 1.5m, 5m, 123456789m, 18446744073709551615m, 18446744073709551616m, 12345678901234567890.5m,
        decimal.MaxValue,
    ];

    private static BigInteger Wrap(BigInteger value) => ((value % TwoPow256) + TwoPow256) % TwoPow256;

    private static UInt256 ToUInt256(BigInteger value) => (UInt256)Wrap(value);

    [Test]
    public void Negate_matches_BigInteger_on_limb_boundaries()
    {
        for (int bit = 0; bit < 256; bit++)
        {
            BigInteger power = BigInteger.One << bit;
            foreach (BigInteger value in new[] { power - 1, power, power + 1, TwoPow256 - power })
            {
                Assert.That((BigInteger)UInt256.Negate(ToUInt256(value)), Is.EqualTo(Wrap(-value)), value.ToString());
            }
        }
    }

    [Test]
    public void Negate_matches_BigInteger_on_random_values()
    {
        Random random = new(0x4E47);
        byte[] bytes = new byte[32];
        for (int i = 0; i < 10_000; i++)
        {
            random.NextBytes(bytes);
            int zeroLimbs = i & 3;
            bytes.AsSpan(32 - zeroLimbs * 8).Clear();
            BigInteger value = new(bytes, isUnsigned: true);
            Assert.That((BigInteger)UInt256.Negate(ToUInt256(value)), Is.EqualTo(Wrap(-value)), value.ToString());
        }
    }

    [Test]
    public void Negative_double_wraps([ValueSource(nameof(DoubleMagnitudes))] double magnitude)
    {
        BigInteger positive = (BigInteger)(UInt256)magnitude;

        Assert.That((BigInteger)(UInt256)(-magnitude), Is.EqualTo(Wrap(-positive)));
    }

    [Test]
    public void Negative_decimal_wraps([ValueSource(nameof(DecimalMagnitudes))] decimal magnitude)
    {
        BigInteger truncated = new(decimal.Truncate(magnitude));

        Assert.That((BigInteger)(UInt256)magnitude, Is.EqualTo(truncated));
        Assert.That((BigInteger)(UInt256)(-magnitude), Is.EqualTo(Wrap(-truncated)));
    }

    [Test]
    public void Negative_one_is_max_value()
    {
        Assert.That((UInt256)(-1.0), Is.EqualTo(UInt256.MaxValue));
        Assert.That((UInt256)(-1m), Is.EqualTo(UInt256.MaxValue));
    }
}
