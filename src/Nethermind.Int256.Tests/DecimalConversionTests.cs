// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Globalization;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

/// <summary>
/// Covers the explicit <see cref="decimal"/> conversions of <see cref="UInt256"/> and
/// <see cref="UInt256.ToDecimal(IFormatProvider)"/>. Every expected value comes from <see cref="BigInteger"/>.
/// </summary>
[Parallelizable(ParallelScope.All)]
public class DecimalConversionTests
{
    private static readonly BigInteger DecimalMax = new(decimal.MaxValue);

    private static readonly BigInteger[] Edges =
    [
        BigInteger.Zero,
        BigInteger.One,
        ulong.MaxValue,
        (BigInteger)ulong.MaxValue + 1,
        (BigInteger.One << 95) - 1,
        BigInteger.One << 95,
        (BigInteger.One << 96) - 2,
        (BigInteger.One << 96) - 1,
        BigInteger.One << 96,
        (BigInteger.One << 96) + 1,
        (BigInteger.One << 128) - 1,
        BigInteger.One << 128,
        BigInteger.One << 192,
        (BigInteger.One << 255) + 7,
        (BigInteger.One << 256) - 1,
    ];

    [Test]
    public void Edge_values_match_BigInteger()
    {
        foreach (BigInteger value in Edges)
        {
            AssertToDecimal(value);
        }
    }

    [Test]
    public void Random_values_match_BigInteger()
    {
        Random random = new(0xDEC1);
        byte[] bytes = new byte[32];
        for (int i = 0; i < 20_000; i++)
        {
            random.NextBytes(bytes);
            int bits = random.Next(0, 257);
            BigInteger value = new BigInteger(bytes, isUnsigned: true) >> (256 - bits);
            AssertToDecimal(value);
        }
    }

    [Test]
    public void Decimal_to_UInt256_matches_BigInteger()
    {
        decimal[] values = [0m, 0.9m, 1m, 1.5m, 12345678901234567890.5m, 1234567890123456789012345678.9m, decimal.MaxValue];
        foreach (decimal value in values)
        {
            Assert.That((BigInteger)(UInt256)value, Is.EqualTo(new BigInteger(decimal.Truncate(value))), value.ToString(CultureInfo.InvariantCulture));
        }

        Random random = new(0xDEC2);
        for (int i = 0; i < 20_000; i++)
        {
            decimal value = new(random.Next(), random.Next(), random.Next(), false, (byte)random.Next(0, 29));
            Assert.That((BigInteger)(UInt256)value, Is.EqualTo(new BigInteger(decimal.Truncate(value))), value.ToString(CultureInfo.InvariantCulture));
        }
    }

    [Test]
    public void Conversions_do_not_allocate()
    {
        UInt256 value = new(ulong.MaxValue, uint.MaxValue, 0, 0);
        decimal source = 1234567890123456789012345678.9m;
        UInt256 truncated = UInt256.Parse("1234567890123456789012345678");
        int mismatches = 0;
        long[] allocated = [long.MaxValue, long.MaxValue, long.MaxValue];
        // A tier-up during a round can allocate on its own, so the quietest round is the one judged.
        for (int round = 0; round < 5; round++)
        {
            long start = GC.GetAllocatedBytesForCurrentThread();
            for (int i = 0; i < 1_000; i++)
            {
                mismatches += (decimal)value != decimal.MaxValue ? 1 : 0;
            }

            long afterCast = GC.GetAllocatedBytesForCurrentThread();
            for (int i = 0; i < 1_000; i++)
            {
                mismatches += value.ToDecimal(null) != decimal.MaxValue ? 1 : 0;
            }

            long afterToDecimal = GC.GetAllocatedBytesForCurrentThread();
            for (int i = 0; i < 1_000; i++)
            {
                mismatches += (UInt256)source != truncated ? 1 : 0;
            }

            long afterFromDecimal = GC.GetAllocatedBytesForCurrentThread();
            allocated[0] = Math.Min(allocated[0], afterCast - start);
            allocated[1] = Math.Min(allocated[1], afterToDecimal - afterCast);
            allocated[2] = Math.Min(allocated[2], afterFromDecimal - afterToDecimal);
        }

        Assert.That(allocated, Is.EqualTo(new long[3]));
        Assert.That(mismatches, Is.Zero);
    }

    private static void AssertToDecimal(BigInteger value)
    {
        UInt256 number = (UInt256)value;
        if (value <= DecimalMax)
        {
            decimal expected = (decimal)value;
            Assert.That((decimal)number, Is.EqualTo(expected), value.ToString());
            Assert.That(number.ToDecimal(null), Is.EqualTo(expected), value.ToString());
        }
        else
        {
            Assert.Throws<OverflowException>(() => _ = (decimal)number, value.ToString());
            Assert.Throws<OverflowException>(() => number.ToDecimal(null), value.ToString());
        }
    }
}
