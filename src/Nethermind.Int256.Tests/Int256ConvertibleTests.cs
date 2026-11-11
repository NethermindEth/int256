// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Globalization;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

/// <summary>
/// Covers the <see cref="IConvertible"/> members of <see cref="Int256"/>, and of <see cref="UInt256"/> where they
/// boxed. Each result, or the type of each exception, is checked against the conversion these members used to make.
/// </summary>
[Parallelizable(ParallelScope.All)]
public class Int256ConvertibleTests
{
    private static readonly BigInteger TwoPow255 = BigInteger.One << 255;
    private static readonly BigInteger TwoPow256 = BigInteger.One << 256;

    private static readonly BigInteger[] Magnitudes =
    [
        BigInteger.Zero,
        BigInteger.One,
        127,
        128,
        255,
        256,
        char.MaxValue,
        int.MaxValue,
        (BigInteger)int.MaxValue + 1,
        uint.MaxValue,
        long.MaxValue,
        (BigInteger)long.MaxValue + 1,
        ulong.MaxValue,
        (BigInteger)ulong.MaxValue + 1,
        (BigInteger.One << 53) + 1,
        (BigInteger.One << 64) + (1 << 11),
        (BigInteger.One << 64) + (1 << 11) + 1,
        (BigInteger.One << 64) + (3 << 11),
        (BigInteger.One << 89) + (BigInteger.One << 65),
        (BigInteger.One << 89) + (BigInteger.One << 65) + 1,
        (BigInteger.One << 96) - 1,
        BigInteger.One << 96,
        BigInteger.One << 127,
        (BigInteger.One << 128) - (BigInteger.One << 103),
        (BigInteger.One << 128) - (BigInteger.One << 103) - 1,
        BigInteger.One << 200,
        TwoPow255 - 1,
        TwoPow255,
    ];

    [Test]
    public void Edge_values_match_BigInteger()
    {
        foreach (BigInteger magnitude in Magnitudes)
        {
            if (magnitude < TwoPow255)
            {
                AssertConversions(magnitude);
            }

            AssertConversions(-magnitude);
        }
    }

    [Test]
    public void Random_values_match_BigInteger()
    {
        Random random = new(0x1C0E);
        byte[] bytes = new byte[32];
        for (int i = 0; i < 20_000; i++)
        {
            random.NextBytes(bytes);
            BigInteger bits = new BigInteger(bytes, isUnsigned: true) >> random.Next(0, 256);
            if (random.Next(2) == 0)
            {
                bits = TwoPow256 - bits;
            }

            AssertConversions(bits >= TwoPow255 ? bits - TwoPow256 : bits);
        }
    }

    [Test]
    public void Conversions_do_not_allocate()
    {
        Int256 value = -(long)int.MaxValue;
        IFormatProvider provider = CultureInfo.InvariantCulture;
        long mismatches = 0;
        long[] allocated = [long.MaxValue, long.MaxValue, long.MaxValue, long.MaxValue];
        // A tier-up during a round can allocate on its own, so the quietest round is the one judged.
        for (int round = 0; round < 5; round++)
        {
            long start = GC.GetAllocatedBytesForCurrentThread();
            for (int i = 0; i < 1_000; i++)
            {
                mismatches += value.ToDecimal(provider) != -int.MaxValue ? 1 : 0;
            }

            long afterDecimal = GC.GetAllocatedBytesForCurrentThread();
            for (int i = 0; i < 1_000; i++)
            {
                mismatches += value.ToDouble(provider) != -int.MaxValue ? 1 : 0;
            }

            long afterDouble = GC.GetAllocatedBytesForCurrentThread();
            for (int i = 0; i < 1_000; i++)
            {
                mismatches += value.ToInt64(provider) != -int.MaxValue ? 1 : 0;
            }

            long afterInt64 = GC.GetAllocatedBytesForCurrentThread();
            for (int i = 0; i < 1_000; i++)
            {
                mismatches += value.ToSingle(provider) != -int.MaxValue ? 1 : 0;
            }

            long afterSingle = GC.GetAllocatedBytesForCurrentThread();
            allocated[0] = Math.Min(allocated[0], afterDecimal - start);
            allocated[1] = Math.Min(allocated[1], afterDouble - afterDecimal);
            allocated[2] = Math.Min(allocated[2], afterInt64 - afterDouble);
            allocated[3] = Math.Min(allocated[3], afterSingle - afterInt64);
        }

        Assert.That(allocated, Is.EqualTo(new long[4]));
        Assert.That(mismatches, Is.Zero);
    }

    [Test]
    public void UInt256_single_char_and_date_keep_their_results()
    {
        IFormatProvider provider = CultureInfo.InvariantCulture;
        Random random = new(0x1C0F);
        byte[] bytes = new byte[32];
        for (int i = 0; i < 5_000; i++)
        {
            random.NextBytes(bytes);
            UInt256 value = new UInt256(bytes, isBigEndian: false) >> random.Next(0, 256);
            Assert.That(value.ToSingle(provider), Is.EqualTo((float)value.ToDouble(provider)));
        }

        UInt256 small = 65;
        Assert.That(() => small.ToChar(provider), Throws.TypeOf<InvalidCastException>());
        Assert.That(() => small.ToDateTime(provider), Throws.TypeOf<InvalidCastException>());
        UInt256 wide = UInt256.MaxValue;
        Assert.That(() => wide.ToChar(provider), Throws.TypeOf<OverflowException>());
        Assert.That(() => wide.ToDateTime(provider), Throws.TypeOf<OverflowException>());

        long allocated = long.MaxValue;
        float sum = 0;
        // A tier-up during a round can allocate on its own, so the quietest round is the one judged.
        for (int round = 0; round < 5; round++)
        {
            long start = GC.GetAllocatedBytesForCurrentThread();
            for (int i = 0; i < 1_000; i++)
            {
                sum += small.ToSingle(provider);
            }

            allocated = Math.Min(allocated, GC.GetAllocatedBytesForCurrentThread() - start);
        }

        Assert.That(allocated, Is.Zero);
        Assert.That(sum, Is.EqualTo(5 * 1_000 * 65f));
    }

    private static void AssertConversions(BigInteger value)
    {
        Int256 number = (Int256)value;
        IFormatProvider provider = CultureInfo.InvariantCulture;
        string label = value.ToString(CultureInfo.InvariantCulture);

        Assert.That(number.ToDouble(provider), Is.EqualTo((double)value), label);
        Assert.That(number.ToSingle(provider), Is.EqualTo((float)value), label);

        IEnumerable<(string Name, Func<object> Actual, Func<decimal, object> Expected)> narrowing =
        [
            ("decimal", () => number.ToDecimal(provider), d => d),
            ("byte", () => number.ToByte(provider), d => Convert.ToByte(d, provider)),
            ("sbyte", () => number.ToSByte(provider), d => Convert.ToSByte(d, provider)),
            ("short", () => number.ToInt16(provider), d => Convert.ToInt16(d, provider)),
            ("ushort", () => number.ToUInt16(provider), d => Convert.ToUInt16(d, provider)),
            ("int", () => number.ToInt32(provider), d => Convert.ToInt32(d, provider)),
            ("uint", () => number.ToUInt32(provider), d => Convert.ToUInt32(d, provider)),
            ("long", () => number.ToInt64(provider), d => Convert.ToInt64(d, provider)),
            ("ulong", () => number.ToUInt64(provider), d => Convert.ToUInt64(d, provider)),
            ("char", () => number.ToChar(provider), d => Convert.ToChar(d, provider)),
        ];

        foreach ((string name, Func<object> actual, Func<decimal, object> expected) in narrowing)
        {
            Type? expectedException = null;
            object? expectedValue = null;
            try
            {
                expectedValue = expected((decimal)value);
            }
            catch (Exception e)
            {
                expectedException = e.GetType();
            }

            if (expectedException is null)
            {
                Assert.That(actual(), Is.EqualTo(expectedValue), $"{label} as {name}");
            }
            else
            {
                Assert.That(() => actual(), Throws.TypeOf(expectedException), $"{label} as {name}");
            }
        }
    }
}
