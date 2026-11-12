// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Globalization;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

/// <summary>
/// Covers <see cref="UInt256.ToString(IFormatProvider)"/> and <see cref="Int256.ToString(IFormatProvider)"/>. The
/// unsigned text is checked against <see cref="BigInteger.ToString(IFormatProvider)"/>; the signed text keeps its
/// literal '-' under every culture.
/// </summary>
[Parallelizable(ParallelScope.All)]
public class FormatProviderTests
{
    private static readonly IFormatProvider?[] Providers =
    [
        null,
        CultureInfo.InvariantCulture,
        CultureInfo.GetCultureInfo("en-US"),
        CultureInfo.GetCultureInfo("fr-FR"),
        CultureInfo.GetCultureInfo("ar-SA"),
        new NumberFormatInfo { NegativeSign = "~", PositiveSign = "#", NumberGroupSeparator = "_" },
    ];

    private static readonly BigInteger TwoPow255 = BigInteger.One << 255;
    private static readonly BigInteger TwoPow256 = BigInteger.One << 256;

    private static readonly BigInteger[] Edges =
    [
        BigInteger.Zero,
        BigInteger.One,
        9,
        10,
        ulong.MaxValue,
        (BigInteger)ulong.MaxValue + 1,
        BigInteger.Pow(10, 19) - 1,
        BigInteger.Pow(10, 19),
        BigInteger.Pow(10, 38),
        BigInteger.Pow(10, 77),
        TwoPow255 - 1,
        TwoPow255,
        TwoPow256 - 1,
    ];

    [Test]
    public void UInt256_matches_BigInteger()
    {
        foreach (BigInteger value in Values())
        {
            UInt256 number = (UInt256)value;
            foreach (IFormatProvider? provider in Providers)
            {
                Assert.That(number.ToString(provider), Is.EqualTo(value.ToString(provider)));
            }
        }
    }

    [Test]
    public void Int256_writes_a_literal_minus_and_the_magnitude()
    {
        foreach (BigInteger bits in Values())
        {
            BigInteger value = bits >= TwoPow255 ? bits - TwoPow256 : bits;
            Int256 number = new((UInt256)bits);
            string expected = value.Sign < 0 ? "-" + BigInteger.Abs(value).ToString(CultureInfo.InvariantCulture) : value.ToString(CultureInfo.InvariantCulture);
            foreach (IFormatProvider? provider in Providers)
            {
                Assert.That(number.ToString(provider), Is.EqualTo(expected));
            }
        }
    }

    [Test]
    public void Allocates_only_the_result()
    {
        UInt256 unsigned = (UInt256)(TwoPow256 - 1);
        Int256 signed = new((UInt256)TwoPow255);
        IFormatProvider provider = CultureInfo.InvariantCulture;
        int length = 0;
        long[] allocated = [long.MaxValue, long.MaxValue, long.MaxValue, long.MaxValue];
        // A tier-up during a round can allocate on its own, so the quietest round is the one judged.
        for (int round = 0; round < 5; round++)
        {
            long start = GC.GetAllocatedBytesForCurrentThread();
            for (int i = 0; i < 1_000; i++)
            {
                length += unsigned.ToString().Length;
            }

            long afterUnsigned = GC.GetAllocatedBytesForCurrentThread();
            for (int i = 0; i < 1_000; i++)
            {
                length += unsigned.ToString(provider).Length;
            }

            long afterUnsignedProvider = GC.GetAllocatedBytesForCurrentThread();
            for (int i = 0; i < 1_000; i++)
            {
                length += signed.ToString().Length;
            }

            long afterSigned = GC.GetAllocatedBytesForCurrentThread();
            for (int i = 0; i < 1_000; i++)
            {
                length += signed.ToString(provider).Length;
            }

            long afterSignedProvider = GC.GetAllocatedBytesForCurrentThread();
            allocated[0] = Math.Min(allocated[0], afterUnsigned - start);
            allocated[1] = Math.Min(allocated[1], afterUnsignedProvider - afterUnsigned);
            allocated[2] = Math.Min(allocated[2], afterSigned - afterUnsignedProvider);
            allocated[3] = Math.Min(allocated[3], afterSignedProvider - afterSigned);
        }

        Assert.That(allocated[1], Is.EqualTo(allocated[0]));
        Assert.That(allocated[3], Is.EqualTo(allocated[2]));
        Assert.That(length, Is.EqualTo(5 * 1_000 * 2 * (78 + 78)));
    }

    private static IEnumerable<BigInteger> Values()
    {
        foreach (BigInteger edge in Edges)
        {
            yield return edge;
        }

        Random random = new(0xF0A7);
        byte[] bytes = new byte[32];
        for (int i = 0; i < 5_000; i++)
        {
            random.NextBytes(bytes);
            yield return new BigInteger(bytes, isUnsigned: true) >> random.Next(0, 256);
        }
    }
}
