// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

[Parallelizable(ParallelScope.All)]
public class SignedDivideRemainderTests
{
    private static readonly BigInteger TwoPow255 = BigInteger.One << 255;
    private static readonly BigInteger TwoPow256 = BigInteger.One << 256;

    private static BigInteger Wrap(BigInteger value)
    {
        BigInteger wrapped = ((value % TwoPow256) + TwoPow256) % TwoPow256;
        return wrapped >= TwoPow255 ? wrapped - TwoPow256 : wrapped;
    }

    private static IEnumerable<BigInteger> BoundaryValues()
    {
        for (int bit = 0; bit < 255; bit += 7)
        {
            BigInteger power = BigInteger.One << bit;
            yield return power;
            yield return power + 1;
            yield return power - 1;
        }

        yield return TwoPow255 - 1;
        yield return TwoPow255;
    }

    private static void AssertBoth(BigInteger a, BigInteger b)
    {
        Int256 x = new(Wrap(a));
        Int256 y = new(Wrap(b));
        BigInteger signedA = Wrap(a);
        BigInteger signedB = Wrap(b);

        Int256.Divide(in x, in y, out Int256 quotient);
        Int256.Mod(in x, in y, out Int256 remainder);

        string label = $"{signedA} / {signedB}";
        Assert.That((BigInteger)quotient, Is.EqualTo(Wrap(BigInteger.Divide(signedA, signedB))), label);
        Assert.That((BigInteger)remainder, Is.EqualTo(Wrap(BigInteger.Remainder(signedA, signedB))), label);

        Int256 aliasedDividend = x;
        Int256.Divide(in aliasedDividend, in y, out aliasedDividend);
        Assert.That(aliasedDividend, Is.EqualTo(quotient), label);
        Int256 aliasedDivisor = y;
        Int256.Mod(in x, in aliasedDivisor, out aliasedDivisor);
        Assert.That(aliasedDivisor, Is.EqualTo(remainder), label);
    }

    [Test]
    public void Matches_BigInteger_on_limb_boundaries_for_every_sign_pair()
    {
        foreach (BigInteger a in BoundaryValues())
        {
            foreach (BigInteger b in BoundaryValues())
            {
                if (b.IsZero) continue;
                AssertBoth(a, b);
                AssertBoth(-a, b);
                AssertBoth(a, -b);
                AssertBoth(-a, -b);
            }
        }
    }

    [Test]
    public void Matches_BigInteger_on_random_widths_for_every_sign_pair()
    {
        Random random = new(0x5D1F);
        byte[] bytes = new byte[32];
        for (int i = 0; i < 4_000; i++)
        {
            BigInteger a = RandomMagnitude(random, bytes, i & 3);
            BigInteger b = RandomMagnitude(random, bytes, (i >> 2) & 3);
            if (b.IsZero) continue;
            AssertBoth(a, b);
            AssertBoth(-a, b);
            AssertBoth(a, -b);
            AssertBoth(-a, -b);
        }
    }

    [Test]
    public void Min_value_by_minus_one_wraps_to_min_value()
    {
        Int256 min = new(-TwoPow255);
        Int256.Divide(in min, in Int256.MinusOne, out Int256 quotient);
        Int256.Mod(in min, in Int256.MinusOne, out Int256 remainder);

        Assert.That((BigInteger)quotient, Is.EqualTo(-TwoPow255));
        Assert.That(remainder, Is.EqualTo(Int256.Zero));
    }

    private static BigInteger RandomMagnitude(Random random, byte[] bytes, int zeroLimbs)
    {
        random.NextBytes(bytes);
        bytes[31] &= 0x7F;
        bytes.AsSpan(32 - zeroLimbs * 8).Clear();
        return new BigInteger(bytes, isUnsigned: true);
    }
}
