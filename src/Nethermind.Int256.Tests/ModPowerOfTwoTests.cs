// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

[Parallelizable(ParallelScope.All)]
public class ModPowerOfTwoTests
{
    [Test]
    public void Power_of_two_divisors_match_BigInteger()
    {
        Random random = new(0x3D21);
        for (int exponent = 1; exponent < 256; exponent++)
        {
            BigInteger divisor = BigInteger.One << exponent;
            for (int sample = 0; sample < 16; sample++)
            {
                AssertMod(RandomBits(random, random.Next(exponent + 1, 257)), divisor);
            }

            AssertMod((BigInteger.One << 256) - 1, divisor);
            AssertMod(divisor + 1, divisor);
            AssertMod(divisor * 2 - 1, divisor);
        }
    }

    [Test]
    public void Single_limb_operands_match_BigInteger()
    {
        Random random = new(0x3D22);
        for (int i = 0; i < 50_000; i++)
        {
            BigInteger divisor = RandomBits(random, random.Next(2, 65));
            if (divisor < 2) continue;
            AssertMod(RandomBits(random, random.Next(1, 65)), divisor);
        }

        AssertMod(ulong.MaxValue, ulong.MaxValue - 1);
        AssertMod(ulong.MaxValue, 3);
    }

    private static void AssertMod(BigInteger dividend, BigInteger divisor)
    {
        UInt256 x = FromBig(dividend);
        UInt256 y = FromBig(divisor);
        BigInteger expected = dividend % divisor;

        UInt256.Mod(in x, in y, out UInt256 remainder);
        Assert.That(ToBig(remainder), Is.EqualTo(expected), $"{dividend:x} % {divisor:x}");

        UInt256 aliasX = x;
        UInt256.Mod(in aliasX, in y, out aliasX);
        Assert.That(ToBig(aliasX), Is.EqualTo(expected), $"{dividend:x} % {divisor:x} into the dividend");

        UInt256 aliasY = y;
        UInt256.Mod(in x, in aliasY, out aliasY);
        Assert.That(ToBig(aliasY), Is.EqualTo(expected), $"{dividend:x} % {divisor:x} into the divisor");
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
