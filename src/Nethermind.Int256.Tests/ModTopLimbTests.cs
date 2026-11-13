// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

public class ModTopLimbTests
{
    private static readonly BigInteger Two192 = BigInteger.One << 192;
    private static readonly BigInteger Two256 = BigInteger.One << 256;
    private const ulong Top = 0x30644E72E131A029UL;

    private static readonly BigInteger[] Divisors =
    [
        Hex("30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001"),
        Hex("30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47"),
        Top * Two192,
        Top * Two192 + 1,
        (Top + (BigInteger)1) * Two192 - 1,
        (Top + (BigInteger)1) * Two192 - 2,
        Top * Two192 + (Two192 >> 1),
    ];

    private static IEnumerable<TestCaseData> Cases() =>
        Divisors.Select((d, i) => new TestCaseData(d).SetArgDisplayNames($"y{i}"));

    [TestCaseSource(nameof(Cases))]
    public void Mod_matches_BigInteger_near_multiples(BigInteger y)
    {
        Random random = new(0x70B);
        BigInteger maxQuotient = (Two256 - 1) / y;
        for (BigInteger q = 0; q <= maxQuotient; q++)
        {
            BigInteger[] remainders = [0, 1, 2, y - 1, y - 2, y / 2, RandomBits(random, 256) % y];
            foreach (BigInteger r in remainders)
            {
                if (q * y + r < Two256) AssertMod(q * y + r, y);
            }
        }

        foreach (BigInteger x in new[] { Two256 - 1, Two256 - 2, y + 1, 2 * y - 1, (Two256 - 1) - (Two256 - 1) % y })
        {
            AssertMod(x, y);
        }
    }

    [TestCaseSource(nameof(Cases))]
    public void Mod_matches_BigInteger_for_random_dividends(BigInteger y)
    {
        Random random = new(0x70C);
        for (int i = 0; i < 50_000; i++)
        {
            BigInteger x = i % 2 == 0 ? RandomBits(random, 256) : RandomBits(random, 1 + random.Next(256));
            AssertMod(x, y);
        }
    }

    [Test]
    public void Mod_matches_BigInteger_for_random_divisors_with_the_top_limb()
    {
        Random random = new(0x70D);
        for (int i = 0; i < 50_000; i++)
        {
            BigInteger y = Top * Two192 + RandomBits(random, 192);
            BigInteger k = random.Next(0, 6);
            BigInteger x3 = k * (Top + (BigInteger)1) + random.Next(-2, 3);
            if (x3 < 0 || x3 > ulong.MaxValue) continue;
            BigInteger x = (x3 << 192) + RandomBits(random, 192);
            AssertMod(x, y);
        }
    }

    [Test]
    public void Mod_matches_BigInteger_when_the_product_carries_between_limbs()
    {
        BigInteger top = Top;
        int checkedCount = 0;
        for (ulong d = 2; d <= 6; d++)
        {
            ulong near = ulong.MaxValue / d;
            ulong[] limbs = [near - 1, near, near + 1, ulong.MaxValue, ulong.MaxValue - 1, 0];
            foreach (ulong y2 in limbs)
                foreach (ulong y1 in limbs)
                    foreach (ulong y0 in limbs)
                    {
                        BigInteger y = (top << 192) | ((BigInteger)y2 << 128) | ((BigInteger)y1 << 64) | y0;
                        for (int k = 1; k <= 5; k++)
                        {
                            BigInteger aligned = k * (top + 1) << 192;
                            foreach (BigInteger x in new[] { aligned, aligned - 1, aligned + 1, aligned + (Two192 - 1), k * y, k * y - 1, k * y + y - 1 })
                            {
                                if (x > y && x < Two256)
                                {
                                    AssertMod(x, y);
                                    checkedCount++;
                                }
                            }
                        }
                    }
        }

        AssertMod(3 * (top + 1) << 192, Hex("30644e72e131a02955555555555555555555555555555555ffffffffffffffff"));
        Assert.That(checkedCount, Is.GreaterThan(5_000));
    }

    private static void AssertMod(BigInteger x, BigInteger y)
    {
        UInt256 a = FromBig(x), b = FromBig(y);
        UInt256.Mod(in a, in b, out UInt256 res);
        Assert.That(ToBig(res), Is.EqualTo(x % y), $"x={x:X} y={y:X}");
        UInt256.Mod(in a, in b, out a);
        Assert.That(ToBig(a), Is.EqualTo(x % y), $"aliased x={x:X} y={y:X}");
    }

    private static BigInteger RandomBits(Random random, int bits)
    {
        if (bits <= 0) return BigInteger.Zero;
        byte[] bytes = new byte[(bits + 7) / 8 + 1];
        random.NextBytes(bytes);
        bytes[^1] = 0;
        return new BigInteger(bytes) & ((BigInteger.One << bits) - 1);
    }

    private static BigInteger Hex(string value) => BigInteger.Parse("0" + value, NumberStyles.HexNumber);

    private static BigInteger ToBig(UInt256 v) => v.u0 | ((BigInteger)v.u1 << 64) | ((BigInteger)v.u2 << 128) | ((BigInteger)v.u3 << 192);

    private static UInt256 FromBig(BigInteger v) => new((ulong)(v & ulong.MaxValue), (ulong)((v >> 64) & ulong.MaxValue),
        (ulong)((v >> 128) & ulong.MaxValue), (ulong)((v >> 192) & ulong.MaxValue));
}
