// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

public class MultiplyModPseudoMersenneTests
{
    private static readonly BigInteger Two64 = BigInteger.One << 64;
    private static readonly BigInteger Two256 = BigInteger.One << 256;
    private static readonly BigInteger Max512 = (BigInteger.One << 512) - 1;

    private static readonly ulong[] Constants =
    [
        2, 3, 189, 977, 0x1000003D1, 0xFFFFFFFF, 0x100000000, 1UL << 63, (1UL << 63) + 1, ulong.MaxValue - 2,
        ulong.MaxValue - 1, 0x9A3B5C7D1E2F4061,
    ];

    private static IEnumerable<TestCaseData> Cases() =>
        Constants.Select(c => new TestCaseData(c).SetArgDisplayNames($"c{c:X}"));

    [TestCaseSource(nameof(Cases))]
    public void Fold_matches_BigInteger_at_boundaries(ulong c)
    {
        BigInteger m = Two256 - c;
        foreach (BigInteger x in Dividends(m, c, new Random(0x5EED + (int)(c & 0xFFFF))))
        {
            Assert.That(Fold(x, c), Is.EqualTo(x % m), $"x={x:X}");
        }
    }

    [TestCaseSource(nameof(Cases))]
    public void Fold_matches_BigInteger_for_random_dividends(ulong c)
    {
        BigInteger m = Two256 - c;
        Random random = new(0xF01D);
        for (int i = 0; i < 20_000; i++)
        {
            BigInteger x = (i % 4) switch
            {
                0 => RandomBits(random, 1 + random.Next(512)),
                1 => (RandomBits(random, 256) % m) * (RandomBits(random, 256) % m),
                2 => Max512 - RandomBits(random, random.Next(1, 300)),
                _ => RandomBits(random, 1 + random.Next(256)) * m + RandomBits(random, 70) - (Two64 << 2),
            };
            if (x < 0 || x > Max512) continue;
            Assert.That(Fold(x, c), Is.EqualTo(x % m), $"x={x:X}");
        }
    }

    [TestCaseSource(nameof(Cases))]
    public void Fold_covers_the_carry_and_final_subtraction_paths(ulong c)
    {
        BigInteger m = Two256 - c;
        BigInteger cc = c;
        BigInteger[] dividends =
        [
            (Two256 - 1) * Two256 + (Two256 - 1),
            (Two256 - 1) * Two256 + (Two256 - cc),
            (Two256 - 1) * Two256 + (Two256 - cc - 1),
            Two256 * (Two256 - 1) + m,
            Two256 + m - cc,
            Two256 + m - cc - 1,
            Two256 + m - 1,
            m,
            m - 1,
            m + 1,
            Two256 - 1,
            Two256 - cc,
            Two256 - cc + 1,
            (BigInteger)1 << 511,
            m * m,
            m * m - 1,
            (m - 1) * (m - 1),
        ];
        foreach (BigInteger x in dividends)
        {
            if (x < 0 || x > Max512) continue;
            Assert.That(Fold(x, c), Is.EqualTo(x % m), $"x={x:X}");
        }
    }

    [Test]
    public void MultiplyMod_by_secp256k1_p_matches_BigInteger_for_chained_products()
    {
        BigInteger m = Two256 - 0x1000003D1;
        UInt256 modulus = FromBig(m);
        Random random = new(0x5EC9);
        BigInteger x = RandomBits(random, 256) % m;
        for (int i = 0; i < 100_000; i++)
        {
            BigInteger y = i % 5 == 0 ? RandomBits(random, 256) : (i % 3 == 0 ? x : RandomBits(random, 256) % m);
            UInt256.MultiplyMod(FromBig(x), FromBig(y), modulus, out UInt256 res);
            BigInteger expected = x * y % m;
            Assert.That(ToBig(res), Is.EqualTo(expected), $"x={x:X} y={y:X}");
            x = expected.IsZero ? RandomBits(random, 256) % m : expected;
        }
    }

    private static IEnumerable<BigInteger> Dividends(BigInteger m, ulong c, Random random)
    {
        yield return BigInteger.Zero;
        yield return Max512;
        yield return Max512 - 1;
        yield return Max512 - Max512 % m;
        yield return Max512 - Max512 % m - 1;
        yield return Two256;
        yield return Two256 - 1;
        yield return Two256 + c - 1;
        yield return Two256 + c;
        for (int i = 0; i < 512; i++)
        {
            BigInteger q = RandomBits(random, 1 + random.Next(256));
            foreach (BigInteger r in new[] { BigInteger.Zero, BigInteger.One, m - 1, m - 2, (BigInteger)c, RandomBits(random, 256) % m })
            {
                BigInteger x = q * m + r;
                if (x <= Max512) yield return x;
            }
        }
    }

    private static BigInteger Fold(BigInteger x, ulong c)
    {
        UInt256 lo = FromBig(x & (Two256 - 1)), hi = FromBig(x >> 256);
        UInt256.Remainder512ByPseudoMersenne(in lo, in hi, c, out UInt256 rem);
        return ToBig(rem);
    }

    private static BigInteger RandomBits(Random random, int bits)
    {
        if (bits <= 0) return BigInteger.Zero;
        byte[] bytes = new byte[(bits + 7) / 8 + 1];
        random.NextBytes(bytes);
        bytes[^1] = 0;
        return new BigInteger(bytes) & ((BigInteger.One << bits) - 1);
    }

    private static BigInteger ToBig(UInt256 v) => v.u0 | ((BigInteger)v.u1 << 64) | ((BigInteger)v.u2 << 128) | ((BigInteger)v.u3 << 192);

    private static UInt256 FromBig(BigInteger v) => new((ulong)(v & ulong.MaxValue), (ulong)((v >> 64) & ulong.MaxValue),
        (ulong)((v >> 128) & ulong.MaxValue), (ulong)((v >> 192) & ulong.MaxValue));
}
