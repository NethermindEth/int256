// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

public class AddModSmallModulusTests
{
    private static readonly BigInteger Two64 = BigInteger.One << 64;

    private static readonly ulong[] Moduli =
    [
        2,
        3,
        7,
        (1UL << 32) - 5,
        1UL << 32,
        (1UL << 63) - 25,
        1UL << 63,
        (1UL << 63) + 1,
        0x9E37_79B9_7F4A_7C15,
        ulong.MaxValue - 58,
        ulong.MaxValue - 1,
        ulong.MaxValue,
    ];

    private static IEnumerable<TestCaseData> Cases() =>
        Moduli.Select((m, i) => new TestCaseData(m).SetArgDisplayNames($"m{i}"));

    [TestCaseSource(nameof(Cases))]
    public void AddMod_matches_BigInteger_for_operands_near_the_modulus(ulong m)
    {
        BigInteger mb = m;
        BigInteger[] operands = [0, 1, 2, mb / 2, mb / 2 + 1, mb - 2, mb - 1, mb, mb + 1, 2 * mb - 1, 2 * mb, Two64 - 1, Two64, Two64 + 1];
        foreach (BigInteger x in operands)
        {
            foreach (BigInteger y in operands)
            {
                AssertAddMod(x, y, mb);
            }
        }
    }

    [TestCaseSource(nameof(Cases))]
    public void AddMod_matches_BigInteger_for_random_reduced_operands(ulong m)
    {
        Random random = new(0xADD5);
        BigInteger mb = m;
        for (int i = 0; i < 20_000; i++)
        {
            BigInteger x = RandomBelow(random, mb);
            BigInteger y = i % 4 == 0 ? RandomBelow(random, 2 * mb - x) : RandomBelow(random, mb);
            AssertAddMod(x, y, mb);
        }
    }

    [Test]
    public void AddMod_matches_BigInteger_for_random_small_moduli()
    {
        Random random = new(0xADD6);
        for (int i = 0; i < 50_000; i++)
        {
            int bits = 1 + random.Next(64);
            BigInteger m = RandomBits(random, bits) | (BigInteger.One << (bits - 1));
            if (m < 2) m = 2;
            BigInteger x = i % 3 == 0 ? RandomBits(random, 1 + random.Next(130)) : RandomBelow(random, m);
            BigInteger y = i % 5 == 0 ? RandomBits(random, 1 + random.Next(130)) : RandomBelow(random, m);
            AssertAddMod(x, y, m);
        }
    }

    private static void AssertAddMod(BigInteger x, BigInteger y, BigInteger m)
    {
        UInt256.AddMod(FromBig(x), FromBig(y), FromBig(m), out UInt256 result);
        Assert.That(ToBig(result), Is.EqualTo((x + y) % m), $"x={x} y={y} m={m}");
    }

    private static BigInteger RandomBelow(Random random, BigInteger bound)
    {
        if (bound <= 1) return BigInteger.Zero;
        return RandomBits(random, 72) % bound;
    }

    private static BigInteger RandomBits(Random random, int bits)
    {
        byte[] bytes = new byte[bits / 8 + 2];
        random.NextBytes(bytes);
        bytes[^1] = 0;
        return new BigInteger(bytes) & ((BigInteger.One << bits) - 1);
    }

    private static BigInteger ToBig(UInt256 v) => v.u0 | ((BigInteger)v.u1 << 64) | ((BigInteger)v.u2 << 128) | ((BigInteger)v.u3 << 192);

    private static UInt256 FromBig(BigInteger v) => new((ulong)(v & ulong.MaxValue), (ulong)((v >> 64) & ulong.MaxValue),
        (ulong)((v >> 128) & ulong.MaxValue), (ulong)((v >> 192) & ulong.MaxValue));
}
