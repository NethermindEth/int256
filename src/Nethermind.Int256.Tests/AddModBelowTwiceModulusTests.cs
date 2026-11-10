// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

public class AddModBelowTwiceModulusTests
{
    private static readonly BigInteger Max = (BigInteger.One << 256) - 1;

    [Test]
    public void Operands_on_both_sides_of_the_top_limb_gate_match_BigInteger()
    {
        Random random = new(0xADD2);
        for (int i = 0; i < 50_000; i++)
        {
            BigInteger m = Modulus(random, i);
            BigInteger mTop = m >> 192;
            foreach (BigInteger x in Candidates(random, m, mTop))
            {
                BigInteger y = Candidates(random, m, mTop)[random.Next(9)];
                AssertAddMod(x, y, m);
            }
        }
    }

    private static BigInteger Modulus(Random random, int i) => (i % 5) switch
    {
        0 => (BigInteger.One << 192) + RandomBelow(random, BigInteger.One << 192),
        1 => Max,
        2 => Max - RandomBelow(random, BigInteger.One << 64),
        3 => (BigInteger.One << 255) + 1,
        _ => (BigInteger.One << (193 + random.Next(63))) - 1 - RandomBelow(random, BigInteger.One << 192),
    };

    private static BigInteger[] Candidates(Random random, BigInteger m, BigInteger mTop)
    {
        BigInteger topLimbEdge = BigInteger.Min(Max, ((mTop + 1) << 192) - 1);
        return
        [
            BigInteger.Zero,
            m - 1,
            BigInteger.Min(Max, m),
            BigInteger.Min(Max, 2 * m - 1),
            topLimbEdge,
            BigInteger.Min(Max, topLimbEdge + 1),
            // Largest value with the next top limb: at least 2m for a small modulus, so it must not pass the gate.
            BigInteger.Min(Max, ((mTop + 2) << 192) - 1),
            RandomBelow(random, m),
            RandomBelow(random, BigInteger.Min(Max + 1, 2 * m)),
        ];
    }

    private static void AssertAddMod(BigInteger x, BigInteger y, BigInteger m)
    {
        UInt256 ux = FromBig(x), uy = FromBig(y), um = FromBig(m);
        UInt256.AddMod(in ux, in uy, in um, out UInt256 result);
        Assert.That(ToBig(result), Is.EqualTo((x + y) % m), $"x={x}, y={y}, m={m}");
        UInt256 alias = um;
        UInt256.AddMod(in ux, in uy, in alias, out alias);
        Assert.That(ToBig(alias), Is.EqualTo((x + y) % m), $"aliased modulus, x={x}, y={y}, m={m}");
    }

    private static BigInteger RandomBelow(Random random, BigInteger bound)
    {
        byte[] bytes = new byte[33];
        random.NextBytes(bytes);
        bytes[32] = 0;
        return new BigInteger(bytes) % bound;
    }

    private static BigInteger ToBig(UInt256 v) => v.u0 | ((BigInteger)v.u1 << 64) | ((BigInteger)v.u2 << 128) | ((BigInteger)v.u3 << 192);

    private static UInt256 FromBig(BigInteger v) => new((ulong)(v & ulong.MaxValue), (ulong)((v >> 64) & ulong.MaxValue),
        (ulong)((v >> 128) & ulong.MaxValue), (ulong)((v >> 192) & ulong.MaxValue));
}
