// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

public class MultiplyModReducedOperandTests
{
    private static readonly BigInteger Mask = (BigInteger.One << 256) - 1;

    private static readonly string[] NamedModuli =
    [
        // Scalar and base fields used by on-chain proof verifiers: top limbs need a normalising shift.
        "21888242871839275222246405745257275088548364400416034343698204186575808495617",
        "21888242871839275222246405745257275088696311157297823662689037894645226208583",
        // Fields whose top limb is already normalised.
        "115792089237316195423570985008687907853269984665640564039457584007908834671663",
        "115792089237316195423570985008687907852837564279074904382605163141518161494337",
        "57896044618658097711785492504343953926634992332820282019728792003956564819949",
        "52435875175126190479447740508185965837690552500527637822603658699938581184513",
    ];

    [Test]
    public void Reduced_operands_against_named_moduli_match_BigInteger()
    {
        Random random = new(0x2B1D);
        foreach (string text in NamedModuli)
        {
            BigInteger m = BigInteger.Parse(text);
            foreach (BigInteger x in Operands(random, m, 256))
            foreach (BigInteger y in Operands(random, m, 16))
            {
                AssertMultiplyMod(x, y, m);
            }
        }
    }

    [Test]
    public void Reduced_operands_against_every_modulus_width_and_shift_match_BigInteger()
    {
        Random random = new(0x51F7);
        for (int bits = 65; bits <= 256; bits++)
        {
            for (int i = 0; i < 64; i++)
            {
                BigInteger m = RandomBelow(random, BigInteger.One << bits) | (BigInteger.One << (bits - 1));
                BigInteger x = RandomBelow(random, m);
                BigInteger y = RandomBelow(random, m);
                AssertMultiplyMod(x, y, m);
                AssertMultiplyMod(m - 1, m - 1, m);
                AssertMultiplyMod(m - 1, y, m);
            }
        }
    }

    [Test]
    public void Unreduced_and_boundary_operands_match_BigInteger()
    {
        Random random = new(0x7E11);
        BigInteger[] edges = [BigInteger.Zero, BigInteger.One, Mask, Mask - 1, BigInteger.One << 255, (BigInteger.One << 255) - 1];
        for (int i = 0; i < 20_000; i++)
        {
            int bits = 64 + random.Next(193);
            BigInteger m = RandomBelow(random, BigInteger.One << bits) | (BigInteger.One << (bits - 1));
            BigInteger x = i % 4 == 0 ? edges[random.Next(edges.Length)] : RandomBelow(random, BigInteger.One << random.Next(1, 257));
            BigInteger y = i % 5 == 0 ? edges[random.Next(edges.Length)] : RandomBelow(random, BigInteger.One << random.Next(1, 257));
            // Products just below and just above m * 2^256 sit on either side of the zero leading digit.
            if (i % 7 == 0) x = BigInteger.Min(Mask, m + random.Next(3) - 1);
            AssertMultiplyMod(x, y, m);
        }
    }

    [TestCase(192)]
    [TestCase(256)]
    public void Dividends_around_divisor_times_limb_powers_match_BigInteger(int bits)
    {
        Reduce reduce = typeof(UInt256).GetMethod($"Remainder512By{bits}Bits",
            System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Static)!.CreateDelegate<Reduce>();
        Random random = new(0x3C0D);
        for (int shift = 0; shift < 64; shift++)
        {
            BigInteger d = RandomBelow(random, BigInteger.One << (bits - shift)) | (BigInteger.One << (bits - shift - 1));
            for (int limbs = 1; limbs * 64 + bits - shift <= 512; limbs++)
            {
                BigInteger power = d << (64 * limbs);
                foreach (BigInteger dividend in new[] { power - 1, power, power + 1, power - d, power + d - 1 })
                {
                    if (dividend >> 256 == 0 || dividend > (BigInteger.One << 512) - 1) continue;
                    UInt256 lo = FromBig(dividend & Mask), hi = FromBig(dividend >> 256), divisor = FromBig(d);
                    reduce(in lo, in hi, in divisor, out UInt256 result);
                    Assert.That(ToBig(result), Is.EqualTo(dividend % d), $"bits={bits}, shift={shift}, limbs={limbs}");
                }
            }
        }
    }

    private delegate void Reduce(in UInt256 lo, in UInt256 hi, in UInt256 divisor, out UInt256 result);

    private static IEnumerable<BigInteger> Operands(Random random, BigInteger m, int count)
    {
        yield return BigInteger.Zero;
        yield return BigInteger.One;
        yield return m - 1;
        yield return m - 2;
        yield return m >> 1;
        for (int i = 0; i < count; i++) yield return RandomBelow(random, m);
    }

    private static void AssertMultiplyMod(BigInteger x, BigInteger y, BigInteger m)
    {
        UInt256 ux = FromBig(x), uy = FromBig(y), um = FromBig(m);
        UInt256.MultiplyMod(in ux, in uy, in um, out UInt256 result);
        Assert.That(ToBig(result), Is.EqualTo(x * y % m), $"x={x}, y={y}, m={m}");
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
