// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

/// <summary>
/// Covers the column carries of the full-width 512-bit product behind <see cref="UInt256.MultiplyMod"/>. Every
/// expected value comes from <see cref="BigInteger"/>.
/// </summary>
/// <remarks>
/// Both operands are wider than 128 bits, so the product takes the four-by-four limb path. Limbs near
/// <c>2^64 - 1</c> push the high half of each limb product to its <c>2^64 - 2</c> bound and make every column
/// carry, which is where a carry folded into the high half would wrap if the bound did not hold.
/// </remarks>
[Parallelizable(ParallelScope.All)]
public class MultiplyModWideCarryTests
{
    private static readonly BigInteger TwoPow256 = BigInteger.One << 256;

    private static readonly ulong[] EdgeLimbs = [0, 1, 2, 1UL << 63, ulong.MaxValue - 1, ulong.MaxValue];

    private static readonly string[] Moduli =
    [
        "21888242871839275222246405745257275088548364400416034343698204186575808495617",
        "115792089237316195423570985008687907853269984665640564039457584007908834671663",
        "115792089237316195423570985008687907853269984665640564039457584007913129639935",
        "115792089237316195423570985008687907853269984665640564039457584007913129639934",
        "6277101735386680763835789423207666416102355444464034512895",
        "340282366920938463463374607431768211297",
    ];

    [Test]
    public void Edge_limb_operands_match_BigInteger()
    {
        Random random = new(0xCA44);
        foreach (string modulus in Moduli)
        {
            BigInteger m = BigInteger.Parse(modulus);
            for (int i = 0; i < 20_000; i++)
            {
                AssertMultiplyMod(EdgeOperand(random), EdgeOperand(random), m);
            }
        }
    }

    [Test]
    public void Max_operands_match_BigInteger()
    {
        BigInteger max = TwoPow256 - 1;
        foreach (string modulus in Moduli)
        {
            BigInteger m = BigInteger.Parse(modulus);
            AssertMultiplyMod(max, max, m);
            AssertMultiplyMod(max, max - 1, m);
            AssertMultiplyMod(max - ulong.MaxValue, max, m);
        }
    }

    [Test]
    public void Random_wide_operands_match_BigInteger()
    {
        Random random = new(0xCA45);
        for (int i = 0; i < 50_000; i++)
        {
            BigInteger x = RandomWide(random);
            BigInteger y = RandomWide(random);
            BigInteger m = (i % 3) switch
            {
                0 => RandomWide(random),
                1 => RandomWide(random) >> 64 | BigInteger.One << 128,
                _ => RandomWide(random) >> 128 | BigInteger.One << 64,
            };
            AssertMultiplyMod(x, y, m);
        }
    }

    private static BigInteger EdgeOperand(Random random)
    {
        BigInteger value;
        do
        {
            value = BigInteger.Zero;
            for (int limb = 0; limb < 4; limb++)
            {
                ulong word = random.Next(4) == 0 ? (ulong)random.NextInt64() : EdgeLimbs[random.Next(EdgeLimbs.Length)];
                value |= (BigInteger)word << (64 * limb);
            }
        } while (value >> 128 == 0);

        return value;
    }

    private static BigInteger RandomWide(Random random)
    {
        byte[] bytes = new byte[33];
        random.NextBytes(bytes);
        bytes[^1] = 0;
        return new BigInteger(bytes) | BigInteger.One << 200;
    }

    private static void AssertMultiplyMod(BigInteger x, BigInteger y, BigInteger m)
    {
        BigInteger expected = x * y % m;
        UInt256 ux = FromBig(x);
        UInt256 uy = FromBig(y);
        UInt256 um = FromBig(m);
        UInt256.MultiplyMod(in ux, in uy, in um, out UInt256 result);
        if (ToBig(result) != expected)
        {
            Assert.Fail($"{x:x} * {y:x} mod {m:x}\n  expected {expected:x}\n  actual   {ToBig(result):x}");
        }
    }

    private static BigInteger ToBig(in UInt256 v)
        => v.u0 | ((BigInteger)v.u1 << 64) | ((BigInteger)v.u2 << 128) | ((BigInteger)v.u3 << 192);

    private static UInt256 FromBig(BigInteger v) => new(
        (ulong)(v & ulong.MaxValue), (ulong)((v >> 64) & ulong.MaxValue),
        (ulong)((v >> 128) & ulong.MaxValue), (ulong)((v >> 192) & ulong.MaxValue));
}
