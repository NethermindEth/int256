// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

/// <summary>
/// Covers the zero and one operand exits of <see cref="UInt256.MultiplyMod(in UInt256, in UInt256, in UInt256, out UInt256)"/>
/// for moduli of 2^128 and more, next to operands that only look like zero or one in their low limb. Every expected
/// value comes from <see cref="BigInteger"/>, also with the result written over each input.
/// </summary>
[Parallelizable(ParallelScope.All)]
public class MultiplyModUnitOperandTests
{
    [Test]
    public void Zero_and_one_operands_match_BigInteger()
    {
        Random random = new(0x7A11);
        for (int i = 0; i < 2_000; i++)
        {
            BigInteger m = RandomBits(random, random.Next(129, 257)) | (BigInteger.One << 128);
            BigInteger other = RandomBits(random, random.Next(0, 257));
            foreach (BigInteger unit in new[] { BigInteger.Zero, BigInteger.One })
            {
                AssertMulMod(unit, other, m);
                AssertMulMod(other, unit, m);
                // Same low limb as zero or one, but a high limb set: these must multiply.
                AssertMulMod(unit + (BigInteger.One << (64 * random.Next(1, 4))), other, m);
                AssertMulMod(other, unit + (BigInteger.One << (64 * random.Next(1, 4))), m);
            }

            AssertMulMod(2, other, m);
            AssertMulMod(other, 3, m);
            AssertMulMod(m, m - 1, m);
        }
    }

    private static void AssertMulMod(BigInteger a, BigInteger b, BigInteger m)
    {
        UInt256 x = FromBig(a);
        UInt256 y = FromBig(b);
        UInt256 mod = FromBig(m);
        BigInteger expected = a * b % m;

        UInt256.MultiplyMod(in x, in y, in mod, out UInt256 result);
        Assert.That(ToBig(result), Is.EqualTo(expected), $"{a:x} * {b:x} mod {m:x}");

        UInt256 aliasX = x;
        UInt256.MultiplyMod(in aliasX, in y, in mod, out aliasX);
        Assert.That(ToBig(aliasX), Is.EqualTo(expected), "into the first factor");

        UInt256 aliasY = y;
        UInt256.MultiplyMod(in x, in aliasY, in mod, out aliasY);
        Assert.That(ToBig(aliasY), Is.EqualTo(expected), "into the second factor");

        UInt256 aliasM = mod;
        UInt256.MultiplyMod(in x, in y, in aliasM, out aliasM);
        Assert.That(ToBig(aliasM), Is.EqualTo(expected), "into the modulus");
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
