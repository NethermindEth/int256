// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

[Parallelizable(ParallelScope.All)]
public class DivideDispatchTests
{
    private static readonly BigInteger TwoPow256 = BigInteger.One << 256;

    [Test]
    public void Zero_divisor_throws()
    {
        UInt256 x = new(5, 6, 7, 8);
        Assert.Throws<DivideByZeroException>(() => UInt256.Divide(in x, in UInt256.Zero, out _));
        Assert.Throws<DivideByZeroException>(() => UInt256.Divide(in UInt256.Zero, in UInt256.Zero, out _));
    }

    [Test]
    public void Divisor_one_returns_the_dividend()
    {
        Random random = new(0x0D11);
        for (int i = 0; i < 1_000; i++)
        {
            BigInteger dividend = RandomBits(random, random.Next(0, 257));
            AssertDivide(dividend, BigInteger.One);
        }
    }

    [Test]
    public void Equal_and_smaller_dividends_match_BigInteger()
    {
        Random random = new(0x0D12);
        for (int i = 0; i < 5_000; i++)
        {
            int bits = random.Next(1, 257);
            BigInteger divisor = RandomBits(random, bits) | (BigInteger.One << (bits - 1));
            if (divisor < 2) continue;
            AssertDivide(divisor, divisor);
            AssertDivide(divisor - 1, divisor);
            AssertDivide(RandomBits(random, bits - 1), divisor);
            AssertDivide(BigInteger.Zero, divisor);
        }
    }

    [Test]
    public void Power_of_two_divisors_match_BigInteger()
    {
        Random random = new(0x0D13);
        for (int exponent = 1; exponent < 256; exponent++)
        {
            BigInteger divisor = BigInteger.One << exponent;
            for (int sample = 0; sample < 16; sample++)
            {
                AssertDivide(RandomBits(random, random.Next(exponent, 257)), divisor);
            }

            AssertDivide(TwoPow256 - 1, divisor);
            AssertDivide(divisor, divisor);
            AssertDivide(divisor + 1, divisor);
            AssertDivide(TwoPow256 - 1, divisor + 1);
            AssertDivide(RandomBits(random, 256), divisor + 1);
        }
    }

    [Test]
    public void Divisors_with_the_top_bit_set_match_BigInteger()
    {
        Random random = new(0x0D14);
        for (int i = 0; i < 5_000; i++)
        {
            BigInteger divisor = RandomBits(random, 256) | (BigInteger.One << 255);
            AssertDivide(TwoPow256 - 1, divisor);
            AssertDivide(divisor + RandomBits(random, 255) % (TwoPow256 - divisor), divisor);
        }
    }

    [Test]
    public void Single_limb_divisors_match_BigInteger()
    {
        Random random = new(0x0D15);
        ulong[] fixedDivisors = [3, 7, 10, 1_000_000, 1_000_000_000_000_000_000, 10_000_000_000_000_000_000, ulong.MaxValue, ulong.MaxValue - 1, (1UL << 63) + 1];
        foreach (ulong d in fixedDivisors)
        {
            for (int bits = 1; bits <= 256; bits++)
            {
                AssertDivide(RandomBits(random, bits) | (BigInteger.One << (bits - 1)), d);
            }

            for (int limb = 0; limb < 4; limb++)
            {
                BigInteger aligned = (BigInteger)d << (64 * limb);
                AssertDivide(aligned - 1, d);
                AssertDivide(aligned, d);
                AssertDivide(aligned + 1, d);
                AssertDivide(aligned + d, d);
                AssertDivide(((BigInteger)(d - 1) << (64 * limb)) | RandomBits(random, 64 * limb), d);
            }
        }

        for (int i = 0; i < 50_000; i++)
        {
            int divisorBits = random.Next(2, 65);
            BigInteger divisor = RandomBits(random, divisorBits) | (BigInteger.One << (divisorBits - 1));
            if (divisor < 2) continue;
            BigInteger dividend = RandomBits(random, random.Next(1, 257));
            if (random.Next(4) == 0) dividend &= ~(((BigInteger.One << 64) - 1) << (64 * random.Next(0, 4)));
            AssertDivide(dividend, divisor);
        }
    }

    [TestCase(128)]
    [TestCase(192)]
    [TestCase(256)]
    public void Multi_limb_divisors_match_BigInteger(int maxBits)
    {
        Random random = new(0x0D16 + maxBits);
        for (int i = 0; i < 20_000; i++)
        {
            int divisorBits = random.Next(maxBits - 63, maxBits + 1);
            BigInteger divisor = RandomBits(random, divisorBits) | (BigInteger.One << (divisorBits - 1));
            AssertDivide(RandomBits(random, random.Next(divisorBits, 257)), divisor);
        }
    }

    private static void AssertDivide(BigInteger dividend, BigInteger divisor)
    {
        if (dividend.Sign < 0 || dividend >= TwoPow256) return;

        UInt256 x = FromBig(dividend);
        UInt256 y = FromBig(divisor);
        BigInteger expected = dividend / divisor;

        UInt256.Divide(in x, in y, out UInt256 quotient);
        if (ToBig(quotient) != expected)
        {
            Assert.Fail($"{dividend:x} / {divisor:x}\n  expected {expected:x}\n  actual   {ToBig(quotient):x}");
        }

        UInt256 aliasX = x;
        UInt256.Divide(in aliasX, in y, out aliasX);
        Assert.That(ToBig(aliasX), Is.EqualTo(expected), $"{dividend:x} / {divisor:x} into the dividend");

        UInt256 aliasY = y;
        UInt256.Divide(in x, in aliasY, out aliasY);
        Assert.That(ToBig(aliasY), Is.EqualTo(expected), $"{dividend:x} / {divisor:x} into the divisor");

        Assert.That(ToBig(x / y), Is.EqualTo(expected), $"{dividend:x} / {divisor:x} through the operator");
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
