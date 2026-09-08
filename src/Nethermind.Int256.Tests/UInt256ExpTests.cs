// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Tests;

[TestFixture]
public class UInt256ExpTests
{
    private static void Check(UInt256 b, UInt256 e)
    {
        UInt256 expected = (UInt256)BigInteger.ModPow((BigInteger)b, (BigInteger)e, BigInteger.One << 256);
        UInt256.Exp(b, e, out UInt256 actual);
        Assert.That(actual, Is.EqualTo(expected));
        UInt256 ba = b, ea = e;
        UInt256.Exp(ba, ea, out ba);
        Assert.That(ba, Is.EqualTo(expected), "Base alias");
        UInt256.Exp(b, ea, out ea);
        Assert.That(ea, Is.EqualTo(expected), "Exponent alias");
    }

    [Test]
    public void DecimalPowersIncludeOverflowAndTableBoundaries()
    {
        for (ulong e = 0; e <= 512; ++e) Check(new UInt256(10), new UInt256(e));
        Check(new UInt256(10), UInt256.MaxValue);
        Check(new UInt256(10), new UInt256(18, 1));
        Check(new UInt256(10, 1), new UInt256(18));
    }

    [Test]
    public void EvenBasesIncludeEveryTrailingZeroCount()
    {
        for (int bit = 0; bit < 256; ++bit)
        {
            UInt256 b = (UInt256)(BigInteger.One << bit);
            foreach (ulong e in new ulong[] { 0, 1, 2, 3, 127, 128, 254, 255, 256, 257 })
                Check(b, new UInt256(e));
            Check(b, UInt256.MaxValue);
        }
    }

    [Test]
    public void LimbAlignedPowersMatchBigInteger()
    {
        Random random = new(64);
        byte[] bytes = new byte[32];
        for (int i = 0; i < 512; ++i)
        {
            random.NextBytes(bytes);
            UInt256 x = new(bytes);
            UInt256 b = new(0, i % 8 == 0 ? 0 : x.u1, x.u2, x.u3);
            for (ulong e = 0; e <= 5; ++e) Check(b, new UInt256(e));
            Check(b, UInt256.MaxValue);
        }
    }

    [Test]
    public void WindowsCrossLimbAndDensityBoundaries()
    {
        UInt256 b = new(3, 5, 7, 11);
        for (int bits = 1; bits <= 256; ++bits)
        {
            BigInteger top = BigInteger.One << (bits - 1);
            Check(b, (UInt256)((top << 1) - 1));
            Check(b, (UInt256)(top | uint.MaxValue));
        }
        foreach (BigInteger b1 in new[] { (BigInteger.One << 255) + 1, (BigInteger.One << 255) - 1 })
        {
            Check((UInt256)b1, UInt256.MaxValue);
            Check((UInt256)b1, (UInt256)((BigInteger.One << 256) - 2));
        }
    }

    [Test]
    public void SquarePartialProductsAndCarries()
    {
        ulong[] values = { 0, 1, 2, 0x7fffffff, 0x80000000, 0xffffffff, 0x100000000,
            0x100000001, 0x7fffffffffffffff, 0x8000000000000000, ulong.MaxValue - 1, ulong.MaxValue };
        foreach (ulong x in values)
            foreach (ulong y in values)
            {
                Check(new UInt256(x, y, x, y), new UInt256(2));
                Check(new UInt256(x, y, x, y), new UInt256(3));
            }
    }

    [Test]
    public void BothInputsAndOutputCanAlias()
    {
        UInt256[] values = { UInt256.Zero, UInt256.One, new(2), new(3), new(10),
            UInt256.MaxValue, new(1, 0, 13, 17), new(3, 5, 7, 11) };
        foreach (UInt256 value in values)
        {
            UInt256 expected = (UInt256)BigInteger.ModPow((BigInteger)value, (BigInteger)value, BigInteger.One << 256);
            UInt256 actual = value;
            UInt256.Exp(actual, actual, out actual);
            Assert.That(actual, Is.EqualTo(expected));
        }
    }

    [Test]
    public void BinomialReductionMatchesBigInteger()
    {
        Random random = new(42);
        byte[] bytes = new byte[32];
        for (int i = 0; i < 1000; ++i)
        {
            random.NextBytes(bytes);
            UInt256 high = new(bytes);
            random.NextBytes(bytes);
            UInt256 e = new(bytes);
            Check(new UInt256(1, 0, high.u2, high.u3), e);
            Check(new UInt256(ulong.MaxValue, ulong.MaxValue, high.u2, high.u3), e);
        }
    }

    [Test]
    public void WideExponentsMatchBigInteger()
    {
        Random random = new(20260908);
        byte[] bytes = new byte[32];
        for (int i = 0; i < 1000; ++i)
        {
            random.NextBytes(bytes);
            UInt256 b = new(bytes);
            random.NextBytes(bytes);
            UInt256 e = new(bytes);
            Check(b, e);
        }
        for (int bit = 0; bit < 256; ++bit)
        {
            UInt256 e = (UInt256)(BigInteger.One << bit);
            Check(new UInt256(3, 5, 7, 11), e);
            Check(UInt256.MaxValue, e);
        }
    }
}
