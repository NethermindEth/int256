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
    public void WindowFactorsCrossProductWidthBoundaries()
    {
        foreach (int bit in new[] { 2, 4, 8, 16, 32, 63, 64, 65, 127, 128, 129, 191, 192, 255 })
            foreach (int delta in new[] { -1, 1 })
                foreach (int exponentBits in new[] { 33, 63, 64, 65, 127, 128, 129, 255, 256 })
                    Check((UInt256)((BigInteger.One << bit) + delta),
                        (UInt256)((BigInteger.One << exponentBits) - 1));
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
    public void AdaptiveBinomialCutoffsPreserveSignsAndAliases()
    {
        BigInteger modulus = BigInteger.One << 256;
        for (int valuation = 15; valuation <= 63; ++valuation)
        {
            BigInteger b = 1 + (BigInteger.One << valuation) + (11 * (BigInteger.One << 64))
                + (13 * (BigInteger.One << 128)) + (17 * (BigInteger.One << 192));
            // Mirrors Exp's bitLen > 32 gate and structured cutoff 128 - 2 * precision;
            // ExpBinomialMinBits (80 in both variants) can select the path earlier.
            int cutoff = Math.Max(33, 128 - 2 * valuation);
            for (int bits = cutoff - 1; bits <= cutoff + 1; ++bits)
                foreach (BigInteger e in new[] { (BigInteger.One << bits) - 1, (BigInteger.One << (bits - 1)) + 1 })
                {
                    Check((UInt256)b, (UInt256)e);
                    Check((UInt256)(modulus - b), (UInt256)e);
                }
        }
    }

    [Test]
    public void LongPowersCoverIndependentLimbCarries()
    {
        Random random = new(20260909);
        byte[] bytes = new byte[32];
        for (int i = 0; i < 2048; ++i)
        {
            random.NextBytes(bytes);
            UInt256 b = new(bytes);
            b = new UInt256(b.u0 | 1, b.u1, b.u2, b.u3);
            Check(b, new UInt256(ulong.MaxValue)); // Window helper.
            Check(b, new UInt256(1, 0, 1)); // Long binomial helper.
        }
    }

    [Test]
    public void GeneralBinomialCutoffMatchesWidthsAndDensities()
    {
        UInt256[] bases = { new(3), new(5), new(7), new(ulong.MaxValue - 2),
            new(ulong.MaxValue - 2, 1), new(3, 11, 13, 17) };
        foreach (int bits in new[] { 123, 124, 125, 127, 128, 129 })
        {
            BigInteger top = BigInteger.One << (bits - 1);
            foreach (BigInteger e in new[] { 2 * top - 1, top + 1,
                top + (BigInteger.One << 31) - 1, top + (BigInteger.One << 32) - 1 })
                foreach (UInt256 b in bases) Check(b, (UInt256)e);
        }
    }

    [Test]
    public void LongPowersCross32BitPrecisionAndCarryBoundaries()
    {
        BigInteger modulus = BigInteger.One << 256;
        UInt256[] exponents = { UInt256.MaxValue, new(0, 0, 0, 1UL << 63),
            new(1, 0, 0, 1UL << 63), new(ulong.MaxValue, uint.MaxValue), new(2, 0, 1) };
        ulong[] limbs = { 0, 1, uint.MaxValue, 1UL << 32, 1UL << 63, ulong.MaxValue };
        foreach (uint q in new uint[] { 0, 1, 0x7fffffff, 0x80000000, uint.MaxValue })
            foreach (ulong limb in limbs)
                foreach (UInt256 e in exponents)
                {
                    UInt256 b = new(1 | ((ulong)q << 32), limb, ~limb, limb);
                    Check(b, e);
                    Check((UInt256)(modulus - (BigInteger)b), e);
                }
        for (int valuation = 2; valuation < 64; ++valuation)
            foreach (UInt256 e in exponents)
            {
                BigInteger b = 1 + (BigInteger.One << valuation) + (11 * (BigInteger.One << 64))
                    + (13 * (BigInteger.One << 128)) + (17 * (BigInteger.One << 192));
                Check((UInt256)b, e);
                Check((UInt256)(modulus - b), e);
            }
    }

    [Test]
    public void EightTermBinomialCarriesSurviveExactDivision()
    {
        BigInteger modulus = BigInteger.One << 256;
        foreach (int valuation in new[] { 2, 16, 30, 31, 32, 33, 42, 43, 47, 48, 51, 52, 55, 56 })
            foreach (int sign in new[] { -1, 1 })
                foreach (int boundary in new[] { 64, 128, 192 })
                    for (int offset = -1; offset <= 7; ++offset)
                    {
                        BigInteger b = 1 + (BigInteger.One << valuation)
                            + (BigInteger.One << 255) + (BigInteger.One << 128);
                        if (sign < 0) b = modulus - b;
                        // Mirrors ExpOddLong's 32-bit prefix target (ExpOddLong32).
                        int prefix = Math.Max(1, 32 - valuation);
                        BigInteger high = (BigInteger.One << boundary) + offset;
                        BigInteger e = (high << prefix) | ((BigInteger.One << prefix) - 1);
                        // Keep a long exponent even when the coefficient boundary is low.
                        e |= BigInteger.One << 255;
                        Check((UInt256)b, (UInt256)e);
                    }
    }

    [Test]
    public void GeneralBinomialCutoffCrossesExponentAndBaseWidths()
    {
        UInt256[] bases = { new(3), new(ulong.MaxValue - 2), new(3, 1), new(3, 11, 13, 17), new(6, 11, 13, 17) };
        for (int bits = 60; bits <= 129; ++bits)
        {
            BigInteger top = BigInteger.One << (bits - 1);
            BigInteger mask = (top << 1) - 1;
            foreach (BigInteger exponent in new[] { top, top + 1, mask, mask - 1,
                top | (BigInteger.Parse("12297829382473034410") & mask) })
                foreach (UInt256 b in bases) Check(b, (UInt256)exponent);
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
    public void FourTermBinomialReductionMatchesBigInteger()
    {
        Random random = new(65);
        byte[] bytes = new byte[32];
        for (int i = 0; i < 512; ++i)
        {
            random.NextBytes(bytes);
            UInt256 x = new(bytes);
            random.NextBytes(bytes);
            UInt256 e = new(bytes);
            Check(new UInt256(1, x.u1, x.u2, x.u3), e);
            Check(new UInt256(ulong.MaxValue, x.u1, x.u2, x.u3), e);
        }
        for (int bit = 1; bit < 256; ++bit)
            for (int delta = -1; delta <= 1; ++delta)
            {
                UInt256 e = (UInt256)((BigInteger.One << bit) + delta);
                Check(new UInt256(1, 11, 13, 17), e);
                Check(new UInt256(ulong.MaxValue, 11, 13, 17), e);
            }
        for (ulong e = 0; e < 32; ++e)
            Check(new UInt256(1, 11, 13, 17), new UInt256(e));
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

    [Test]
    public void LongOddPowersMatchAtEveryBinomialCutoff()
    {
        BigInteger modulus = BigInteger.One << 256;
        for (int valuation = 2; valuation <= 63; ++valuation)
        {
            UInt256 b = new(1 + (1UL << valuation), ulong.MaxValue, 13, 17);
            UInt256 negative = (UInt256)(modulus - (BigInteger)b);
            // Mirrors ExpOddLongPhased/ExpOddLongNear32's 64-bit prefix target;
            // ExpFourTermPrecision selects when each variant uses this prefix.
            int cutoff = 64 - valuation;
            foreach (int top in new[] { 127, 128, 129, 191, 192, 254, 255 })
                foreach (int delta in new[] { -1, 0, 1 })
                {
                    UInt256 e = (UInt256)((BigInteger.One << top) + (BigInteger.One << cutoff) + delta);
                    Check(b, e);
                    Check(negative, e);
                }
            Check(b, UInt256.MaxValue);
            Check(negative, UInt256.MaxValue);
        }
    }
}
