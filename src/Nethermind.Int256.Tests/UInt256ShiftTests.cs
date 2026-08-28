// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Collections.Generic;
using System.Numerics;
using System.Runtime.Intrinsics.X86;
using FluentAssertions;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

public partial class UInt256Tests
{
    private static readonly BigInteger ShiftMask = (BigInteger.One << 256) - 1;

    public static IEnumerable<TestCaseData> ShiftBoundaryCases
    {
        get
        {
            BigInteger[] values =
            [
                BigInteger.Zero,
                BigInteger.One,
                (BigInteger.One << 64) - 1,
                (BigInteger.One << 128) + 1,
                (BigInteger.One << 192) + (BigInteger.One << 65) + 1,
                ShiftMask,
            ];
            int[] shifts =
            [
                -256, -192, -128, -64,
                0, 1, 63, 64, 65,
                127, 128, 129, 191, 192, 193,
                255, 256, 257,
                int.MinValue, int.MaxValue,
            ];

            foreach (BigInteger value in values)
            {
                foreach (int shift in shifts)
                {
                    yield return new TestCaseData(value, shift);
                }
            }
        }
    }

    [TestCaseSource(nameof(ShiftBoundaryCases))]
    public void Shift_Boundaries_MatchBigInteger(BigInteger value, int shift)
    {
        AssertShiftMatches(value, shift);
    }

    [Test]
    public void Shift_AllNonnegativeCounts_MatchBigIntegerOracle()
    {
        BigInteger[] values =
        [
            BigInteger.Zero,
            BigInteger.One,
            (BigInteger.One << 64) - 1,
            (BigInteger.One << 128) + 1,
            (BigInteger.One << 192) + (BigInteger.One << 65) + 1,
            ShiftMask,
        ];

        foreach (BigInteger value in values)
        {
            for (int shift = 0; shift <= 256; shift++)
            {
                AssertShiftMatches(value, shift);
            }
        }
    }

    [Test]
    public void Shift_RandomValues_MatchBigIntegerOracle()
    {
        Random random = new(0x256);
        for (int i = 0; i < 256; i++)
        {
            byte[] bytes = new byte[32];
            random.NextBytes(bytes);
            BigInteger value = new(bytes, isUnsigned: true);
            int shift = random.Next(0, 258);
            AssertShiftMatches(value, shift);
        }
    }

    [Test]
    public void Shift_NegativeNonWordCounts_MatchBigIntegerWhenX64IntrinsicsAvailable()
    {
        if (!X86Base.X64.IsSupported)
        {
            Assert.Ignore("Negative non-word shifts use the legacy debug assertion when X86Base.X64 is unavailable.");
        }

        BigInteger[] values =
        [
            BigInteger.Zero,
            BigInteger.One,
            (BigInteger.One << 64) - 1,
            (BigInteger.One << 128) + 1,
            (BigInteger.One << 192) + (BigInteger.One << 65) + 1,
            ShiftMask,
        ];
        int[] shifts = [-257, -255, -193, -191, -129, -127, -65, -63, -1];

        foreach (BigInteger value in values)
        {
            foreach (int shift in shifts)
            {
                AssertShiftMatches(value, shift);
                AssertShiftAliasingMatches(value, shift);
            }
        }
    }

    [TestCaseSource(nameof(ShiftBoundaryCases))]
    public void Shift_Aliasing_MatchesBigInteger(BigInteger value, int shift)
    {
        AssertShiftAliasingMatches(value, shift);
    }

    private static void AssertShiftAliasingMatches(BigInteger value, int shift)
    {
        UInt256 input = (UInt256)value;
        BigInteger expectedLeft = ExpectedShift(value, shift, left: true);
        BigInteger expectedRight = ExpectedShift(value, shift, left: false);

        input.LeftShift(shift, out input);
        ((BigInteger)input).Should().Be(expectedLeft);

        input = (UInt256)value;
        input.RightShift(shift, out input);
        ((BigInteger)input).Should().Be(expectedRight);
    }

    private static BigInteger ExpectedShift(BigInteger value, int shift, bool left)
    {
        if (shift == 0)
        {
            return value;
        }

        if (shift < 0)
        {
            shift &= 63;
            if (shift == 0)
            {
                return BigInteger.Zero;
            }
        }
        else if (shift >= 256)
        {
            return BigInteger.Zero;
        }

        return (left ? value << shift : value >> shift) & ShiftMask;
    }

    private static void AssertShiftMatches(BigInteger value, int shift)
    {
        UInt256 input = (UInt256)value;
        input.LeftShift(shift, out UInt256 left);
        input.RightShift(shift, out UInt256 right);

        ((BigInteger)left).Should().Be(ExpectedShift(value, shift, left: true));
        ((BigInteger)right).Should().Be(ExpectedShift(value, shift, left: false));
    }
}
