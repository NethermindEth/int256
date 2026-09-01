// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Collections.Generic;
using System.Numerics;
using FluentAssertions;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

public partial class UInt256Tests
{
    private static readonly BigInteger ShiftMask = (BigInteger.One << 256) - 1;

    private static BigInteger[] ShiftValues =>
    [
        BigInteger.Zero,
        BigInteger.One,
        (BigInteger.One << 64) - 1,
        (BigInteger.One << 128) + 1,
        (BigInteger.One << 192) + (BigInteger.One << 65) + 1,
        BigInteger.One << 255,
        (BigInteger.One << 255) - 1,
        ShiftMask,
    ];

    public static IEnumerable<TestCaseData> ShiftBoundaryCases
    {
        get
        {
            int[] shifts =
            [
                int.MinValue, -257, -256, -255, -193, -192, -191, -129, -128, -127,
                -65, -64, -63, -1,
                0, 1, 63, 64, 65, 127, 128, 129, 191, 192, 193, 255, 256, 257,
                int.MaxValue,
            ];

            foreach (BigInteger value in ShiftValues)
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
        => AssertShiftMatches(value, shift);

    [TestCaseSource(nameof(ShiftBoundaryCases))]
    public void Shift_Aliasing_MatchesBigInteger(BigInteger value, int shift)
        => AssertShiftAliasingMatches(value, shift);

    [Test]
    public void Shift_EveryCountUpTo256_MatchesBigIntegerOracle()
    {
        foreach (BigInteger value in ShiftValues)
        {
            for (int shift = 0; shift <= 256; shift++)
            {
                AssertShiftMatches(value, shift);
                AssertShiftAliasingMatches(value, shift);
            }
        }
    }

    // Negative counts are not a designed contract - the pre-1.6.1 implementation reached them through
    // a path whose own Debug.Assert(n < 64) they violate - but callers may depend on the release-build
    // result, so the behaviour is pinned here.
    [Test]
    public void Shift_NegativeCounts_MatchLegacyBehaviour()
    {
        for (int shift = -260; shift < 0; shift++)
        {
            foreach (BigInteger value in ShiftValues)
            {
                AssertShiftMatches(value, shift);
                AssertShiftAliasingMatches(value, shift);
            }
        }
    }

    [Test]
    public void Shift_RandomValues_MatchBigIntegerOracle()
    {
        Random random = new(0x256);
        for (int i = 0; i < 4096; i++)
        {
            byte[] bytes = new byte[32];
            random.NextBytes(bytes);
            BigInteger value = new(bytes, isUnsigned: true);
            int shift = random.Next(-300, 300);
            AssertShiftMatches(value, shift);
            AssertShiftAliasingMatches(value, shift);
        }
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

        ((BigInteger)left).Should().Be(ExpectedShift(value, shift, left: true), $"Lsh(0x{value:X}, {shift})");
        ((BigInteger)right).Should().Be(ExpectedShift(value, shift, left: false), $"Rsh(0x{value:X}, {shift})");
    }

    private static void AssertShiftAliasingMatches(BigInteger value, int shift)
    {
        UInt256 input = (UInt256)value;
        input.LeftShift(shift, out input);
        ((BigInteger)input).Should().Be(ExpectedShift(value, shift, left: true), $"aliased Lsh(0x{value:X}, {shift})");

        input = (UInt256)value;
        input.RightShift(shift, out input);
        ((BigInteger)input).Should().Be(ExpectedShift(value, shift, left: false), $"aliased Rsh(0x{value:X}, {shift})");
    }
}
