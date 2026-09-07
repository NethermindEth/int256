// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Numerics;
using System.Reflection;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

public class MultiplyModLeadingDigitTests
{
    private delegate void Reduce(in UInt256 lo, in UInt256 hi, in UInt256 divisor, out UInt256 result);

    [TestCase(256)]
    [TestCase(192)]
    [TestCase(128)]
    public void Leading_quotient_digit_boundaries_match_BigInteger(int bits)
    {
        Reduce reduce = typeof(UInt256).GetMethod($"Remainder512By{bits}Bits",
            BindingFlags.NonPublic | BindingFlags.Static)!.CreateDelegate<Reduce>();
        BigInteger mask = (BigInteger.One << 256) - 1;
        foreach (int shift in new[] { 0, 1, 31, 63 })
        foreach (ulong top in new[] { 1UL << 63, (1UL << 63) + 1, ulong.MaxValue })
        foreach (int length in new[] { 5, 6, 7, 8 })
        foreach (int delta in new[] { -1, 0, 1 })
        foreach (BigInteger tail in new[] { BigInteger.Zero, mask })
        {
            ulong dTop = top >> shift;
            BigInteger d = ((BigInteger)dTop << (bits - 64)) | ((BigInteger.One << (bits - 64)) - 1);
            BigInteger head = (BigInteger)dTop + delta;
            if (head <= 0 || head > ulong.MaxValue) continue;
            BigInteger dividend = (head << (64 * (length - 1))) | tail;
            UInt256 lo = FromBig(dividend & mask), hi = FromBig(dividend >> 256), divisor = FromBig(d);
            BigInteger expected = dividend % d;
            reduce(in lo, in hi, in divisor, out UInt256 result);
            Assert.That(ToBig(result), Is.EqualTo(expected), $"bits={bits}, shift={shift}, length={length}, delta={delta}");
            UInt256 alias = divisor;
            reduce(in lo, in hi, in alias, out alias);
            Assert.That(ToBig(alias), Is.EqualTo(expected));
        }
    }

    private static BigInteger ToBig(UInt256 v) => v.u0 | ((BigInteger)v.u1 << 64) | ((BigInteger)v.u2 << 128) | ((BigInteger)v.u3 << 192);
    private static UInt256 FromBig(BigInteger v) => new((ulong)(v & ulong.MaxValue), (ulong)((v >> 64) & ulong.MaxValue),
        (ulong)((v >> 128) & ulong.MaxValue), (ulong)((v >> 192) & ulong.MaxValue));
}
