// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

/// <summary>
/// Covers <see cref="UInt256.ToString(string)"/>, which formats as <see cref="BigInteger.ToString(string)"/> does,
/// including the leading 0 that <see cref="BigInteger"/> writes before a hex digit above 7 or a binary 1.
/// </summary>
[Parallelizable(ParallelScope.All)]
public class FormatStringTests
{
    private static readonly string?[] Formats =
    [
        null, "", "D", "d", "D0", "D1", "D5", "D01", "D78", "D79", "D100", "G", "g",
        "X", "x", "X0", "X1", "X2", "X3", "X01", "X63", "X64", "X65", "X66", "x100", "X600",
        "B", "b", "B0", "B1", "B3", "B255", "B256", "B257", "B300", "b600",
        "G5", "N0", "R", "E", "F2", "0.#",
    ];

    private static IEnumerable<BigInteger> EdgeValues()
    {
        yield return BigInteger.Zero;
        for (int bit = 0; bit < 256; bit++)
        {
            BigInteger power = BigInteger.One << bit;
            yield return power - 1;
            yield return power;
            yield return power + 1;
            yield return (BigInteger.One << 256) - power;
        }
    }

    private static void AssertFormats(BigInteger value)
    {
        UInt256 number = (UInt256)value;
        foreach (string? format in Formats)
        {
            Assert.That(number.ToString(format!), Is.EqualTo(value.ToString(format)), $"{value} as {format ?? "null"}");
        }
    }

    [Test]
    public void Edge_values_match_BigInteger()
    {
        foreach (BigInteger value in EdgeValues())
        {
            AssertFormats(value);
        }
    }

    [Test]
    public void Random_values_match_BigInteger()
    {
        Random random = new(0xF0A7);
        byte[] bytes = new byte[32];
        for (int i = 0; i < 4_096; i++)
        {
            random.NextBytes(bytes);
            bytes.AsSpan(random.Next(1, 33)).Clear();
            AssertFormats(new BigInteger(bytes, isUnsigned: true));
        }
    }
}
