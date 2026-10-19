// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Globalization;
using System.Numerics;
using System.Text;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

public partial class NumericsTests
{
    private static readonly string[] CultureFormats = ["N", "N0", "E", "e3", "F2", "C", "P0", "G5", "#,##0"];

    // The standard build formats these through BigInteger, so they match it.
    [TestCaseSource(nameof(SignedValues))]
    public void Culture_formats_match_BigInteger(BigInteger big)
    {
        Span<char> chars = stackalloc char[512];
        Span<byte> bytes = stackalloc byte[512];
        foreach (string format in CultureFormats)
        {
            string expected = big.ToString(format, CultureInfo.InvariantCulture);
            Assert.That(S(big).ToString(format, CultureInfo.InvariantCulture), Is.EqualTo(expected), format);
            if (big >= 0)
            {
                Assert.That(U(big).ToString(format, CultureInfo.InvariantCulture), Is.EqualTo(expected), format);
            }

            Assert.That(S(big).TryFormat(chars, out int written, format, CultureInfo.InvariantCulture), Is.True, format);
            Assert.That(chars[..written].ToString(), Is.EqualTo(expected), format);

            Assert.That(((IUtf8SpanFormattable)S(big)).TryFormat(bytes, out written, format, CultureInfo.InvariantCulture), Is.True, format);
            Assert.That(Encoding.UTF8.GetString(bytes[..written]), Is.EqualTo(expected), format);
        }
    }
}
