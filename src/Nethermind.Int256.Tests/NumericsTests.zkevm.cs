// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Globalization;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

public partial class NumericsTests
{
    // The zkEVM build writes D, G, X and B only, which keeps BigInteger's formatting out of guest images.
    [TestCase("N")]
    [TestCase("E")]
    [TestCase("F2")]
    [TestCase("G5")]
    [TestCase("#,##0")]
    public void Culture_formats_are_unsupported(string format)
    {
        Assert.Throws<FormatException>(() => U(12345).ToString(format, CultureInfo.InvariantCulture));
        Assert.Throws<FormatException>(() => S(-12345).TryFormat(new char[64], out _, format, CultureInfo.InvariantCulture));
        Assert.Throws<FormatException>(() => ((IUtf8SpanFormattable)S(-12345)).TryFormat(new byte[64], out _, format, CultureInfo.InvariantCulture));
    }
}
