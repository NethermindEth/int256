// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Globalization;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

public class ParseDigitsTests
{
    private const string MaxText = "115792089237316195423570985008687907853269984665640564039457584007913129639935";

    private static IEnumerable<string> Texts()
    {
        yield return "0";
        yield return "000";
        yield return "7";
        yield return "18446744073709551615";
        yield return "18446744073709551616";
        yield return "1234567890123456789012345678901234567890";
        yield return MaxText;
        yield return "115792089237316195423570985008687907853269984665640564039457584007913129639936";
        yield return new string('0', 100) + MaxText;
        yield return new string('9', 79);
        yield return "123\0";
        yield return "123\0\0";
        yield return "\0";
        yield return "\0" + "1";
        yield return "1\0" + "2";
        yield return "";
        yield return " 1";
        yield return "1 ";
        yield return "+1";
        yield return "-1";
        yield return "-0";
        yield return "1,000";
        yield return "1.0";
        yield return "1e3";
        yield return "0x10";
        yield return "12a";
    }

    [TestCaseSource(nameof(Texts))]
    public void TryParse_with_no_style_flags_matches_BigInteger(string text)
    {
        bool expected = BigInteger.TryParse(text, NumberStyles.None, CultureInfo.InvariantCulture, out BigInteger big)
            && big.Sign >= 0 && big.GetBitLength() <= 256;

        bool parsed = UInt256.TryParse(text.AsSpan(), NumberStyles.None, CultureInfo.InvariantCulture, out UInt256 result);

        Assert.That(parsed, Is.EqualTo(expected));
        Assert.That((BigInteger)result, Is.EqualTo(expected ? big : BigInteger.Zero));
    }

    [TestCaseSource(nameof(Texts))]
    public void Parse_with_no_style_flags_matches_BigInteger(string text)
    {
        bool expected = BigInteger.TryParse(text, NumberStyles.None, CultureInfo.InvariantCulture, out BigInteger big)
            && big.Sign >= 0 && big.GetBitLength() <= 256;

        if (expected)
        {
            Assert.That((BigInteger)UInt256.Parse(text.AsSpan(), NumberStyles.None), Is.EqualTo(big));
        }
        else
        {
            Assert.Throws<FormatException>(() => UInt256.Parse(text.AsSpan(), NumberStyles.None));
        }
    }

    [Test]
    public void Parses_random_digit_strings_like_BigInteger()
    {
        Random random = new(0x5EED);
        char[] digits = new char[78];
        for (int i = 0; i < 10_000; i++)
        {
            int length = random.Next(1, digits.Length + 1);
            for (int j = 0; j < length; j++)
            {
                digits[j] = (char)('0' + random.Next(10));
            }

            string text = new(digits, 0, length);
            BigInteger big = BigInteger.Parse(text, NumberStyles.None, CultureInfo.InvariantCulture);
            bool fits = big.GetBitLength() <= 256;

            Assert.That(UInt256.TryParse(text.AsSpan(), NumberStyles.None, CultureInfo.InvariantCulture, out UInt256 result), Is.EqualTo(fits), text);
            if (fits)
            {
                Assert.That((BigInteger)result, Is.EqualTo(big), text);
            }
        }
    }
}
