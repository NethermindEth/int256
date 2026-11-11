// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Globalization;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

/// <summary>
/// Covers the generic <see cref="Int256"/> parse with <see cref="NumberStyles.None"/>. Every expected result comes
/// from <see cref="BigInteger"/>: text of digits only is in range below <c>2^255</c>, larger values overflow, and
/// anything else is malformed.
/// </summary>
[Parallelizable(ParallelScope.All)]
public class Int256ParseDigitsTests
{
    private const string SignedMaxText = "57896044618658097711785492504343953926634992332820282019728792003956564819967";
    private const string SignedMinMagnitudeText = "57896044618658097711785492504343953926634992332820282019728792003956564819968";
    private const string UnsignedMaxText = "115792089237316195423570985008687907853269984665640564039457584007913129639935";

    private static IEnumerable<string> Texts()
    {
        yield return "0";
        yield return "000";
        yield return "7";
        yield return "9223372036854775807";
        yield return "9223372036854775808";
        yield return "18446744073709551615";
        yield return "18446744073709551616";
        yield return "1234567890123456789012345678901234567890";
        yield return SignedMaxText;
        yield return SignedMinMagnitudeText;
        yield return UnsignedMaxText;
        yield return "115792089237316195423570985008687907853269984665640564039457584007913129639936";
        yield return new string('0', 100) + SignedMaxText;
        yield return new string('0', 100) + SignedMinMagnitudeText;
        yield return new string('9', 79);
        yield return SignedMaxText + "\0";
        yield return SignedMinMagnitudeText + "\0";
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

    private static bool Expected(string text, out BigInteger value) =>
        BigInteger.TryParse(text, NumberStyles.None, CultureInfo.InvariantCulture, out value) && value.GetBitLength() <= 255;

    private static bool TryParse<T>(string text, out T result) where T : struct, INumberBase<T> =>
        T.TryParse(text.AsSpan(), NumberStyles.None, CultureInfo.InvariantCulture, out result);

    private static T Parse<T>(string text) where T : struct, INumberBase<T> =>
        T.Parse(text.AsSpan(), NumberStyles.None, CultureInfo.InvariantCulture);

    [TestCaseSource(nameof(Texts))]
    public void TryParse_with_no_style_flags_matches_BigInteger(string text)
    {
        bool expected = Expected(text, out BigInteger big);

        bool parsed = TryParse(text, out Int256 result);

        Assert.That(parsed, Is.EqualTo(expected));
        Assert.That((BigInteger)result, Is.EqualTo(expected ? big : BigInteger.Zero));
    }

    [TestCaseSource(nameof(Texts))]
    public void Parse_with_no_style_flags_matches_BigInteger(string text)
    {
        bool digits = BigInteger.TryParse(text, NumberStyles.None, CultureInfo.InvariantCulture, out BigInteger big);

        if (digits && big.GetBitLength() <= 255)
        {
            Assert.That((BigInteger)Parse<Int256>(text), Is.EqualTo(big));
        }
        else if (digits)
        {
            Assert.Throws<OverflowException>(() => Parse<Int256>(text));
        }
        else
        {
            Assert.Throws<FormatException>(() => Parse<Int256>(text));
        }
    }

    [Test]
    public void Parses_random_digit_strings_like_BigInteger()
    {
        Random random = new(0x51D6);
        char[] digits = new char[78];
        for (int i = 0; i < 10_000; i++)
        {
            int length = random.Next(1, digits.Length + 1);
            for (int j = 0; j < length; j++)
            {
                digits[j] = (char)('0' + random.Next(10));
            }

            string text = new(digits, 0, length);
            bool fits = Expected(text, out BigInteger big);

            Assert.That(TryParse(text, out Int256 result), Is.EqualTo(fits), text);
            Assert.That((BigInteger)result, Is.EqualTo(fits ? big : BigInteger.Zero), text);
            if (!fits)
            {
                Assert.Throws<OverflowException>(() => Parse<Int256>(text), text);
            }
        }
    }
}
