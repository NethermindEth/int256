// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Collections.Generic;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

public class Convertibles
{
    private static IEnumerable<(object, string)> Numbers = new (object, string)[]
    {
        (0, "0"),
        (1, "1"),
        (2, "2"),
        (3, "3"),
        (byte.MaxValue, "byte.MaxValue"),
        (sbyte.MaxValue, "sbyte.MaxValue"),
        (short.MaxValue, "short.MaxValue"),
        (ushort.MaxValue, "ushort.MaxValue"),
        (int.MaxValue, "int.MaxValue"),
        (uint.MaxValue, "uint.MaxValue"),
        (long.MaxValue, "long.MaxValue"),
        (ulong.MaxValue, "ulong.MaxValue"),
        (TestNumbers.TwoTo64, "TwoTo64"),
        (TestNumbers.TwoTo128, "TwoTo128"),
        (TestNumbers.TwoTo192, "TwoTo192"),
        (TestNumbers.UInt128Max, "UInt128Max"),
        (TestNumbers.UInt192Max, "UInt192Max"),
        (TestNumbers.UInt256Max, "UInt256Max"),
    };

    private static IEnumerable<(object, string)> SignedNumbers = new (object, string)[]
    {
        (0, "0"),
        (1, "1"),
        (2, "2"),
        (3, "3"),
        (byte.MaxValue, "byte.MaxValue"),
        (sbyte.MaxValue, "sbyte.MaxValue"),
        (sbyte.MinValue, "sbyte.MinValue"),
        (short.MaxValue, "short.MaxValue"),
        (short.MinValue, "short.MinValue"),
        (ushort.MaxValue, "ushort.MaxValue"),
        (int.MaxValue, "int.MaxValue"),
        (int.MinValue, "int.MinValue"),
        (uint.MaxValue, "uint.MaxValue"),
        (long.MaxValue, "long.MaxValue"),
        (long.MinValue, "long.MinValue"),
        (ulong.MaxValue, "ulong.MaxValue"),
        (TestNumbers.TwoTo64, "TwoTo64"),
        (TestNumbers.TwoTo128, "TwoTo128"),
        (TestNumbers.TwoTo192, "TwoTo192"),
        (TestNumbers.UInt128Max, "UInt128Max"),
        (TestNumbers.UInt192Max, "UInt192Max"),
        (-TestNumbers.TwoTo64, "-TwoTo64"),
        (-TestNumbers.TwoTo128, "-TwoTo128"),
        (-TestNumbers.TwoTo192, "-TwoTo192"),
        (-TestNumbers.UInt128Max, "-UInt128Max"),
        (-TestNumbers.UInt192Max, "-UInt192Max"),
        (TestNumbers.Int256Max, "Int256Max"),
        (TestNumbers.Int256Min, "Int256Min"),
    };

    public static (Type type, BigInteger? min, BigInteger? max)[] ConvertibleTypes =
    {
        (typeof(byte), byte.MinValue, byte.MaxValue),
        (typeof(sbyte), sbyte.MinValue, sbyte.MaxValue),
        (typeof(short), short.MinValue, short.MaxValue),
        (typeof(ushort), ushort.MinValue, ushort.MaxValue),
        (typeof(int), int.MinValue, int.MaxValue),
        (typeof(uint), uint.MinValue, uint.MaxValue),
        (typeof(long), long.MinValue, long.MaxValue),
        (typeof(ulong), ulong.MinValue, ulong.MaxValue),
        (typeof(float), (BigInteger?)float.MinValue, (BigInteger?)float.MaxValue),
        (typeof(double), (BigInteger?)double.MinValue, (BigInteger?)double.MaxValue),
        (typeof(decimal), (BigInteger?)decimal.MinValue, (BigInteger?)decimal.MaxValue),
        (typeof(BigInteger), null, null)
    };

    public static IEnumerable<TestCaseData> TestCases => GenerateTestCases(Numbers, BigInteger.Zero);
    public static IEnumerable<TestCaseData> SignedTestCases => GenerateTestCases(SignedNumbers);

    private static IEnumerable<TestCaseData> GenerateTestCases(IEnumerable<(object, string)> numbers, BigInteger? minValue = null)
    {
        Type ExpectedException(BigInteger value, BigInteger? min, BigInteger? max) =>
            (!min.HasValue || !max.HasValue || (value >= min && value <= max)) && (!minValue.HasValue || value >= minValue)
                ? null
                : typeof(OverflowException);

        string ExpectedString(Type type, BigInteger value, BigInteger? min, ref Type expectedException)
        {
            string expectedString = null;
            if (expectedException is not null && type == typeof(float))
            {
                expectedString = value < min ? "-∞" : "∞";
                expectedException = null;
            }

            return expectedString;
        }

        foreach ((object number, string name) in numbers)
        {
            foreach ((Type type, BigInteger? min, BigInteger? max) in ConvertibleTypes)
            {
                BigInteger value = BigInteger.Parse(number.ToString()!);
                Type expectedException = ExpectedException(value, min, max);
                string expectedString = ExpectedString(type, value, min, ref expectedException);
                string testName = $"Convert({name}, {type.Name}{(expectedException is not null || expectedString?.Contains('∞') == true ? ", over/under flow" : "")})";
                yield return new TestCaseData(type, number, expectedException, expectedString) { TestName = testName };
            }
        }
    }

    // The integral IConvertible members narrow from ToUInt64 instead of going through decimal, which
    // used to build a BigInteger. These pin both the in-range values and the overflow boundary.
    [TestCase(0UL)]
    [TestCase(1UL)]
    [TestCase((ulong)byte.MaxValue)]
    [TestCase((ulong)short.MaxValue)]
    [TestCase((ulong)ushort.MaxValue)]
    [TestCase((ulong)int.MaxValue)]
    [TestCase((ulong)uint.MaxValue)]
    [TestCase((ulong)long.MaxValue)]
    [TestCase(ulong.MaxValue)]
    public void Integral_conversions_agree_with_a_checked_narrowing(ulong value)
    {
        IConvertible c = new UInt256(value);

        Assert.That(c.ToUInt64(null), Is.EqualTo(value));
        AssertNarrowing(() => c.ToByte(null), () => checked((byte)value));
        AssertNarrowing(() => c.ToSByte(null), () => checked((sbyte)value));
        AssertNarrowing(() => c.ToInt16(null), () => checked((short)value));
        AssertNarrowing(() => c.ToUInt16(null), () => checked((ushort)value));
        AssertNarrowing(() => c.ToInt32(null), () => checked((int)value));
        AssertNarrowing(() => c.ToUInt32(null), () => checked((uint)value));
        AssertNarrowing(() => c.ToInt64(null), () => checked((long)value));
    }

    [Test]
    public void Integral_conversions_overflow_above_the_low_limb()
    {
        IConvertible c = new UInt256(0, 1);

        Assert.Throws<OverflowException>(() => c.ToUInt64(null));
        Assert.Throws<OverflowException>(() => c.ToInt64(null));
        Assert.Throws<OverflowException>(() => c.ToInt32(null));
        Assert.Throws<OverflowException>(() => c.ToUInt16(null));
    }

    private static void AssertNarrowing<T>(Func<T> actual, Func<T> expected)
    {
        T want;
        try
        {
            want = expected();
        }
        catch (OverflowException)
        {
            Assert.Throws<OverflowException>(() => actual());
            return;
        }

        Assert.That(actual(), Is.EqualTo(want));
    }

    private static IEnumerable<BigInteger> ToStringCases()
    {
        yield return BigInteger.Zero;
        yield return BigInteger.One;
        yield return 9;
        yield return 10;
        yield return DecimalChunkValue - 1;
        yield return DecimalChunkValue;
        yield return DecimalChunkValue + 1;
        yield return ulong.MaxValue;
        yield return (BigInteger)ulong.MaxValue + 1;
        yield return TestNumbers.TwoTo64;
        yield return TestNumbers.TwoTo128;
        yield return TestNumbers.TwoTo192;
        yield return TestNumbers.UInt128Max;
        yield return TestNumbers.UInt192Max;
        yield return TestNumbers.UInt256Max;

        // Every power of ten a 256-bit value can reach, and its neighbours, to catch a chunk boundary.
        BigInteger power = 1;
        for (int i = 0; i < 77; i++)
        {
            power *= 10;
            yield return power - 1;
            yield return power;
        }
    }

    private static readonly BigInteger DecimalChunkValue = BigInteger.Pow(10, 19);

    [TestCaseSource(nameof(ToStringCases))]
    public void ToString_matches_the_BigInteger_rendering(BigInteger value)
    {
        // ToString formats from the limbs now; BigInteger is the reference it replaced.
        UInt256 a = (UInt256)value;

        Assert.That(a.ToString(), Is.EqualTo(value.ToString()));
    }
}
