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
            (min.HasValue && max.HasValue && value > min && value < max) && (!minValue.HasValue || value >= minValue)
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
                yield return new TestCaseData(type, number, expectedException, expectedString) { TestName = $"{type.Name}.{name}" };
            }
        }
    }
}
