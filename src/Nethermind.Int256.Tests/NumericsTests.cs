// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Numerics;
using System.Text;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

/// <summary>
/// Generic math through <see cref="INumber{TSelf}"/>. Every operation goes through a generic helper: a direct
/// call binds to the public <c>in</c> members and would never reach the explicit interface implementations.
/// </summary>
[Parallelizable(ParallelScope.All)]
public class NumericsTests
{
    private static readonly BigInteger UInt256Max = TestNumbers.UInt256Max;
    private static readonly BigInteger Int256Max = TestNumbers.Int256Max;
    private static readonly BigInteger Int256Min = TestNumbers.Int256Min;

    private static IEnumerable<BigInteger> UnsignedValues => UnaryOps.TestCases.Concat(
    [
        UInt256Max,
        UInt256Max - 1,
        BigInteger.One << 255,
        (BigInteger.One << 255) - 1,
        TestNumbers.TwoTo64 + 1,
    ]).Distinct();

    private static IEnumerable<BigInteger> SignedValues => UnaryOps.SignedTestCases.Concat(
    [
        -1,
        -2,
        long.MinValue,
        -TestNumbers.TwoTo64,
        -TestNumbers.TwoTo128 + 1,
        Int256Max - 1,
    ]).Distinct();

    private static IEnumerable<(BigInteger, BigInteger)> UnsignedPairs =>
        from a in UnsignedValues from b in UnsignedValues select (a, b);

    private static IEnumerable<(BigInteger, BigInteger)> SignedPairs =>
        from a in SignedValues from b in SignedValues select (a, b);

    private static UInt256 U(BigInteger value) => (UInt256)value;

    private static Int256 S(BigInteger value) => (Int256)value;

    private static BigInteger Wrap(BigInteger value, int bits, bool signed)
    {
        BigInteger modulus = BigInteger.One << bits;
        BigInteger result = ((value % modulus) + modulus) % modulus;
        return signed && result >= modulus >> 1 ? result - modulus : result;
    }

    // Generic entry points: these bind to the interface members.
    private static T Add<T>(T a, T b) where T : INumber<T> => a + b;
    private static T CheckedAdd<T>(T a, T b) where T : INumber<T> => checked(a + b);
    private static T Sub<T>(T a, T b) where T : INumber<T> => a - b;
    private static T CheckedSub<T>(T a, T b) where T : INumber<T> => checked(a - b);
    private static T Mul<T>(T a, T b) where T : INumber<T> => a * b;
    private static T CheckedMul<T>(T a, T b) where T : INumber<T> => checked(a * b);
    private static T Div<T>(T a, T b) where T : INumber<T> => a / b;
    private static T CheckedDiv<T>(T a, T b) where T : INumber<T> => checked(a / b);
    private static T Rem<T>(T a, T b) where T : INumber<T> => a % b;
    private static T Neg<T>(T a) where T : INumber<T> => -a;
    private static T CheckedNeg<T>(T a) where T : INumber<T> => checked(-a);
    private static T Plus<T>(T a) where T : INumber<T> => +a;
    private static T Inc<T>(T a) where T : INumber<T> => ++a;
    private static T CheckedInc<T>(T a) where T : INumber<T> => checked(++a);
    private static T Dec<T>(T a) where T : INumber<T> => --a;
    private static T CheckedDec<T>(T a) where T : INumber<T> => checked(--a);
    private static bool Lt<T>(T a, T b) where T : INumber<T> => a < b;
    private static bool Le<T>(T a, T b) where T : INumber<T> => a <= b;
    private static bool Gt<T>(T a, T b) where T : INumber<T> => a > b;
    private static bool Ge<T>(T a, T b) where T : INumber<T> => a >= b;
    private static bool Eq<T>(T a, T b) where T : INumber<T> => a == b;
    private static bool Ne<T>(T a, T b) where T : INumber<T> => a != b;

    private static BigInteger ToBig<T>(T value) where T : INumberBase<T> => value switch
    {
        UInt256 u => (BigInteger)u,
        Int256 s => (BigInteger)s,
        _ => BigInteger.CreateChecked(value),
    };

    [TestCaseSource(nameof(UnsignedPairs))]
    public void UInt256_arithmetic((BigInteger A, BigInteger B) test)
    {
        (BigInteger a, BigInteger b) = test;
        UInt256 x = U(a), y = U(b);

        Assert.That((BigInteger)Add(x, y), Is.EqualTo(Wrap(a + b, 256, false)));
        AssertChecked(() => CheckedAdd(x, y), a + b, 0, UInt256Max);

        // Underflow throws either way, as the public operator does.
        AssertChecked(() => Sub(x, y), a - b, 0, UInt256Max);
        AssertChecked(() => CheckedSub(x, y), a - b, 0, UInt256Max);

        Assert.That((BigInteger)Mul(x, y), Is.EqualTo(Wrap(a * b, 256, false)));
        AssertChecked(() => CheckedMul(x, y), a * b, 0, UInt256Max);

        if (b.IsZero)
        {
            Assert.Throws<DivideByZeroException>(() => Div(x, y));
            Assert.Throws<DivideByZeroException>(() => Rem(x, y));
        }
        else
        {
            Assert.That((BigInteger)Div(x, y), Is.EqualTo(a / b));
            Assert.That((BigInteger)CheckedDiv(x, y), Is.EqualTo(a / b));
            Assert.That((BigInteger)Rem(x, y), Is.EqualTo(a % b));
        }

        Assert.That(Lt(x, y), Is.EqualTo(a < b));
        Assert.That(Le(x, y), Is.EqualTo(a <= b));
        Assert.That(Gt(x, y), Is.EqualTo(a > b));
        Assert.That(Ge(x, y), Is.EqualTo(a >= b));
        Assert.That(Eq(x, y), Is.EqualTo(a == b));
        Assert.That(Ne(x, y), Is.EqualTo(a != b));

        Assert.That((BigInteger)Max(x, y), Is.EqualTo(BigInteger.Max(a, b)));
        Assert.That((BigInteger)Min(x, y), Is.EqualTo(BigInteger.Min(a, b)));
        Assert.That((BigInteger)MaxMagnitude(x, y), Is.EqualTo(BigInteger.MaxMagnitude(a, b)));
        Assert.That((BigInteger)MinMagnitude(x, y), Is.EqualTo(BigInteger.MinMagnitude(a, b)));
        Assert.That((BigInteger)MultiplyAddEstimate(x, y, x), Is.EqualTo(Wrap(a * b + a, 256, false)));
    }

    [TestCaseSource(nameof(SignedPairs))]
    public void Int256_arithmetic((BigInteger A, BigInteger B) test)
    {
        (BigInteger a, BigInteger b) = test;
        Int256 x = S(a), y = S(b);

        Assert.That((BigInteger)Add(x, y), Is.EqualTo(Wrap(a + b, 256, true)));
        AssertChecked(() => CheckedAdd(x, y), a + b, Int256Min, Int256Max);
        Assert.That((BigInteger)Sub(x, y), Is.EqualTo(Wrap(a - b, 256, true)));
        AssertChecked(() => CheckedSub(x, y), a - b, Int256Min, Int256Max);
        Assert.That((BigInteger)Mul(x, y), Is.EqualTo(Wrap(a * b, 256, true)));
        AssertChecked(() => CheckedMul(x, y), a * b, Int256Min, Int256Max);

        if (b.IsZero)
        {
            Assert.Throws<DivideByZeroException>(() => Div(x, y));
            Assert.Throws<DivideByZeroException>(() => Rem(x, y));
        }
        else
        {
            // Unchecked wraps MinValue / -1 like SDIV; checked throws.
            Assert.That((BigInteger)Div(x, y), Is.EqualTo(Wrap(BigInteger.Divide(a, b), 256, true)));
            AssertChecked(() => CheckedDiv(x, y), BigInteger.Divide(a, b), Int256Min, Int256Max);
            Assert.That((BigInteger)Rem(x, y), Is.EqualTo(BigInteger.Remainder(a, b)));
        }

        Assert.That(Lt(x, y), Is.EqualTo(a < b));
        Assert.That(Le(x, y), Is.EqualTo(a <= b));
        Assert.That(Gt(x, y), Is.EqualTo(a > b));
        Assert.That(Ge(x, y), Is.EqualTo(a >= b));
        Assert.That(Eq(x, y), Is.EqualTo(a == b));
        Assert.That(Ne(x, y), Is.EqualTo(a != b));

        Assert.That((BigInteger)Max(x, y), Is.EqualTo(BigInteger.Max(a, b)));
        Assert.That((BigInteger)Min(x, y), Is.EqualTo(BigInteger.Min(a, b)));
        Assert.That((BigInteger)MaxMagnitude(x, y), Is.EqualTo(BigInteger.MaxMagnitude(a, b)));
        Assert.That((BigInteger)MinMagnitude(x, y), Is.EqualTo(BigInteger.MinMagnitude(a, b)));
        AssertChecked(() => CopySign(x, y), a.Sign != 0 && (a < 0) != (b < 0) ? -a : a, Int256Min, Int256Max);
    }

    private static T Max<T>(T x, T y) where T : INumber<T> => T.Max(x, y);
    private static T Min<T>(T x, T y) where T : INumber<T> => T.Min(x, y);
    private static T MaxMagnitude<T>(T x, T y) where T : INumber<T> => T.MaxMagnitude(x, y);
    private static T MinMagnitude<T>(T x, T y) where T : INumber<T> => T.MinMagnitude(x, y);
    private static T MultiplyAddEstimate<T>(T x, T y, T z) where T : INumber<T> => T.MultiplyAddEstimate(x, y, z);
    private static T CopySign<T>(T x, T y) where T : INumber<T> => T.CopySign(x, y);

    private static void AssertChecked<T>(Func<T> operation, BigInteger expected, BigInteger min, BigInteger max)
        where T : INumberBase<T>
    {
        if (expected < min || expected > max)
        {
            Assert.Throws<OverflowException>(() => operation());
        }
        else
        {
            Assert.That(ToBig(operation()), Is.EqualTo(expected));
        }
    }

    [TestCaseSource(nameof(UnsignedValues))]
    public void UInt256_unary(BigInteger a)
    {
        UInt256 x = U(a);
        Assert.That((BigInteger)Plus(x), Is.EqualTo(a));
        AssertChecked(() => Neg(x), -a, 0, UInt256Max);
        AssertChecked(() => CheckedNeg(x), -a, 0, UInt256Max);
        Assert.That((BigInteger)Inc(x), Is.EqualTo(Wrap(a + 1, 256, false)));
        AssertChecked(() => CheckedInc(x), a + 1, 0, UInt256Max);
        AssertChecked(() => Dec(x), a - 1, 0, UInt256Max);
        AssertChecked(() => CheckedDec(x), a - 1, 0, UInt256Max);

        Assert.That((BigInteger)Abs(x), Is.EqualTo(a));
        Assert.That(Sign(x), Is.EqualTo(a.Sign));
        Assert.That(IsZero(x), Is.EqualTo(a.IsZero));
        Assert.That(IsNegative(x), Is.False);
        Assert.That(IsPositive(x), Is.True);
        Assert.That(IsEvenInteger(x), Is.EqualTo(a.IsEven));
        Assert.That(IsOddInteger(x), Is.EqualTo(!a.IsEven));
        Assert.That(IsNormal(x), Is.EqualTo(!a.IsZero));
        Assert.That((BigInteger)CopySign(x, x), Is.EqualTo(a));
    }

    [TestCaseSource(nameof(SignedValues))]
    public void Int256_unary(BigInteger a)
    {
        Int256 x = S(a);
        Assert.That((BigInteger)Plus(x), Is.EqualTo(a));
        Assert.That((BigInteger)Neg(x), Is.EqualTo(Wrap(-a, 256, true)));
        AssertChecked(() => CheckedNeg(x), -a, Int256Min, Int256Max);
        Assert.That((BigInteger)Inc(x), Is.EqualTo(Wrap(a + 1, 256, true)));
        AssertChecked(() => CheckedInc(x), a + 1, Int256Min, Int256Max);
        Assert.That((BigInteger)Dec(x), Is.EqualTo(Wrap(a - 1, 256, true)));
        AssertChecked(() => CheckedDec(x), a - 1, Int256Min, Int256Max);

        AssertChecked(() => Abs(x), BigInteger.Abs(a), Int256Min, Int256Max);
        Assert.That(Sign(x), Is.EqualTo(a.Sign));
        Assert.That(IsZero(x), Is.EqualTo(a.IsZero));
        Assert.That(IsNegative(x), Is.EqualTo(a < 0));
        Assert.That(IsPositive(x), Is.EqualTo(a >= 0));
        Assert.That(IsEvenInteger(x), Is.EqualTo(a.IsEven));
        Assert.That(IsOddInteger(x), Is.EqualTo(!a.IsEven));
        Assert.That(IsNormal(x), Is.EqualTo(!a.IsZero));
    }

    private static T Abs<T>(T x) where T : INumber<T> => T.Abs(x);
    private static int Sign<T>(T x) where T : INumber<T> => T.Sign(x);
    private static bool IsZero<T>(T x) where T : INumber<T> => T.IsZero(x);
    private static bool IsNegative<T>(T x) where T : INumber<T> => T.IsNegative(x);
    private static bool IsPositive<T>(T x) where T : INumber<T> => T.IsPositive(x);
    private static bool IsEvenInteger<T>(T x) where T : INumber<T> => T.IsEvenInteger(x);
    private static bool IsOddInteger<T>(T x) where T : INumber<T> => T.IsOddInteger(x);
    private static bool IsNormal<T>(T x) where T : INumber<T> => T.IsNormal(x);

    [Test]
    public void Constants()
    {
        AssertConstants<UInt256>(0, UInt256Max);
        AssertConstants<Int256>(Int256Min, Int256Max);
        Assert.That((BigInteger)NegativeOne<Int256>(), Is.EqualTo(BigInteger.MinusOne));
    }

    private static void AssertConstants<T>(BigInteger min, BigInteger max) where T : INumber<T>, IMinMaxValue<T>
    {
        Assert.That(ToBig(T.Zero), Is.EqualTo(BigInteger.Zero));
        Assert.That(ToBig(T.One), Is.EqualTo(BigInteger.One));
        Assert.That(ToBig(T.AdditiveIdentity), Is.EqualTo(BigInteger.Zero));
        Assert.That(ToBig(T.MultiplicativeIdentity), Is.EqualTo(BigInteger.One));
        Assert.That(ToBig(T.MinValue), Is.EqualTo(min));
        Assert.That(ToBig(T.MaxValue), Is.EqualTo(max));
        Assert.That(Radix<T>(), Is.EqualTo(2));
    }

    private static int Radix<T>() where T : INumber<T> => T.Radix;
    private static T NegativeOne<T>() where T : ISignedNumber<T> => T.NegativeOne;

    [Test]
    public void Clamp_orders_and_rejects_inverted_bounds()
    {
        Assert.That((BigInteger)Clamp(U(5), U(10), U(20)), Is.EqualTo((BigInteger)10));
        Assert.That((BigInteger)Clamp(U(UInt256Max), U(10), U(20)), Is.EqualTo((BigInteger)20));
        Assert.That((BigInteger)Clamp(U(15), U(10), U(20)), Is.EqualTo((BigInteger)15));
        Assert.Throws<ArgumentException>(() => Clamp(U(15), U(20), U(10)));

        Assert.That((BigInteger)Clamp(S(Int256Min), S(-10), S(20)), Is.EqualTo((BigInteger)(-10)));
        Assert.That((BigInteger)Clamp(S(Int256Max), S(-10), S(20)), Is.EqualTo((BigInteger)20));
        Assert.That((BigInteger)Clamp(S(-5), S(-10), S(20)), Is.EqualTo((BigInteger)(-5)));
        Assert.Throws<ArgumentException>(() => Clamp(S(0), S(1), S(-1)));
    }

    private static T Clamp<T>(T value, T min, T max) where T : INumber<T> => T.Clamp(value, min, max);

    // Conversions

    private static IEnumerable<BigInteger> IntegerSamples(BigInteger min, BigInteger max) =>
        new[] { min, min + 1, -1, 0, 1, max - 1, max, max + 1, min - 1 }.Distinct();

    private static void AssertConversions<TFrom, TTo>(TFrom value, BigInteger big, BigInteger min, BigInteger max, int bits, bool signed)
        where TFrom : INumberBase<TFrom>
        where TTo : INumberBase<TTo>
    {
        string context = $"{typeof(TFrom).Name} {big} -> {typeof(TTo).Name}";
        if (big >= min && big <= max)
        {
            Assert.That(ToBig(TTo.CreateChecked(value)), Is.EqualTo(big), context);
        }
        else
        {
            Assert.Throws<OverflowException>(() => TTo.CreateChecked(value), context);
        }

        Assert.That(ToBig(TTo.CreateSaturating(value)), Is.EqualTo(BigInteger.Clamp(big, min, max)), context);
        Assert.That(ToBig(TTo.CreateTruncating(value)), Is.EqualTo(Wrap(big, bits, signed)), context);
    }

    private static void AssertIntegerRoundTrips<T>(BigInteger min, BigInteger max, int bits) where T : INumberBase<T>
    {
        bool signed = min < 0;
        foreach (BigInteger big in UnsignedValues.Concat(IntegerSamples(min, max)).Where(v => v >= 0 && v <= UInt256Max))
        {
            AssertConversions<UInt256, T>(U(big), big, min, max, bits, signed);
        }

        foreach (BigInteger big in SignedValues.Concat(IntegerSamples(min, max)).Where(v => v >= Int256Min && v <= Int256Max))
        {
            AssertConversions<Int256, T>(S(big), big, min, max, bits, signed);
        }

        foreach (BigInteger big in IntegerSamples(min, max).Where(v => v >= min && v <= max))
        {
            T value = T.CreateChecked(big);
            AssertConversions<T, UInt256>(value, big, 0, UInt256Max, 256, false);
            AssertConversions<T, Int256>(value, big, Int256Min, Int256Max, 256, true);
        }
    }

    [Test] public void Converts_byte() => AssertIntegerRoundTrips<byte>(byte.MinValue, byte.MaxValue, 8);
    [Test] public void Converts_sbyte() => AssertIntegerRoundTrips<sbyte>(sbyte.MinValue, sbyte.MaxValue, 8);
    [Test] public void Converts_char() => AssertIntegerRoundTrips<char>(char.MinValue, char.MaxValue, 16);
    [Test] public void Converts_short() => AssertIntegerRoundTrips<short>(short.MinValue, short.MaxValue, 16);
    [Test] public void Converts_ushort() => AssertIntegerRoundTrips<ushort>(ushort.MinValue, ushort.MaxValue, 16);
    [Test] public void Converts_int() => AssertIntegerRoundTrips<int>(int.MinValue, int.MaxValue, 32);
    [Test] public void Converts_uint() => AssertIntegerRoundTrips<uint>(uint.MinValue, uint.MaxValue, 32);
    [Test] public void Converts_long() => AssertIntegerRoundTrips<long>(long.MinValue, long.MaxValue, 64);
    [Test] public void Converts_ulong() => AssertIntegerRoundTrips<ulong>(ulong.MinValue, ulong.MaxValue, 64);
    [Test] public void Converts_nint() => AssertIntegerRoundTrips<nint>(nint.MinValue, nint.MaxValue, IntPtr.Size * 8);
    [Test] public void Converts_nuint() => AssertIntegerRoundTrips<nuint>(nuint.MinValue, nuint.MaxValue, IntPtr.Size * 8);
    [Test] public void Converts_Int128() => AssertIntegerRoundTrips<Int128>((BigInteger)Int128.MinValue, (BigInteger)Int128.MaxValue, 128);
    [Test] public void Converts_UInt128() => AssertIntegerRoundTrips<UInt128>(0, (BigInteger)UInt128.MaxValue, 128);
    [Test] public void Converts_UInt256() => AssertIntegerRoundTrips<UInt256>(0, UInt256Max, 256);
    [Test] public void Converts_Int256() => AssertIntegerRoundTrips<Int256>(Int256Min, Int256Max, 256);

    [Test]
    public void Converts_BigInteger()
    {
        foreach (BigInteger big in UnsignedValues)
        {
            Assert.That(BigInteger.CreateChecked(U(big)), Is.EqualTo(big));
        }

        foreach (BigInteger big in SignedValues)
        {
            Assert.That(BigInteger.CreateChecked(S(big)), Is.EqualTo(big));
        }

        BigInteger[] wide = [.. UnsignedValues, .. SignedValues, TestNumbers.TwoTo256, -TestNumbers.TwoTo256 - 5, Int256Min - 1, BigInteger.One << 300];
        foreach (BigInteger big in wide)
        {
            AssertConversions<BigInteger, UInt256>(big, big, 0, UInt256Max, 256, false);
            AssertConversions<BigInteger, Int256>(big, big, Int256Min, Int256Max, 256, true);
        }
    }

    private static IEnumerable<double> Doubles =>
    [
        0.0, -0.0, 0.25, 0.999, 1.0, 1.5, -0.5, -0.999, -1.0, -1.5, 3e15, 9007199254740993.0, 1e19, 1.8446744073709552e19,
        1e30, 1e38, 3.4028235e38, 1.7e50, 1e76, Math.ScaleB(1, 255), -Math.ScaleB(1, 255), Math.ScaleB(1, 256),
        Math.BitDecrement(Math.ScaleB(1, 256)), Math.BitDecrement(Math.ScaleB(1, 255)), -Math.BitDecrement(Math.ScaleB(1, 255)),
        -Math.BitIncrement(Math.ScaleB(1, 255)), double.MaxValue, double.MinValue, double.Epsilon, double.NaN,
        double.PositiveInfinity, double.NegativeInfinity,
    ];

    // Truncation toward zero, then the floating-point rule: NaN gives zero, and truncating saturates.
    private static void AssertFromFloating<TFrom>(TFrom value, double asDouble) where TFrom : INumberBase<TFrom>
    {
        bool finite = double.IsFinite(asDouble);
        BigInteger truncated = finite ? new BigInteger(Math.Truncate(asDouble)) : BigInteger.Zero;
        BigInteger huge = TestNumbers.TwoTo256 * 4;
        BigInteger target = double.IsNaN(asDouble) ? 0 : !finite ? (asDouble > 0 ? huge : -huge) : truncated;
        string context = $"{typeof(TFrom).Name} {asDouble:R}";

        Check<UInt256>(0, UInt256Max);
        Check<Int256>(Int256Min, Int256Max);

        void Check<TTo>(BigInteger min, BigInteger max) where TTo : INumberBase<TTo>
        {
            if (!double.IsNaN(asDouble) && target >= min && target <= max)
            {
                Assert.That(ToBig(TTo.CreateChecked(value)), Is.EqualTo(target), context);
            }
            else
            {
                Assert.Throws<OverflowException>(() => TTo.CreateChecked(value), context);
            }

            BigInteger saturated = BigInteger.Clamp(target, min, max);
            Assert.That(ToBig(TTo.CreateSaturating(value)), Is.EqualTo(saturated), context);
            Assert.That(ToBig(TTo.CreateTruncating(value)), Is.EqualTo(saturated), context);
        }
    }

    [Test]
    public void Converts_from_floating_point()
    {
        foreach (double value in Doubles)
        {
            AssertFromFloating(value, value);
            AssertFromFloating((float)value, (float)value);
            AssertFromFloating((Half)value, (double)(Half)value);
        }
    }

    // double.Parse rounds correctly, so formatting the exact value in decimal gives the reference.
    [Test]
    public void Converts_to_floating_point_rounding_to_nearest_even()
    {
        IEnumerable<BigInteger> values = UnsignedValues.Concat(
        [
            (BigInteger.One << 53) + 1,
            // One limb: these round wrongly if a step goes through double first.
            (BigInteger.One << 54) + (BigInteger.One << 30) + 1,
            (BigInteger.One << 63) + (BigInteger.One << 39) + 1,
            (BigInteger.One << 63) + (BigInteger.One << 10) + 1,
            (BigInteger.One << 64) - 1,
            (BigInteger.One << 64) - (BigInteger.One << 10),
            (BigInteger.One << 54) + 2,
            (BigInteger.One << 54) + 6,
            (BigInteger.One << 100) + (BigInteger.One << 47),
            (BigInteger.One << 100) + (BigInteger.One << 47) + 1,
            (BigInteger.One << 100) + (BigInteger.One << 48) + (BigInteger.One << 47),
            (BigInteger.One << 200) - 1,
            (BigInteger.One << 128) - (BigInteger.One << 103),
            (BigInteger.One << 70) + (BigInteger.One << 46),
            (BigInteger.One << 70) + (BigInteger.One << 46) + 1,
            65519,
            65520,
            2047,
            2049,
            2051,
        ]);

        foreach (BigInteger big in values)
        {
            string text = big.ToString(CultureInfo.InvariantCulture);
            Assert.That(double.CreateChecked(U(big)), Is.EqualTo(double.Parse(text, CultureInfo.InvariantCulture)), text);
            Assert.That(float.CreateChecked(U(big)), Is.EqualTo(float.Parse(text, CultureInfo.InvariantCulture)), text);
            Assert.That(Half.CreateChecked(U(big)), Is.EqualTo(Half.Parse(text, CultureInfo.InvariantCulture)), text);

            if (big <= Int256Max)
            {
                Assert.That(double.CreateChecked(S(-big)), Is.EqualTo(double.Parse("-" + text, CultureInfo.InvariantCulture)), text);
                Assert.That(float.CreateSaturating(S(-big)), Is.EqualTo(float.Parse("-" + text, CultureInfo.InvariantCulture)), text);
                Assert.That(Half.CreateTruncating(S(-big)), Is.EqualTo(Half.Parse("-" + text, CultureInfo.InvariantCulture)), text);
            }
        }

        Assert.That(double.CreateChecked(S(Int256Min)), Is.EqualTo(-Math.ScaleB(1, 255)));
    }

    [Test]
    public void Converts_decimal()
    {
        decimal[] values = [0m, 0.9m, -0.9m, 1m, -1m, 1.5m, -1.5m, 12345678901234567890.5m, decimal.MaxValue, decimal.MinValue, -decimal.MaxValue + 1];
        foreach (decimal value in values)
        {
            BigInteger truncated = new(decimal.Truncate(value));
            AssertConversions<decimal, Int256>(value, truncated, Int256Min, Int256Max, 256, true);
            // Negative values saturate to zero when truncating too, as they do for UInt128.
            Assert.That((BigInteger)UInt256.CreateSaturating(value), Is.EqualTo(BigInteger.Max(truncated, 0)));
            Assert.That((BigInteger)UInt256.CreateTruncating(value), Is.EqualTo(BigInteger.Max(truncated, 0)));
            if (truncated < 0)
            {
                Assert.Throws<OverflowException>(() => UInt256.CreateChecked(value));
            }
            else
            {
                Assert.That((BigInteger)UInt256.CreateChecked(value), Is.EqualTo(truncated));
            }
        }

        BigInteger decimalMax = new(decimal.MaxValue);
        foreach (BigInteger big in UnsignedValues)
        {
            decimal saturated = (decimal)BigInteger.Min(big, decimalMax);
            AssertDecimal(U(big), big, saturated);
        }

        foreach (BigInteger big in SignedValues)
        {
            decimal saturated = (decimal)BigInteger.Clamp(big, -decimalMax, decimalMax);
            AssertDecimal(S(big), big, saturated);
        }

        void AssertDecimal<T>(T value, BigInteger big, decimal saturated) where T : INumberBase<T>
        {
            if (BigInteger.Abs(big) <= decimalMax)
            {
                Assert.That(decimal.CreateChecked(value), Is.EqualTo((decimal)big));
            }
            else
            {
                Assert.Throws<OverflowException>(() => decimal.CreateChecked(value));
            }

            Assert.That(decimal.CreateSaturating(value), Is.EqualTo(saturated));
            Assert.That(decimal.CreateTruncating(value), Is.EqualTo(saturated));
        }
    }

    // Parsing and formatting

    private static T Parse<T>(string s, NumberStyles style) where T : INumber<T> => T.Parse(s, style, CultureInfo.InvariantCulture);

    private static bool TryParse<T>(string s, NumberStyles style, out T result) where T : struct, INumber<T> =>
        T.TryParse(s.AsSpan(), style, CultureInfo.InvariantCulture, out result);

    private static T ParseDefault<T>(string s) where T : IParsable<T> => T.Parse(s, CultureInfo.InvariantCulture);

    private static T ParseUtf8<T>(string s) where T : INumber<T> => T.Parse(Encoding.UTF8.GetBytes(s), CultureInfo.InvariantCulture);

    [TestCaseSource(nameof(UnsignedValues))]
    public void UInt256_round_trips_through_text(BigInteger big)
    {
        UInt256 value = U(big);
        string expected = big.ToString(CultureInfo.InvariantCulture);
        AssertFormats(value, expected);

        Assert.That((BigInteger)ParseDefault<UInt256>(expected), Is.EqualTo(big));
        Assert.That((BigInteger)ParseUtf8<UInt256>(expected), Is.EqualTo(big));
        Assert.That((BigInteger)Parse<UInt256>($"  +{expected} ", NumberStyles.Integer), Is.EqualTo(big));
        Assert.That((BigInteger)Parse<UInt256>(big.ToString("x", CultureInfo.InvariantCulture), NumberStyles.HexNumber), Is.EqualTo(big));
        Assert.That((BigInteger)Parse<UInt256>(big.ToString("x", CultureInfo.InvariantCulture), NumberStyles.AllowHexSpecifier), Is.EqualTo(big));
        Assert.That((BigInteger)Parse<UInt256>(big.ToString("N0", CultureInfo.InvariantCulture), NumberStyles.Number), Is.EqualTo(big));
        Assert.That(value.ToString("X", CultureInfo.InvariantCulture), Is.EqualTo(big.ToString("X", CultureInfo.InvariantCulture)));
    }

    [TestCaseSource(nameof(SignedValues))]
    public void Int256_round_trips_through_text(BigInteger big)
    {
        Int256 value = S(big);
        string expected = big.ToString(CultureInfo.InvariantCulture);
        AssertFormats(value, expected);

        Assert.That((BigInteger)ParseDefault<Int256>(expected), Is.EqualTo(big));
        Assert.That((BigInteger)ParseUtf8<Int256>(expected), Is.EqualTo(big));
        Assert.That((BigInteger)Parse<Int256>($" {expected}  ", NumberStyles.Integer), Is.EqualTo(big));
        Assert.That((BigInteger)Parse<Int256>(big.ToString("N0", CultureInfo.InvariantCulture), NumberStyles.Number), Is.EqualTo(big));
        // Hex is the 256-bit two's complement.
        string hex = Wrap(big, 256, false).ToString("x64", CultureInfo.InvariantCulture)[^64..];
        Assert.That((BigInteger)Parse<Int256>(hex, NumberStyles.HexNumber), Is.EqualTo(big));
        Assert.That(value.ToString("X", CultureInfo.InvariantCulture), Is.EqualTo(big.ToString("X", CultureInfo.InvariantCulture)));
    }

    private static void AssertFormats<T>(T value, string expected) where T : INumber<T>
    {
        Assert.That(value.ToString(), Is.EqualTo(expected));
        Assert.That($"{value}", Is.EqualTo(expected));
        Assert.That(value.ToString(null, CultureInfo.InvariantCulture), Is.EqualTo(expected));
        Assert.That(value.ToString("D", CultureInfo.InvariantCulture), Is.EqualTo(expected));
        Assert.That(value.ToString("g", CultureInfo.InvariantCulture), Is.EqualTo(expected));
        Assert.That(value.ToString("D80", CultureInfo.InvariantCulture), Is.EqualTo(BigInteger.Parse(expected).ToString("D80", CultureInfo.InvariantCulture)));

        Span<char> chars = stackalloc char[100];
        Assert.That(value.TryFormat(chars, out int charsWritten, default, null), Is.True);
        Assert.That(chars[..charsWritten].ToString(), Is.EqualTo(expected));
        Assert.That(value.TryFormat(chars[..(expected.Length - 1)], out charsWritten, default, null), Is.False);
        Assert.That(charsWritten, Is.Zero);

        Span<byte> bytes = stackalloc byte[100];
        Assert.That(((IUtf8SpanFormattable)value).TryFormat(bytes, out int bytesWritten, default, null), Is.True);
        Assert.That(Encoding.UTF8.GetString(bytes[..bytesWritten]), Is.EqualTo(expected));
        Assert.That(((IUtf8SpanFormattable)value).TryFormat(bytes[..(expected.Length - 1)], out _, default, null), Is.False);
    }

    [Test]
    public void Decimal_digits_match_BigInteger_for_random_values()
    {
        foreach (BigInteger big in UnaryOps.RandomUnsigned(2000).Select((v, i) => i % 2 == 0 ? v : v * 2 + 1))
        {
            Assert.That(U(big).ToString(), Is.EqualTo(big.ToString(CultureInfo.InvariantCulture)));
        }

        foreach (BigInteger big in UnaryOps.RandomSigned(2000))
        {
            Assert.That(S(big).ToString(), Is.EqualTo(big.ToString(CultureInfo.InvariantCulture)));
        }
    }

    [Test]
    public void Signed_formatting_uses_the_culture_negative_sign_for_explicit_formats()
    {
        CultureInfo culture = (CultureInfo)CultureInfo.InvariantCulture.Clone();
        culture.NumberFormat.NegativeSign = "~";
        Int256 value = S(-42);
        Assert.That(value.ToString("D", culture), Is.EqualTo("~42"));
        Assert.That(value.ToString(null, culture), Is.EqualTo("-42"));
        Assert.That(value.ToString(), Is.EqualTo("-42"));
    }

    [TestCase("")]
    [TestCase(" ")]
    [TestCase("-1")]
    [TestCase("--1")]
    [TestCase("+-1")]
    [TestCase("1 2")]
    [TestCase("abc")]
    [TestCase("115792089237316195423570985008687907853269984665640564039457584007913129639936")]
    public void UInt256_rejects_invalid_text(string text)
    {
        Assert.That(TryParse(text, NumberStyles.Integer, out UInt256 _), Is.False);
        Assert.Throws<FormatException>(() => Parse<UInt256>(text, NumberStyles.Integer));
    }

    [TestCase("")]
    [TestCase("-")]
    [TestCase("--1")]
    [TestCase("-+1")]
    [TestCase("+-1")]
    [TestCase("- 1")]
    [TestCase("1-")]
    [TestCase("57896044618658097711785492504343953926634992332820282019728792003956564819968")]
    [TestCase("-57896044618658097711785492504343953926634992332820282019728792003956564819969")]
    public void Int256_rejects_invalid_text(string text)
    {
        Assert.That(TryParse(text, NumberStyles.Integer, out Int256 _), Is.False);
        Assert.Throws<FormatException>(() => Parse<Int256>(text, NumberStyles.Integer));
    }

    [Test]
    public void Parses_null_strings_as_failures()
    {
        Assert.That(TryParseString<UInt256>(null), Is.False);
        Assert.That(TryParseString<Int256>(null), Is.False);
        Assert.Throws<ArgumentNullException>(() => ParseDefault<UInt256>(null!));
        Assert.Throws<ArgumentNullException>(() => ParseDefault<Int256>(null!));
    }

    private static bool TryParseString<T>(string? s) where T : INumber<T> =>
        T.TryParse(s, NumberStyles.Integer, CultureInfo.InvariantCulture, out _);

    // Sums through the interface, the shape generic library code takes.
    private static T Sum<T>(IEnumerable<T> values) where T : INumber<T>
    {
        T total = T.Zero;
        foreach (T value in values)
        {
            total = checked(total + value);
        }

        return total;
    }

    [Test]
    public void Generic_algorithms_run_over_both_types()
    {
        Assert.That((BigInteger)Sum(Enumerable.Range(1, 100).Select(i => (UInt256)(ulong)i)), Is.EqualTo((BigInteger)5050));
        Assert.That((BigInteger)Sum(Enumerable.Range(-50, 101).Select(i => (Int256)i)), Is.EqualTo(BigInteger.Zero));
        Assert.Throws<OverflowException>(() => Sum([U(UInt256Max), U(1)]));
        Assert.Throws<OverflowException>(() => Sum([S(Int256Max), S(1)]));
    }
}
