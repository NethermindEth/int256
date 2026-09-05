// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Collections.Generic;
using System.Numerics;
using FluentAssertions;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

[Parallelizable(ParallelScope.All)]
public class Int256Tests : UInt256TestsTemplate<Int256>
{

    private static BigInteger Postprocess(BigInteger big)
    {
        var bytes = big.ToByteArray();
        return new BigInteger(bytes.AsSpan().Slice(0, Math.Min(256 / 8, bytes.Length)));
    }

    public Int256Tests() : base((BigInteger x) => new Int256(x), (int x) => new Int256(x), Postprocess, TestNumbers.Int256Max) { }

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedTestCases))]
    public override void Add((BigInteger A, BigInteger B) test) => base.Add(test);

    [TestCaseSource(typeof(TernaryOps), nameof(TernaryOps.SignedTestCases))]
    public override void AddMod((BigInteger A, BigInteger B, BigInteger M) test) => base.AddMod(test);

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedTestCases))]
    public override void Subtract((BigInteger A, BigInteger B) test) => base.Subtract(test);

    [TestCaseSource(typeof(TernaryOps), nameof(TernaryOps.SignedTestCases))]
    public override void SubtractMod((BigInteger A, BigInteger B, BigInteger M) test) => base.SubtractModCore(test, false);

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedTestCases))]
    public override void Multiply((BigInteger A, BigInteger B) test) => base.Multiply(test);

    [TestCaseSource(typeof(TernaryOps), nameof(TernaryOps.SignedTestCases))]
    public override void MultiplyMod((BigInteger A, BigInteger B, BigInteger M) test) => base.MultiplyMod(test);

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedTestCases))]
    public override void Div((BigInteger A, BigInteger B) test) => base.Div(test);

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedTestCases))]
    public override void Mod((BigInteger A, BigInteger B) test) => base.Mod(test);

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedShiftTestCases))]
    public override void Exp((BigInteger A, int n) test) => base.Exp(test);

    [TestCaseSource(typeof(TernaryOps), nameof(TernaryOps.SignedTestCases))]
    public override void ExpMod((BigInteger A, BigInteger B, BigInteger M) test) => base.ExpMod(test);

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedShiftTestCases))]
    public override void Lsh((BigInteger A, int n) test) => base.Lsh(test);

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedShiftTestCases))]
    public override void Rsh((BigInteger A, int n) test) => base.Rsh(test);

    [TestCaseSource(typeof(UnaryOps), nameof(UnaryOps.SignedTestCases))]
    public override void ToBigIntegerAndBack(BigInteger test) => base.ToBigIntegerAndBack(test);

    [TestCaseSource(typeof(UnaryOps), nameof(UnaryOps.SignedTestCases))]
    public override void ToString(BigInteger test) => base.ToString(test);

    [TestCaseSource(typeof(Convertibles), nameof(Convertibles.SignedTestCases))]
    public void Convert(Type type, object value, Type expectedException, string expectedString)
    {
        string Expected(string valueString)
        {
            if (valueString.Contains("Infinity"))
            {
                return valueString.StartsWith('-') ? "-∞" : "∞";
            }
            string expected = valueString.Replace(",", "");
            return type == typeof(float) ? expected[..Math.Min(6, expected.Length)] : type == typeof(double) ? expected[..Math.Min(14, expected.Length)] : expected;
        }

        string valueString = value.ToString()!;
        Int256 item = (Int256)BigInteger.Parse(valueString);
        try
        {
            string expected = expectedString ?? Expected(valueString);
            string convertedValue = Expected(((IFormattable)System.Convert.ChangeType(item, type)).ToString("0.#", null));
            convertedValue.Should().BeEquivalentTo(expected);
        }
        catch (Exception e) when (e.GetType() == expectedException) { }
    }

    // The accessors that gained AggressiveInlining hints (Sign, IsZero, IsOne, CompareTo, <, >)
    // are behaviorally unchanged. These cases pin their results across the sign boundary so the
    // inlining change is locked in as a no-op on semantics.
    public static (string value, int sign, bool isZero, bool isOne)[] SignAccessorCases { get; } =
    [
        ("0", 0, true, false),
        ("1", 1, false, true),
        ("-1", -1, false, false),
        ("12345678901234567890", 1, false, false),
        ("-12345678901234567890", -1, false, false),
        ("57896044618658097711785492504343953926634992332820282019728792003956564819967", 1, false, false),   // Int256.Max
        ("-57896044618658097711785492504343953926634992332820282019728792003956564819968", -1, false, false),  // Int256.Min
    ];

    [TestCaseSource(nameof(SignAccessorCases))]
    public void SignZeroOne_Accessors((string value, int sign, bool isZero, bool isOne) test)
    {
        Int256 v = (Int256)BigInteger.Parse(test.value);
        v.Sign.Should().Be(test.sign);
        v.IsZero.Should().Be(test.isZero);
        v.IsOne.Should().Be(test.isOne);
        v.IsNegative.Should().Be(test.sign < 0);
    }

    public static IEnumerable<BigInteger> IsNegativeOracleCases
    {
        get
        {
            BigInteger min = -(BigInteger.One << 255);
            BigInteger max = (BigInteger.One << 255) - 1;
            BigInteger[] boundaries = [min, min + 1, -2, -1, 0, 1, 2, max - 1, max];
            foreach (BigInteger boundary in boundaries)
            {
                yield return boundary;
            }

            Random random = new(0x256);
            byte[] bytes = new byte[32];
            for (int i = 0; i < 16; i++)
            {
                random.NextBytes(bytes);
                BigInteger unsigned = new(bytes, isUnsigned: true, isBigEndian: false);
                yield return (unsigned & (BigInteger.One << 255)) == 0
                    ? unsigned
                    : unsigned - (BigInteger.One << 256);
            }
        }
    }

    [TestCaseSource(nameof(IsNegativeOracleCases))]
    public void IsNegative_MatchesBigInteger(BigInteger value)
    {
        Int256 candidate = new(value);

        candidate.IsNegative.Should().Be(value.Sign < 0);
    }

    [Test]
    public void Exp_NegativeExponent_Throws()
    {
        Action act = () => Int256.One.Exp(Int256.MinusOne, out Int256 _);

        act.Should().Throw<ArgumentException>();
    }

    // 0 - Int256.Min is 2**255, the one difference of two Int256 values that is not
    // itself an Int256, so the reduction has to happen before the difference wraps.
    [TestCase("17", "9")]
    [TestCase("-17", "9")]
    [TestCase("3", "2")]
    [TestCase("57896044618658097711785492504343953926634992332820282019728792003956564819967", "1")]
    public void SubtractMod_ZeroMinusMinValue_DoesNotWrap(string modulus, string expected)
    {
        Int256 min = (Int256)TestNumbers.Int256Min;

        Int256.SubtractMod(Int256.Zero, min, (Int256)BigInteger.Parse(modulus), out Int256 res);

        res.Convert(out BigInteger actual);
        actual.Should().Be(BigInteger.Parse(expected));
    }

    public static (string a, string b)[] SignedComparePairs { get; } =
    [
        ("0", "0"),
        ("-1", "1"),            // negative < positive
        ("1", "-1"),
        ("-2", "-1"),           // both negative: -2 < -1
        ("-1", "-2"),
        ("5", "5"),
        ("-12345678901234567890", "12345678901234567890"),
        ("57896044618658097711785492504343953926634992332820282019728792003956564819967",
         "-57896044618658097711785492504343953926634992332820282019728792003956564819968"),   // Max vs Min
    ];

    [TestCaseSource(nameof(SignedComparePairs))]
    public void Compare_And_Operators_MatchBigInteger((string a, string b) test)
    {
        BigInteger ba = BigInteger.Parse(test.a);
        BigInteger bb = BigInteger.Parse(test.b);
        Int256 a = (Int256)ba;
        Int256 b = (Int256)bb;

        (a < b).Should().Be(ba < bb);
        (a > b).Should().Be(ba > bb);
        Math.Sign(a.CompareTo(b)).Should().Be(Math.Sign(ba.CompareTo(bb)));
        Math.Sign(a.CompareTo((object)b)).Should().Be(Math.Sign(ba.CompareTo(bb)));
        Int256 same = a;
        (a < same).Should().BeFalse();
        a.CompareTo(same).Should().Be(0);
    }

    public static IEnumerable<(BigInteger, BigInteger)> CompareBoundaryCases
    {
        get
        {
            BigInteger min = -(BigInteger.One << 255);
            BigInteger[] values = [min, min + 1, -2, -1, 0, 1, 2, TestNumbers.Int256Max];
            foreach (BigInteger a in values)
            {
                foreach (BigInteger b in values)
                {
                    yield return (a, b);
                }
            }
        }
    }

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedTestCases))]
    [TestCaseSource(nameof(CompareBoundaryCases))]
    public void Compare_operators_match_BigInteger((BigInteger A, BigInteger B) test)
    {
        Int256 a = new(test.A);
        Int256 b = new(test.B);

        (a < b).Should().Be(test.A < test.B);
        (a > b).Should().Be(test.A > test.B);
        Math.Sign(a.CompareTo(b)).Should().Be(Math.Sign(test.A.CompareTo(test.B)));
    }

    [Test]
    public void Is_zero_and_is_one_signed()
    {
        Int256.Zero.IsZero.Should().BeTrue();
        Int256.One.IsZero.Should().BeFalse();
        Int256.MinusOne.IsZero.Should().BeFalse();
        new Int256(-(BigInteger.One << 255)).IsZero.Should().BeFalse();

        Int256.One.IsOne.Should().BeTrue();
        Int256.Zero.IsOne.Should().BeFalse();
        Int256.MinusOne.IsOne.Should().BeFalse();
        Int256.Max.IsOne.Should().BeFalse();
    }

    [TestCase(0L)]
    [TestCase(1L)]
    [TestCase(-1L)]
    [TestCase(long.MaxValue)]
    [TestCase(long.MinValue)]
    public void Long_conversion_agrees_with_the_BigInteger_path(long value)
    {
        // long used to convert through Int256(BigInteger); this pins the direct constructor to it.
        new Int256(value).Should().Be(new Int256((BigInteger)value));
        ((Int256)value).Should().Be(new Int256((BigInteger)value));
    }

    [Test]
    public void Max_is_two_to_the_255_minus_one()
    {
        // Max is written as limbs so the static constructor does not reference BigInteger; this pins
        // those limbs to the value they replaced.
        Int256 expected = new((BigInteger.One << 255) - 1);

        Int256.Max.Should().Be(expected);
        ((BigInteger)Int256.Max).Should().Be((BigInteger.One << 255) - 1);
    }

    [Test]
    public void Right_shift_of_a_negative_value_shifts_in_the_sign()
    {
        // A zero fill agrees with an arithmetic shift on every bit that survives, so it only shows up
        // in the limbs the shift vacates. Pin those limbs at each word boundary and one bit past one.
        Int256 x = new Int256(new UInt256(0x0123456789ABCDEFul, 0x1122334455667788ul, 0x99AABBCCDDEEFF00ul, 0xF000000000000001ul));
        const ulong Ones = ulong.MaxValue;

        x.RightShift(64, out Int256 res);
        ((UInt256)res).Should().Be(new UInt256(0x1122334455667788ul, 0x99AABBCCDDEEFF00ul, 0xF000000000000001ul, Ones));

        x.RightShift(128, out res);
        ((UInt256)res).Should().Be(new UInt256(0x99AABBCCDDEEFF00ul, 0xF000000000000001ul, Ones, Ones));

        x.RightShift(192, out res);
        ((UInt256)res).Should().Be(new UInt256(0xF000000000000001ul, Ones, Ones, Ones));

        x.RightShift(193, out res);
        ((UInt256)res).Should().Be(new UInt256(0xF800000000000000ul, Ones, Ones, Ones));

        x.RightShift(256, out res);
        ((UInt256)res).Should().Be(new UInt256(Ones, Ones, Ones, Ones));

        // The same counts on a positive value must vacate to zero, not to the other operand's sign.
        Int256 p = new Int256(new UInt256(0x0123456789ABCDEFul, 0x1122334455667788ul, 0x99AABBCCDDEEFF00ul, 0x7000000000000001ul));
        p.RightShift(192, out res);
        ((UInt256)res).Should().Be(new UInt256(0x7000000000000001ul, 0, 0, 0));
        p.RightShift(256, out res);
        ((UInt256)res).Should().Be(UInt256.Zero);
    }
}
