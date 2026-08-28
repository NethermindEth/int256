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

    [TestCaseSource(typeof(TernaryOps), nameof(TernaryOps.SignedModTestCases))]
    public override void AddMod((BigInteger A, BigInteger B, BigInteger M) test) => base.AddMod(test);

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedTestCases))]
    public override void Subtract((BigInteger A, BigInteger B) test) => base.Subtract(test);

    [TestCaseSource(typeof(TernaryOps), nameof(TernaryOps.SignedModTestCases))]
    public override void SubtractMod((BigInteger A, BigInteger B, BigInteger M) test) => base.SubtractModCore(test, false);

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedTestCases))]
    public override void Multiply((BigInteger A, BigInteger B) test) => base.Multiply(test);

    [TestCaseSource(typeof(TernaryOps), nameof(TernaryOps.SignedModTestCases))]
    public override void MultiplyMod((BigInteger A, BigInteger B, BigInteger M) test) => base.MultiplyMod(test);

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedTestCases))]
    public override void Div((BigInteger A, BigInteger B) test) => base.Div(test);

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedTestCases))]
    public override void Mod((BigInteger A, BigInteger B) test) => base.Mod(test);

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedShiftTestCases))]
    public override void Exp((BigInteger A, int n) test) => base.Exp(test);

    [TestCaseSource(typeof(TernaryOps), nameof(TernaryOps.SignedModTestCases))]
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
    public void NegativityGatedOperations_MatchBigInteger()
    {
        BigInteger min = -(BigInteger.One << 255);
        BigInteger max = (BigInteger.One << 255) - 1;
        BigInteger[] values = [min, min + 1, -2, -1, 0, 1, 2, max - 1, max];
        BigInteger[] operationValues = [-17, -2, -1, 0, 1, 2, 17];
        BigInteger[] moduli = [min, -17, -1, 1, 17, max];
        int[] shifts = [0, 1, 63, 64, 127, 128, 191, 192, 255, 256, 257];

        foreach (BigInteger a in values)
        {
            Int256 intA = new(a);
            foreach (int shift in shifts)
            {
                intA.RightShift(shift, out Int256 shifted);
                shifted.Convert(out BigInteger shiftedValue);
                shiftedValue.Should().Be(a >> shift, $"Rsh({a}, {shift})");
            }

            foreach (BigInteger exponent in new BigInteger[] { 0, 1, 2, 3 })
            {
                Int256 intExponent = new(exponent);
                intA.Exp(intExponent, out Int256 raised);
                raised.Convert(out BigInteger raisedValue);
                raisedValue.Should().Be(Postprocess(BigInteger.Pow(a, (int)exponent)), $"Exp({a}, {exponent})");

                foreach (BigInteger modulus in moduli)
                {
                    intA.ExpMod(intExponent, new Int256(modulus), out Int256 modularRaised);
                    modularRaised.Convert(out BigInteger modularRaisedValue);
                    BigInteger magnitude = BigInteger.ModPow(BigInteger.Abs(a), exponent, BigInteger.Abs(modulus));
                    BigInteger expected = a.Sign < 0 && !exponent.IsEven ? -magnitude : magnitude;
                    modularRaisedValue.Should().Be(Postprocess(expected), $"ExpMod({a}, {exponent}, {modulus})");
                }
            }

            if (a < -17 || a > 17)
            {
                continue;
            }

            foreach (BigInteger b in operationValues)
            {
                Int256 intB = new(b);

                AssertMultiplyDivideAndMod(a, b);

                if (b.IsZero)
                {
                    continue;
                }

                foreach (BigInteger modulus in moduli)
                {
                    Int256 intModulus = new(modulus);

                    intA.AddMod(intB, intModulus, out Int256 added);
                    added.Convert(out BigInteger addedValue);
                    addedValue.Should().Be(Postprocess((a + b) % modulus), $"AddMod({a}, {b}, {modulus})");

                    intA.SubtractMod(intB, intModulus, out Int256 subtracted);
                    subtracted.Convert(out BigInteger subtractedValue);
                    subtractedValue.Should().Be(Postprocess((a - b) % modulus), $"SubtractMod({a}, {b}, {modulus})");

                    intA.MultiplyMod(intB, intModulus, out Int256 multipliedModular);
                    multipliedModular.Convert(out BigInteger multipliedModularValue);
                    multipliedModularValue.Should().Be(Postprocess((a * b) % modulus), $"MultiplyMod({a}, {b}, {modulus})");
                }
            }
        }

        foreach (BigInteger a in values)
        {
            foreach (BigInteger b in values)
            {
                AssertMultiplyDivideAndMod(a, b);
            }
        }

        foreach (BigInteger value in values)
        {
            Action divideByZero = () => new Int256(value).Divide(Int256.Zero, out Int256 _);
            divideByZero.Should().Throw<DivideByZeroException>();

            Action modByZero = () => new Int256(value).Mod(Int256.Zero, out Int256 _);
            modByZero.Should().Throw<DivideByZeroException>();
        }

        Action negativeExponent = () => Int256.One.Exp(Int256.MinusOne, out Int256 _);
        negativeExponent.Should().Throw<ArgumentException>().WithMessage("exponent must be non-negative");

        Action negativeModularExponent = () => Int256.One.ExpMod(Int256.MinusOne, Int256.One, out Int256 _);
        negativeModularExponent.Should().Throw<ArgumentException>().WithMessage("exponent must not be negative");
    }

    private static void AssertMultiplyDivideAndMod(BigInteger a, BigInteger b)
    {
        Int256 intA = new(a);
        Int256 intB = new(b);

        intA.Multiply(intB, out Int256 multiplied);
        multiplied.Convert(out BigInteger multipliedValue);
        multipliedValue.Should().Be(Postprocess(a * b), $"Multiply({a}, {b})");

        if (b.IsZero)
        {
            return;
        }

        intA.Divide(intB, out Int256 divided);
        divided.Convert(out BigInteger dividedValue);
        dividedValue.Should().Be(Postprocess(a / b), $"Divide({a}, {b})");

        intA.Mod(intB, out Int256 remainder);
        remainder.Convert(out BigInteger remainderValue);
        remainderValue.Should().Be(Postprocess(a % b), $"Mod({a}, {b})");
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
}
