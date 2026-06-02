// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
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
        Math.Sign(a.CompareTo(b)).Should().Be(ba.CompareTo(bb));
        Math.Sign(a.CompareTo((object)b)).Should().Be(ba.CompareTo(bb));
        (a < a).Should().BeFalse();
        a.CompareTo(a).Should().Be(0);
    }
}
