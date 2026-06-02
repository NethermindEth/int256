// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Globalization;
using System.Numerics;
using FluentAssertions;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

public abstract class UInt256TestsTemplate<T> where T : IInteger<T>
{
    private static readonly BigInteger Mod256 = BigInteger.One << 256;
    private static readonly BigInteger Mask256 = Mod256 - 1;
    private static readonly BigInteger SignBit = BigInteger.One << 255;

    private static BigInteger WrapUInt256(BigInteger x)
        => x & Mask256; // always 0..2^256-1

    private static BigInteger WrapInt256(BigInteger x)
    {
        x &= Mask256; // low 256 bits as unsigned
        if (x >= SignBit) x -= Mod256; // interpret as signed two's-complement
        return x;
    }

    protected readonly Func<BigInteger, T> convert;
    protected readonly Func<int, T> convertFromInt;
    protected readonly Func<BigInteger, BigInteger> postprocess;
    protected readonly BigInteger maxValue;

    protected UInt256TestsTemplate(Func<BigInteger, T> convert, Func<int, T> convertFromInt, Func<BigInteger, BigInteger> postprocess, BigInteger maxValue)
    {
        this.convert = convert;
        this.convertFromInt = convertFromInt;
        this.postprocess = postprocess;
        this.maxValue = maxValue;
    }

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
    public virtual void Add((BigInteger A, BigInteger B) test)
    {
        BigInteger resBigInt = test.A + test.B;
        resBigInt %= (BigInteger.One << 256);
        resBigInt = postprocess(resBigInt);

        T a = convert(test.A);
        T b = convert(test.B);
        a.Add(b, out T res);
        res.Convert(out BigInteger resUInt256);

        resUInt256.Should().Be(resBigInt);

        // Test reusing input as output
        a.Add(b, out a);
        a.Convert(out resUInt256);
        resUInt256.Should().Be(resBigInt);

        a = convert(test.A);

        a.Add(b, out b);
        b.Convert(out resUInt256);
        resUInt256.Should().Be(resBigInt);
    }

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
    public virtual void AddOverflow((BigInteger A, BigInteger B) test)
    {
        BigInteger resUInt256;
        BigInteger resBigInt = test.A + test.B;
        bool expectedOverflow = test.A + test.B > (BigInteger)UInt256.MaxValue;

        resBigInt %= (BigInteger.One << 256);
        resBigInt = postprocess(resBigInt);
        T uint256a = convert(test.A);
        T uint256b = convert(test.B);

        bool overflow = T.AddOverflow(uint256a, uint256b, out T res);
        res.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);
        overflow.Should().Be(expectedOverflow);

        // Test reusing input as output
        overflow = T.AddOverflow(uint256a, uint256b, out uint256a);
        uint256a.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);
        overflow.Should().Be(expectedOverflow);

        uint256a = convert(test.A);

        overflow = T.AddOverflow(uint256a, uint256b, out uint256b);
        uint256b.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);
        overflow.Should().Be(expectedOverflow);
    }

    [TestCaseSource(typeof(TernaryOps), nameof(TernaryOps.TestCases))]
    public virtual void AddMod((BigInteger A, BigInteger B, BigInteger M) test)
    {
        T uint256a = convert(test.A);
        T uint256b = convert(test.B);
        T uint256m = convert(test.M);
        if (test.M.IsZero)
        {
            Action act = () => uint256a.AddMod(uint256b, uint256m, out T res);
            act.Should().Throw<DivideByZeroException>();
            return;
        }
        BigInteger resBigInt = (test.A + test.B) % test.M;
        resBigInt %= (BigInteger.One << 256);
        resBigInt = postprocess(resBigInt);

        uint256a.AddMod(uint256b, uint256m, out T res);
        res.Convert(out BigInteger resUInt256);

        resUInt256.Should().Be(resBigInt);

        // Test reusing input as output
        uint256a.AddMod(uint256b, uint256m, out uint256a);
        uint256a.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);

        uint256a = convert(test.A);

        uint256a.AddMod(uint256b, uint256m, out uint256b);
        uint256b.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);

        uint256b = convert(test.B);

        uint256a.AddMod(uint256b, uint256m, out uint256m);
        uint256m.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);
    }

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
    public virtual void Subtract((BigInteger A, BigInteger B) test)
    {
        if (test.A < test.B)
        {
            return;
        }

        BigInteger resBigInt = test.A - test.B;
        resBigInt %= BigInteger.One << 256;
        resBigInt = postprocess(resBigInt);

        T uint256a = convert(test.A);
        T uint256b = convert(test.B);
        uint256a.Subtract(uint256b, out T res);
        res.Convert(out BigInteger resUInt256);

        resUInt256.Should().Be(resBigInt);

        // Test reusing input as output
        uint256a.Subtract(uint256b, out uint256a);
        uint256a.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);

        uint256a = convert(test.A);

        uint256a.Subtract(uint256b, out uint256b);
        uint256b.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);
    }

    [TestCaseSource(typeof(TernaryOps), nameof(TernaryOps.TestCases))]
    public virtual void SubtractMod((BigInteger A, BigInteger B, BigInteger M) test)
    {
        SubtractModCore(test, true);
    }

    protected void SubtractModCore((BigInteger A, BigInteger B, BigInteger M) test, bool convertToUnsigned)
    {
        T uint256a = convert(test.A);
        T uint256b = convert(test.B);
        T uint256m = convert(test.M);
        if (test.M.IsZero)
        {
            Action act = () => uint256a.SubtractMod(uint256b, uint256m, out T res);
            act.Should().Throw<DivideByZeroException>();
            return;
        }
        BigInteger resBigInt = (test.A - test.B) % test.M;

        // convert to unsigned modular value
        if (convertToUnsigned && resBigInt.Sign == -1)
        {
            resBigInt = test.M + resBigInt;
        }

        resBigInt %= (BigInteger.One << 256);
        resBigInt = postprocess(resBigInt);

        uint256a.SubtractMod(uint256b, uint256m, out T res);
        res.Convert(out BigInteger resUInt256);

        resUInt256.Should().Be(resBigInt);

        // Test reusing input as output
        uint256a.SubtractMod(uint256b, uint256m, out uint256a);
        uint256a.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);

        uint256a = convert(test.A);

        uint256a.SubtractMod(uint256b, uint256m, out uint256b);
        uint256b.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);

        uint256b = convert(test.B);

        uint256a.SubtractMod(uint256b, uint256m, out uint256m);
        uint256m.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);
    }

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
    public virtual void SubtractOverflow((BigInteger A, BigInteger B) test)
    {
        BigInteger resBigInt = test.A - test.B;
        resBigInt %= BigInteger.One << 256;
        resBigInt = postprocess(resBigInt);
        T uint256a = convert(test.A);
        T uint256b = convert(test.B);

        SubtractTest(in uint256a, in uint256b, out T res);

        // Test reusing input as output
        SubtractTest(in uint256a, in uint256b, out uint256a);

        uint256a = convert(test.A);

        SubtractTest(in uint256a, in uint256b, out uint256b);

        void SubtractTest(in T uint256a, in T uint256b, out T res)
        {
            BigInteger resUInt256;
            if (test.A >= test.B)
            {
                if (uint256a is UInt256 a && uint256b is UInt256 b)
                {
                    res = (T)(object)(a - b);
                    res.Convert(out resUInt256);
                }
                else
                {
                    uint256a.Subtract(uint256b, out res);
                    res.Convert(out resUInt256);
                }
                resUInt256.Should().Be(resBigInt);
            }
            else
            {
                if (uint256a is UInt256 a && uint256b is UInt256 b)
                {
                    res = default!;
                    a.Invoking(y => y - b)
                        .Should().Throw<OverflowException>()
                        .WithMessage($"Underflow in subtraction {a} - {b}");
                }
                else
                {
                    uint256a.Subtract(uint256b, out res);
                    res.Convert(out resUInt256);
                    resUInt256.Should().Be(resBigInt);
                }
            }
        }
    }

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
    public virtual void Multiply((BigInteger A, BigInteger B) test)
    {
        BigInteger resBigInt = (test.A * test.B) % (BigInteger.One << 256);
        resBigInt = postprocess(resBigInt);

        T uint256a = convert(test.A);
        T uint256b = convert(test.B);
        uint256a.Multiply(uint256b, out T res);
        res.Convert(out BigInteger resUInt256);

        resUInt256.Should().Be(resBigInt);

        // Test reusing input as output
        uint256a.Multiply(uint256b, out uint256a);
        uint256a.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);

        uint256a = convert(test.A);

        uint256a.Multiply(uint256b, out uint256b);
        uint256b.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);
    }

    [TestCaseSource(typeof(TernaryOps), nameof(TernaryOps.TestCases))]
    public virtual void MultiplyMod((BigInteger A, BigInteger B, BigInteger M) test)
    {
        T uint256a = convert(test.A);
        T uint256b = convert(test.B);
        T uint256m = convert(test.M);

        if (test.M.IsZero)
        {
            Action act = () => uint256a.MultiplyMod(uint256b, uint256m, out T res);
            act.Should().Throw<DivideByZeroException>();
            return;
        }
        BigInteger resBigInt = ((test.A * test.B) % test.M) % (BigInteger.One << 256);
        resBigInt = postprocess(resBigInt);

        uint256a.MultiplyMod(uint256b, uint256m, out T res);
        res.Convert(out BigInteger resUInt256);

        resUInt256.Should().Be(resBigInt);

        // Test reusing input as output
        uint256a.MultiplyMod(uint256b, uint256m, out uint256a);
        uint256a.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);

        uint256a = convert(test.A);
        uint256a.MultiplyMod(uint256b, uint256m, out uint256b);
        uint256b.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);

        uint256b = convert(test.B);
        uint256a.MultiplyMod(uint256b, uint256m, out uint256m);
        uint256m.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);
    }

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
    public virtual void Div((BigInteger A, BigInteger B) test)
    {
        T uint256a = convert(test.A);
        T uint256b = convert(test.B);
        if (test.B.IsZero)
        {
            Action act = () => uint256a.Divide(uint256b, out T res);
            act.Should().Throw<DivideByZeroException>();
            return;
        }
        BigInteger resBigInt = (test.A / test.B) % (BigInteger.One << 256);
        resBigInt = postprocess(resBigInt);

        uint256a.Divide(uint256b, out T res);
        res.Convert(out BigInteger resUInt256);

        resUInt256.Should().Be(resBigInt);

        // Test reusing input as output
        uint256a.Divide(uint256b, out uint256a);
        uint256a.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);

        uint256a = convert(test.A);
        uint256a.Divide(uint256b, out uint256b);
        uint256b.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);
    }

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
    public virtual void Mod((BigInteger A, BigInteger B) test)
    {
        T uint256a = convert(test.A);
        T uint256b = convert(test.B);
        if (test.B.IsZero)
        {
            Action act = () => uint256a.Mod(uint256b, out T res);
            act.Should().Throw<DivideByZeroException>();
            return;
        }
        BigInteger resBigInt = (test.A % test.B) % (BigInteger.One << 256);
        resBigInt = postprocess(resBigInt);

        uint256a.Mod(uint256b, out T res);
        res.Convert(out BigInteger resUInt256);

        resUInt256.Should().Be(resBigInt);

        // Test reusing input as output
        uint256a.Mod(uint256b, out uint256a);
        uint256a.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);

        uint256a = convert(test.A);
        uint256a.Mod(uint256b, out uint256b);
        uint256b.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);
    }

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
    public virtual void And((BigInteger A, BigInteger B) test)
    {
        BigInteger resBigInt = test.A & test.B;
        resBigInt = postprocess(resBigInt);

        T uint256a = convert(test.A);
        T uint256b = convert(test.B);
        T.And(uint256a, uint256b, out T res);
        res.Convert(out BigInteger resUInt256);

        resUInt256.Should().Be(resBigInt);

        // Test reusing input as output
        T.And(uint256a, uint256b, out uint256a);
        uint256a.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);

        uint256a = convert(test.A);
        T.And(uint256a, uint256b, out uint256b);
        uint256b.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);
    }

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
    public virtual void Or((BigInteger A, BigInteger B) test)
    {
        BigInteger resBigInt = test.A | test.B;
        resBigInt = postprocess(resBigInt);

        T uint256a = convert(test.A);
        T uint256b = convert(test.B);
        T.Or(uint256a, uint256b, out T res);
        res.Convert(out BigInteger resUInt256);

        resUInt256.Should().Be(resBigInt);

        // Test reusing input as output
        T.Or(uint256a, uint256b, out uint256a);
        uint256a.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);

        uint256a = convert(test.A);
        T.Or(uint256a, uint256b, out uint256b);
        uint256b.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);
    }

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
    public virtual void Xor((BigInteger A, BigInteger B) test)
    {
        BigInteger resBigInt = test.A ^ test.B;
        resBigInt = postprocess(resBigInt);

        T uint256a = convert(test.A);
        T uint256b = convert(test.B);
        T.Xor(uint256a, uint256b, out T res);
        res.Convert(out BigInteger resUInt256);

        resUInt256.Should().Be(resBigInt);

        // Test reusing input as output
        T.Xor(uint256a, uint256b, out uint256a);
        uint256a.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);

        uint256a = convert(test.A);

        T.Xor(uint256a, uint256b, out uint256b);
        uint256b.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);
    }

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.ShiftTestCases))]
    public virtual void Exp((BigInteger A, int n) test)
    {
        BigInteger resBigInt = BigInteger.Pow(test.A, test.n);
        resBigInt %= (BigInteger.One << 256);
        resBigInt = postprocess(resBigInt);

        T uint256a = convert(test.A);

        uint256a.Exp(convertFromInt(test.n), out T res);
        res.Convert(out BigInteger resUInt256);

        resUInt256.Should().Be(resBigInt);

        // Test reusing input as output
        uint256a.Exp(convertFromInt(test.n), out uint256a);
        res.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);
    }

    [TestCaseSource(typeof(TernaryOps), nameof(TernaryOps.TestCases))]
    public virtual void ExpMod((BigInteger A, BigInteger B, BigInteger M) test)
    {
        T uint256a = convert(test.A);
        T uint256b = convert(test.B);
        T uint256m = convert(test.M);
        if (test.B < 0)
        {
            Action act = () => uint256a.ExpMod(uint256b, uint256m, out T res);
            act.Should().Throw<ArgumentException>();
            return;
        }
        if (test.M.IsZero)
        {
            Action act = () => uint256a.ExpMod(uint256b, uint256m, out T res);
            act.Should().Throw<DivideByZeroException>();
            return;
        }

        BigInteger resBigInt = BigInteger.ModPow(test.A, test.B, test.M);
        resBigInt %= (BigInteger.One << 256);
        resBigInt = postprocess(resBigInt);

        uint256a.ExpMod(uint256b, uint256m, out T res);
        res.Convert(out BigInteger resUInt256);

        resUInt256.Should().Be(resBigInt);

        // Test reusing input as output
        uint256a.ExpMod(uint256b, uint256m, out uint256a);
        uint256a.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);

        uint256a = convert(test.A);
        uint256a.ExpMod(uint256b, uint256m, out uint256b);
        uint256b.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);

        uint256b = convert(test.B);
        uint256a.ExpMod(uint256b, uint256m, out uint256m);
        uint256m.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);
    }

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.ShiftTestCases))]
    public virtual void Lsh((BigInteger A, int n) test)
    {
        if (test.n == 0)
        {
            return;
        }
        BigInteger resBigInt = test.A << test.n;
        resBigInt %= (BigInteger.One << 256);
        resBigInt = postprocess(resBigInt);

        T uint256a = convert(test.A);
        uint256a.LeftShift(test.n, out T res);
        res.Convert(out BigInteger resUInt256);

        resUInt256.Should().Be(resBigInt);

        // Test reusing input as output
        uint256a.LeftShift(test.n, out uint256a);
        uint256a.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);
    }

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.ShiftTestCases))]
    public virtual void Rsh((BigInteger A, int n) test)
    {
        if (test.n == 0)
        {
            return;
        }
        BigInteger resBigInt = test.A >> test.n;
        resBigInt %= (BigInteger.One << 256);
        resBigInt = postprocess(resBigInt);

        T uint256a = convert(test.A);
        uint256a.RightShift(test.n, out T res);
        res.Convert(out BigInteger resUInt256);

        resUInt256.Should().Be(resBigInt);

        // Test reusing input as output
        uint256a.RightShift(test.n, out uint256a);
        uint256a.Convert(out resUInt256);

        resUInt256.Should().Be(resBigInt);
    }

    [TestCaseSource(typeof(UnaryOps), nameof(UnaryOps.TestCases))]
    public virtual void ToBigIntegerAndBack(BigInteger test)
    {
        T uint256 = convert(test);
        uint256.Convert(out BigInteger res);
        res.Should().Be(test);
    }

    [TestCaseSource(typeof(UnaryOps), nameof(UnaryOps.TestCases))]
    public virtual void Not(BigInteger test)
    {
        BigInteger resBigInt = typeof(T) == typeof(UInt256)
            ? WrapUInt256(~test)
            : WrapInt256(~test);

        T x = convert(test);
        T.Not(x, out T res);
        res.Convert(out BigInteger resT);

        resT.Should().Be(resBigInt);

        // Test reusing input as output
        T.Not(x, out x);
        x.Convert(out resT);
        resT.Should().Be(resBigInt);
    }

    [TestCaseSource(typeof(UnaryOps), nameof(UnaryOps.TestCases))]
    public virtual void ToString(BigInteger test)
    {
        T uint256 = convert(test);
        uint256.ToString().Should().Be(test.ToString());
    }
}

[Parallelizable(ParallelScope.All)]
public class UInt256Tests : UInt256TestsTemplate<UInt256>
{
    public UInt256Tests() : base((BigInteger x) => (UInt256)x, (int x) => (UInt256)x, x => x, TestNumbers.UInt256Max) { }

    // The (UInt256)BigInteger cast is allocation-free: it writes the value into a stackalloc
    // span via BigInteger.TryWriteBytes instead of allocating intermediate byte[] arrays.
    // These tests pin both the numeric result (right-aligned big-endian, all magnitudes) and
    // the preserved overflow-throws-for-values-that-do-not-fit-in-256-bits behavior.
    public static BigInteger[] CastRoundTripValues { get; } =
    [
        BigInteger.Zero,
        BigInteger.One,
        new BigInteger(ulong.MaxValue),
        (BigInteger.One << 128) - 1,
        (BigInteger.One << 200) - 1,
        BigInteger.One << 255,          // top bit set: BCL would grow to 33 bytes unsigned without the unsigned flag
        (BigInteger.One << 255) - 1,    // unsigned-encoding boundary just below the top bit
        TestNumbers.UInt256Max,
    ];

    [TestCaseSource(nameof(CastRoundTripValues))]
    public void Cast_From_BigInteger_RoundTrips(BigInteger value)
    {
        UInt256 cast = (UInt256)value;
        cast.Convert(out BigInteger actual);
        actual.Should().Be(value);
    }

    [TestCase(256)]   // 2^256: smallest 33-byte value
    [TestCase(257)]   // 2^257
    public void Cast_From_BigInteger_Throws_When_Over_256_Bits(int shift)
    {
        Action exact = () => { _ = (UInt256)(BigInteger.One << shift); };
        exact.Should().Throw<ArgumentOutOfRangeException>();

        Action plusOne = () => { _ = (UInt256)((BigInteger.One << shift) + 1); };
        plusOne.Should().Throw<ArgumentOutOfRangeException>();
    }

    [Test]
    public void Cast_From_Negative_BigInteger_Throws()
    {
        // BigInteger.TryWriteBytes(isUnsigned: true) rejects negative values, matching the
        // legacy ToByteArray(true, true) path which also threw OverflowException.
        Action act = () => { _ = (UInt256)BigInteger.MinusOne; };
        act.Should().Throw<OverflowException>();
    }

    [TestCaseSource(nameof(CastRoundTripValues))]
    public void ToBytes32_Produces_RightAligned_BigEndian(BigInteger value)
    {
        Span<byte> bytes = stackalloc byte[32];
        value.ToBytes32(bytes, true);

        // The bytes must reconstruct the original value as an unsigned big-endian 256-bit word.
        BigInteger reconstructed = new(bytes, isUnsigned: true, isBigEndian: true);
        reconstructed.Should().Be(value);
    }

    // PaddedBytes returns the big-endian, right-aligned, left-zero-padded representation of the
    // value in a byte[n]: when n > 32 the leading bytes are zero, when n < 32 the most-significant
    // bytes are truncated. These cases pin that behavior across the boundary, exercising the
    // all-ones top limb (MaxValue), all-zeros (Zero), and a mixed mid-sized value.
    public static BigInteger[] PaddedBytesValues { get; } =
    [
        BigInteger.Zero,
        BigInteger.Parse("123456789012345678901234567890"),
        TestNumbers.UInt256Max,
    ];

    [Test]
    public void PaddedBytes_Matches_BigEndian_RightAligned(
        [ValueSource(nameof(PaddedBytesValues))] BigInteger value,
        [Values(0, 1, 8, 20, 31, 32, 33, 64)] int n)
    {
        UInt256 v = (UInt256)value;

        byte[] padded = v.PaddedBytes(n);
        padded.Length.Should().Be(n);

        // Expected: the low min(32, n) bytes of the 32-byte big-endian form, right-aligned, with
        // the remaining leading bytes zero.
        byte[] full = v.ToBigEndian(); // 32-byte big-endian
        int copy = Math.Min(32, n);
        byte[] expected = new byte[n];
        full.AsSpan(32 - copy, copy).CopyTo(expected.AsSpan(n - copy, copy));

        padded.Should().Equal(expected);
    }

    [Test]
    public void PaddedBytes_Into_Span_ZeroesLeadingBytes_When_Longer_Than_Word()
    {
        UInt256 v = (UInt256)0x0102030405060708UL;

        // n > 32: the whole span is written. The leading bytes beyond the 32-byte word are zeroed
        // (parity with the array overload), and the prior buffer contents are overwritten.
        Span<byte> target = stackalloc byte[40];
        target.Fill(0xAA);

        v.PaddedBytes(target);

        for (int i = 0; i < 32; i++) target[i].Should().Be(0x00);
        target[32].Should().Be(0x01);
        target[39].Should().Be(0x08);
    }

    [Test]
    public void PaddedBytes_Into_Span_Truncates_And_RightAligns_When_Shorter_Than_Word()
    {
        UInt256 v = (UInt256)0x0102030405060708UL;

        // n < 32: only the low n bytes are emitted, right-aligned; the high bytes of the value are
        // truncated and the whole (pre-filled) buffer is overwritten.
        Span<byte> target = stackalloc byte[6];
        target.Fill(0xAA);

        v.PaddedBytes(target);

        // Low 6 bytes of the big-endian value: 03 04 05 06 07 08 (the 01 02 are truncated).
        byte[] expected = { 0x03, 0x04, 0x05, 0x06, 0x07, 0x08 };
        target.ToArray().Should().Equal(expected);
    }

    [Test]
    public virtual void Zero_is_min_value()
    {
        convert(1).ZeroValue.Should().Be(UInt256.MinValue);
    }

    [Test]
    public virtual void Zero_is_zero()
    {
        convert(1).ZeroValue.Should().Be(convert(BigInteger.Zero));
    }

    [Test]
    public virtual void Is_zero()
    {
        convert(1).ZeroValue.IsZero.Should().BeTrue();
        UInt256.One.IsZero.Should().BeFalse();
    }

    [Test]
    public virtual void One_is_one()
    {
        convert(1).OneValue.Should().Be(convert(BigInteger.One));
    }

    [Test]
    public virtual void Is_one()
    {
        convert(1).OneValue.IsOne.Should().BeTrue();
        convert(1).ZeroValue.IsOne.Should().BeFalse();
    }

    [Test]
    public virtual void Max_value_is_correct()
    {
        convert(1).MaximalValue.Should().Be(convert(maxValue));
    }

    [Test]
    public virtual void ToBigEndian_And_Back()
    {
        byte[] bidEndian = convert(1000000000000000000).ToBigEndian();
        new UInt256(bidEndian, true).Should().Be(convert(1000000000000000000));
    }

    [Test]
    public virtual void ToLittleEndian_And_Back()
    {
        byte[] bidEndian = convert(1000000000000000000).ToLittleEndian();
        new UInt256(bidEndian).Should().Be(convert(1000000000000000000));
    }

    [Test]
    public virtual void Check_For_Correct_Big_And_Little_Endian()
    {
        byte[] bigEndianRepresentation =
        {
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 224, 182, 179, 167, 100,
            0, 0
        };
        convert(1000000000000000000).ToBigEndian().Should().BeEquivalentTo(bigEndianRepresentation);

        byte[] littleEndianRepresentation =
        {
            0, 0, 100, 167, 179, 182, 224, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
        };
        convert(1000000000000000000).ToLittleEndian().Should().BeEquivalentTo(littleEndianRepresentation);
    }

    [TestCaseSource(typeof(Convertibles), nameof(Convertibles.TestCases))]
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
        if (!valueString.StartsWith('-'))
        {
            try
            {
                UInt256 item = (UInt256)BigInteger.Parse(valueString);
                string expected = expectedString ?? Expected(valueString);
                string convertedValue = Expected(((IFormattable)System.Convert.ChangeType(item, type)).ToString("0.#", null));
                convertedValue.Should().BeEquivalentTo(expected);
            }
            catch (Exception e) when (e.GetType() == expectedException) { }
        }
    }
    [Test]
    public virtual void ParseLongNumber()
    {
        string hexValueWith66Zeroes = "0x" + new string('0', 66);
        BigInteger bigIntWith66Zeroes = BigInteger.Parse(hexValueWith66Zeroes.Substring(2), NumberStyles.HexNumber);
        var UintParsedValue = UInt256.Parse(hexValueWith66Zeroes);
        Assert.That((UInt256)bigIntWith66Zeroes, Is.EqualTo(UintParsedValue));
    }

    public static TestCaseData[] ParseTestCases { get; } =
    [
        new TestCaseData("0", BigInteger.Zero),
        new TestCaseData("+1", BigInteger.One),
        new TestCaseData(" 18446744073709551615 ", new BigInteger(ulong.MaxValue)),
        new TestCaseData("0x0", BigInteger.Zero),
        new TestCaseData("0x" + new string('0', 66), BigInteger.Zero),
        new TestCaseData("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff", TestNumbers.UInt256Max),
        new TestCaseData("115792089237316195423570985008687907853269984665640564039457584007913129639935", TestNumbers.UInt256Max),
    ];

    [TestCaseSource(nameof(ParseTestCases))]
    public void TryParse_ReturnsExpectedValue(string value, BigInteger expected)
    {
        UInt256.TryParse(value, out UInt256 parsed).Should().BeTrue();

        parsed.Convert(out BigInteger actual);
        actual.Should().Be(expected);
    }

    [TestCase("")]
    [TestCase("0x")]
    [TestCase("-1")]
    [TestCase("0x1g")]
    [TestCase("115792089237316195423570985008687907853269984665640564039457584007913129639936")]
    public void TryParse_ReturnsFalseForInvalidValues(string value)
    {
        UInt256.TryParse(value, out UInt256 parsed).Should().BeFalse();
        parsed.Should().Be(UInt256.Zero);
    }

    // The direct (non-BigInteger) parsing path introduced on this branch changed behavior for a
    // few inputs relative to the previous BigInteger round-trip. These tests pin the new behavior
    // so the intent is explicit and any future change is deliberate. See the PR open questions.

    // "0x0" is a valid zero, but a bare "0x" prefix with no digits is rejected. The old
    // BigInteger path returned 0 for "0x"; the new path requires at least one digit.
    [TestCase("0x0", true, 0u)]
    [TestCase("0x00", true, 0u)]
    [TestCase("0x", false, 0u)]
    public void TryParse_BarePrefixVsZero(string value, bool expectedSuccess, uint expectedValue)
    {
        UInt256.TryParse(value, out UInt256 parsed).Should().Be(expectedSuccess);
        if (expectedSuccess)
        {
            parsed.Should().Be((UInt256)expectedValue);
        }
    }

    // Whitespace immediately after the "0x" prefix is now tolerated (trimmed), whereas the old
    // BigInteger path rejected it. Internal whitespace between digits is still rejected.
    [TestCase("0x ff", true, 255u)]
    [TestCase("0xff ", true, 255u)]
    [TestCase("0x f f", false, 0u)]
    public void TryParse_HexWhitespaceHandling(string value, bool expectedSuccess, uint expectedValue)
    {
        UInt256.TryParse(value, out UInt256 parsed).Should().Be(expectedSuccess);
        if (expectedSuccess)
        {
            parsed.Should().Be((UInt256)expectedValue);
        }
    }

    [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
    public void ComparisonOperators((BigInteger A, BigInteger B) test)
    {
        UInt256 uint256a = convert(test.A);
        UInt256 uint256b = convert(test.B);

        (uint256a < uint256b).Should().Be(test.A < test.B);
        (uint256a <= uint256b).Should().Be(test.A <= test.B);
        (uint256a > uint256b).Should().Be(test.A > test.B);
        (uint256a >= uint256b).Should().Be(test.A >= test.B);
        (uint256a == uint256b).Should().Be(test.A == test.B);

        // Test overloads ulong, long, uint, int
        if (test.A <= ulong.MaxValue)
        {
            ulong a = (ulong)test.A;

            (a < uint256b).Should().Be(a < test.B);
            (a <= uint256b).Should().Be(a <= test.B);
            (a > uint256b).Should().Be(a > test.B);
            (a >= uint256b).Should().Be(a >= test.B);
            (a == uint256b).Should().Be(a == test.B);
        }

        if (test.A <= long.MaxValue)
        {
            long a = (long)test.A;

            (a < uint256b).Should().Be(a < test.B);
            (a <= uint256b).Should().Be(a <= test.B);
            (a > uint256b).Should().Be(a > test.B);
            (a >= uint256b).Should().Be(a >= test.B);
            (a == uint256b).Should().Be(a == test.B);
        }

        if (test.A <= uint.MaxValue)
        {
            uint a = (uint)test.A;

            (a < uint256b).Should().Be(a < test.B);
            (a <= uint256b).Should().Be(a <= test.B);
            (a > uint256b).Should().Be(a > test.B);
            (a >= uint256b).Should().Be(a >= test.B);
            (a == uint256b).Should().Be(a == test.B);
        }

        if (test.A <= int.MaxValue)
        {
            int a = (int)test.A;

            (a < uint256b).Should().Be(a < test.B);
            (a <= uint256b).Should().Be(a <= test.B);
            (a > uint256b).Should().Be(a > test.B);
            (a >= uint256b).Should().Be(a >= test.B);
            (a == uint256b).Should().Be(a == test.B);
        }

        if (test.B <= ulong.MaxValue)
        {
            ulong b = (ulong)test.B;

            (uint256a < b).Should().Be(test.A < b);
            (uint256a <= b).Should().Be(test.A <= b);
            (uint256a > b).Should().Be(test.A > b);
            (uint256a >= b).Should().Be(test.A >= b);
            (uint256a == b).Should().Be(test.A == b);
        }

        if (test.B <= long.MaxValue)
        {
            long b = (long)test.B;

            (uint256a < b).Should().Be(test.A < b);
            (uint256a <= b).Should().Be(test.A <= b);
            (uint256a > b).Should().Be(test.A > b);
            (uint256a >= b).Should().Be(test.A >= b);
            (uint256a == b).Should().Be(test.A == b);
        }

        if (test.B <= uint.MaxValue)
        {
            uint b = (uint)test.B;

            (uint256a < b).Should().Be(test.A < b);
            (uint256a <= b).Should().Be(test.A <= b);
            (uint256a > b).Should().Be(test.A > b);
            (uint256a >= b).Should().Be(test.A >= b);
            (uint256a == b).Should().Be(test.A == b);
        }

        if (test.B <= int.MaxValue)
        {
            int b = (int)test.B;

            (uint256a < b).Should().Be(test.A < b);
            (uint256a <= b).Should().Be(test.A <= b);
            (uint256a > b).Should().Be(test.A > b);
            (uint256a >= b).Should().Be(test.A >= b);
            (uint256a == b).Should().Be(test.A == b);
        }
    }

    [NonParallelizable]
    [TestCase(false)]
    [TestCase(true)]
    public void Shoud_respect_appcontext_switch(bool useHashCodeRandomizer)
    {
        AppContext.SetSwitch("Nethermind.Int256.UseHashCodeRandomizer", useHashCodeRandomizer);

        Assert.That(UInt256.UseHashCodeRandomizer, Is.EqualTo(useHashCodeRandomizer));
    }
}
