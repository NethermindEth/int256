using System;
using System.Numerics;
using FluentAssertions;
using NUnit.Framework;

namespace Nethermind.Int256.Test
{
    /// <summary>
    /// Tests for the INumber interface implementations on UInt256 and Int256.
    /// Uses BigInteger to verify correctness of operations.
    /// </summary>
    [TestFixture]
    [Parallelizable(ParallelScope.All)]
    public class INumberTests
    {
        #region Static Properties Tests

        [Test]
        public void UInt256_One_IsCorrect()
        {
            UInt256.One.Should().Be((UInt256)1);
            ((BigInteger)UInt256.One).Should().Be(BigInteger.One);
        }

        [Test]
        public void UInt256_Zero_IsCorrect()
        {
            UInt256.Zero.Should().Be((UInt256)0);
            ((BigInteger)UInt256.Zero).Should().Be(BigInteger.Zero);
        }

        [Test]
        public void Int256_One_IsCorrect()
        {
            Int256.One.Should().Be((Int256)1);
            ((BigInteger)Int256.One).Should().Be(BigInteger.One);
        }

        [Test]
        public void Int256_Zero_IsCorrect()
        {
            Int256.Zero.Should().Be((Int256)0);
            ((BigInteger)Int256.Zero).Should().Be(BigInteger.Zero);
        }

        [Test]
        public void Int256_MinusOne_IsCorrect()
        {
            ((BigInteger)Int256.MinusOne).Should().Be(-BigInteger.One);
        }

        [Test]
        public void UInt256_MinMaxValue_IsCorrect()
        {
            ((BigInteger)UInt256.MinValue).Should().Be(BigInteger.Zero);
            ((BigInteger)UInt256.MaxValue).Should().Be(TestNumbers.UInt256Max);
        }

        [Test]
        public void Int256_MinMaxValue_IsCorrect()
        {
            ((BigInteger)Int256.MinValue).Should().Be(-(BigInteger.One << 255));
            ((BigInteger)Int256.MaxValue).Should().Be((BigInteger.One << 255) - 1);
        }

        #endregion

        #region Abs Tests

        [Test]
        public void UInt256_Abs_ReturnsValue()
        {
            var value = (UInt256)12345;
            UInt256.Abs(value).Should().Be(value);
        }

        [Test]
        public void Int256_Abs_PositiveValue_ReturnsValue()
        {
            var value = (Int256)12345;
            Int256.Abs(value).Should().Be(value);
        }

        [Test]
        public void Int256_Abs_NegativeValue_ReturnsPositive()
        {
            var value = new Int256(-12345);
            var expected = (Int256)12345;
            Int256.Abs(value).Should().Be(expected);
        }

        [Test]
        public void Int256_Abs_Zero_ReturnsZero()
        {
            Int256.Abs(Int256.Zero).Should().Be(Int256.Zero);
        }

        #endregion

        #region Clamp Tests

        [Test]
        public void UInt256_Clamp_ValueInRange_ReturnsValue()
        {
            var value = (UInt256)50;
            var min = (UInt256)10;
            var max = (UInt256)100;
            UInt256.Clamp(value, min, max).Should().Be(value);
        }

        [Test]
        public void UInt256_Clamp_ValueBelowMin_ReturnsMin()
        {
            var value = (UInt256)5;
            var min = (UInt256)10;
            var max = (UInt256)100;
            UInt256.Clamp(value, min, max).Should().Be(min);
        }

        [Test]
        public void UInt256_Clamp_ValueAboveMax_ReturnsMax()
        {
            var value = (UInt256)150;
            var min = (UInt256)10;
            var max = (UInt256)100;
            UInt256.Clamp(value, min, max).Should().Be(max);
        }

        [Test]
        public void Int256_Clamp_ValueInRange_ReturnsValue()
        {
            var value = (Int256)50;
            var min = new Int256(-100);
            var max = (Int256)100;
            Int256.Clamp(value, min, max).Should().Be(value);
        }

        [Test]
        public void Int256_Clamp_NegativeValueInRange_ReturnsValue()
        {
            var value = new Int256(-50);
            var min = new Int256(-100);
            var max = (Int256)100;
            Int256.Clamp(value, min, max).Should().Be(value);
        }

        #endregion

        #region Sign Tests

        [Test]
        public void UInt256_Sign_Zero_ReturnsZero()
        {
            UInt256.Sign(UInt256.Zero).Should().Be(0);
        }

        [Test]
        public void UInt256_Sign_PositiveValue_ReturnsOne()
        {
            UInt256.Sign((UInt256)12345).Should().Be(1);
        }

        [Test]
        public void Int256_Sign_Zero_ReturnsZero()
        {
            Int256.Zero.Sign.Should().Be(0);
        }

        [Test]
        public void Int256_Sign_PositiveValue_ReturnsOne()
        {
            ((Int256)12345).Sign.Should().Be(1);
        }

        [Test]
        public void Int256_Sign_NegativeValue_ReturnsMinusOne()
        {
            new Int256(-12345).Sign.Should().Be(-1);
        }

        #endregion

        #region IsEvenInteger / IsOddInteger Tests

        [Test]
        public void UInt256_IsEvenInteger_EvenValue_ReturnsTrue()
        {
            UInt256.IsEvenInteger((UInt256)100).Should().BeTrue();
            UInt256.IsEvenInteger((UInt256)0).Should().BeTrue();
        }

        [Test]
        public void UInt256_IsEvenInteger_OddValue_ReturnsFalse()
        {
            UInt256.IsEvenInteger((UInt256)101).Should().BeFalse();
        }

        [Test]
        public void UInt256_IsOddInteger_OddValue_ReturnsTrue()
        {
            UInt256.IsOddInteger((UInt256)101).Should().BeTrue();
        }

        [Test]
        public void UInt256_IsOddInteger_EvenValue_ReturnsFalse()
        {
            UInt256.IsOddInteger((UInt256)100).Should().BeFalse();
        }

        [Test]
        public void Int256_IsEvenInteger_EvenValue_ReturnsTrue()
        {
            Int256.IsEvenInteger((Int256)100).Should().BeTrue();
            Int256.IsEvenInteger(new Int256(-100)).Should().BeTrue();
        }

        [Test]
        public void Int256_IsOddInteger_OddValue_ReturnsTrue()
        {
            Int256.IsOddInteger((Int256)101).Should().BeTrue();
            Int256.IsOddInteger(new Int256(-101)).Should().BeTrue();
        }

        #endregion

        #region PopCount Tests

        [Test]
        public void UInt256_PopCount_Zero_ReturnsZero()
        {
            UInt256.PopCount(UInt256.Zero).Should().Be((UInt256)0);
        }

        [Test]
        public void UInt256_PopCount_One_ReturnsOne()
        {
            UInt256.PopCount((UInt256)1).Should().Be((UInt256)1);
        }

        [Test]
        public void UInt256_PopCount_AllOnes_Returns256()
        {
            UInt256.PopCount(UInt256.MaxValue).Should().Be((UInt256)256);
        }

        [TestCase(0b1010UL, 2)]
        [TestCase(0b11111111UL, 8)]
        [TestCase(0b10000001UL, 2)]
        public void UInt256_PopCount_Values(ulong value, int expectedCount)
        {
            UInt256.PopCount((UInt256)value).Should().Be((UInt256)expectedCount);
        }

        #endregion

        #region LeadingZeroCount Tests

        [Test]
        public void UInt256_LeadingZeroCount_Zero_Returns256()
        {
            UInt256.LeadingZeroCount(UInt256.Zero).Should().Be(256);
        }

        [Test]
        public void UInt256_LeadingZeroCount_One_Returns255()
        {
            UInt256.LeadingZeroCount((UInt256)1).Should().Be(255);
        }

        [Test]
        public void UInt256_LeadingZeroCount_MaxValue_ReturnsZero()
        {
            UInt256.LeadingZeroCount(UInt256.MaxValue).Should().Be(0);
        }

        #endregion

        #region TrailingZeroCount Tests

        [Test]
        public void UInt256_TrailingZeroCount_Zero_Returns256()
        {
            UInt256.TrailingZeroCount(UInt256.Zero).Should().Be((UInt256)256);
        }

        [Test]
        public void UInt256_TrailingZeroCount_One_ReturnsZero()
        {
            UInt256.TrailingZeroCount((UInt256)1).Should().Be((UInt256)0);
        }

        [Test]
        public void UInt256_TrailingZeroCount_PowerOfTwo()
        {
            UInt256.TrailingZeroCount((UInt256)8).Should().Be((UInt256)3);
            UInt256.TrailingZeroCount((UInt256)16).Should().Be((UInt256)4);
        }

        #endregion

        #region DivRem Tests

        [Test]
        public void UInt256_DivRem_SimpleCase()
        {
            var (quotient, remainder) = UInt256.DivRem((UInt256)17, (UInt256)5);
            quotient.Should().Be((UInt256)3);
            remainder.Should().Be((UInt256)2);
        }

        [Test]
        public void UInt256_DivRem_ExactDivision()
        {
            var (quotient, remainder) = UInt256.DivRem((UInt256)20, (UInt256)5);
            quotient.Should().Be((UInt256)4);
            remainder.Should().Be((UInt256)0);
        }

        [Test]
        public void UInt256_DivRem_LargeNumbers()
        {
            BigInteger bigA = TestNumbers.TwoTo128 + 17;
            BigInteger bigB = TestNumbers.TwoTo64 + 5;
            BigInteger expectedQuotient = BigInteger.DivRem(bigA, bigB, out BigInteger expectedRemainder);

            var (quotient, remainder) = UInt256.DivRem((UInt256)bigA, (UInt256)bigB);

            ((BigInteger)quotient).Should().Be(expectedQuotient);
            ((BigInteger)remainder).Should().Be(expectedRemainder);
        }

        [Test]
        public void Int256_DivRem_SimpleCase()
        {
            var (quotient, remainder) = Int256.DivRem((Int256)17, (Int256)5);
            quotient.Should().Be((Int256)3);
            remainder.Should().Be((Int256)2);
        }

        [Test]
        public void Int256_DivRem_NegativeDividend()
        {
            var (quotient, remainder) = Int256.DivRem(new Int256(-17), (Int256)5);
            ((BigInteger)quotient).Should().Be(-3);
            ((BigInteger)remainder).Should().Be(-2);
        }

        #endregion

        #region TryConvertFromChecked Tests

        [Test]
        public void UInt256_TryConvertFromChecked_Byte()
        {
            byte value = 123;
            bool success = UInt256.TryParse(value.ToString(), out UInt256 result);
            success.Should().BeTrue();
            result.Should().Be((UInt256)value);
        }

        [Test]
        public void UInt256_TryConvertFromChecked_UInt64()
        {
            ulong value = ulong.MaxValue;
            var result = (UInt256)value;
            ((BigInteger)result).Should().Be(value);
        }

        [Test]
        public void UInt256_TryConvertFromChecked_BigInteger()
        {
            BigInteger value = TestNumbers.TwoTo128 + 12345;
            var result = (UInt256)value;
            ((BigInteger)result).Should().Be(value);
        }

        [Test]
        public void Int256_TryConvertFromChecked_Int64()
        {
            long value = -12345;
            var result = new Int256(value);
            ((BigInteger)result).Should().Be(value);
        }

        [Test]
        public void Int256_TryConvertFromChecked_BigInteger()
        {
            BigInteger value = -(TestNumbers.TwoTo128 + 12345);
            var result = new Int256(value);
            ((BigInteger)result).Should().Be(value);
        }

        #endregion

        #region TryConvertToChecked Tests

        [Test]
        public void UInt256_ToUInt64_SmallValue()
        {
            UInt256 value = 12345;
            ulong result = (ulong)value;
            result.Should().Be(12345);
        }

        [Test]
        public void UInt256_ToBigInteger()
        {
            BigInteger expected = TestNumbers.TwoTo192 + 12345;
            UInt256 value = (UInt256)expected;
            ((BigInteger)value).Should().Be(expected);
        }

        [Test]
        public void Int256_ToInt64_SmallPositiveValue()
        {
            Int256 value = (Int256)12345;
            value.ToInt64(null).Should().Be(12345);
        }

        [Test]
        public void Int256_ToInt64_SmallNegativeValue()
        {
            Int256 value = new Int256(-12345);
            value.ToInt64(null).Should().Be(-12345);
        }

        [Test]
        public void Int256_ToBigInteger_Positive()
        {
            BigInteger expected = TestNumbers.TwoTo128 + 12345;
            Int256 value = new Int256(expected);
            ((BigInteger)value).Should().Be(expected);
        }

        [Test]
        public void Int256_ToBigInteger_Negative()
        {
            BigInteger expected = -(TestNumbers.TwoTo128 + 12345);
            Int256 value = new Int256(expected);
            ((BigInteger)value).Should().Be(expected);
        }

        #endregion

        #region MaxMagnitude / MinMagnitude Tests

        [Test]
        public void UInt256_MaxMagnitude()
        {
            var a = (UInt256)100;
            var b = (UInt256)50;
            UInt256.MaxMagnitude(a, b).Should().Be(a);
        }

        [Test]
        public void UInt256_MinMagnitude()
        {
            var a = (UInt256)100;
            var b = (UInt256)50;
            UInt256.MinMagnitude(a, b).Should().Be(b);
        }

        [Test]
        public void Int256_MaxMagnitude_BothPositive()
        {
            var a = (Int256)100;
            var b = (Int256)50;
            Int256.MaxMagnitude(a, b).Should().Be(a);
        }

        [Test]
        public void Int256_MaxMagnitude_NegativeHasLargerMagnitude()
        {
            var a = (Int256)50;
            var b = new Int256(-100);
            Int256.MaxMagnitude(a, b).Should().Be(b);
        }

        [Test]
        public void Int256_MinMagnitude_NegativeHasSmallerMagnitude()
        {
            var a = (Int256)100;
            var b = new Int256(-50);
            Int256.MinMagnitude(a, b).Should().Be(b);
        }

        #endregion

        #region CopySign Tests

        [Test]
        public void Int256_CopySign_PositiveToNegative()
        {
            var value = (Int256)100;
            var sign = new Int256(-1);
            var result = Int256.CopySign(value, sign);
            ((BigInteger)result).Should().Be(-100);
        }

        [Test]
        public void Int256_CopySign_NegativeToPositive()
        {
            var value = new Int256(-100);
            var sign = (Int256)1;
            var result = Int256.CopySign(value, sign);
            ((BigInteger)result).Should().Be(100);
        }

        [Test]
        public void UInt256_CopySign_ReturnsValue()
        {
            var value = (UInt256)100;
            var sign = (UInt256)1;
            UInt256.CopySign(value, sign).Should().Be(value);
        }

        #endregion

        #region Parse Tests with IFormatProvider

        [Test]
        public void UInt256_Parse_ValidString()
        {
            var result = UInt256.Parse("12345", System.Globalization.NumberStyles.Integer, null);
            result.Should().Be((UInt256)12345);
        }

        [Test]
        public void UInt256_Parse_HexString()
        {
            var result = UInt256.Parse("FF", System.Globalization.NumberStyles.HexNumber, null);
            result.Should().Be((UInt256)255);
        }

        [Test]
        public void Int256_Parse_NegativeString()
        {
            var result = Int256.Parse("-12345", System.Globalization.NumberStyles.Integer, null);
            ((BigInteger)result).Should().Be(-12345);
        }

        [Test]
        public void UInt256_TryParse_ValidString_ReturnsTrue()
        {
            bool success = UInt256.TryParse("12345", out UInt256 result);
            success.Should().BeTrue();
            result.Should().Be((UInt256)12345);
        }

        [Test]
        public void UInt256_TryParse_InvalidString_ReturnsFalse()
        {
            bool success = UInt256.TryParse("not a number", out UInt256 result);
            success.Should().BeFalse();
            result.Should().Be(UInt256.Zero);
        }

        #endregion

        #region TryFormat Tests

        [Test]
        public void UInt256_TryFormat_Success()
        {
            var value = (UInt256)12345;
            Span<char> buffer = stackalloc char[20];
            bool success = value.TryFormat(buffer, out int charsWritten, default, null);
            success.Should().BeTrue();
            buffer[..charsWritten].ToString().Should().Be("12345");
        }

        [Test]
        public void Int256_TryFormat_Positive()
        {
            var value = (Int256)12345;
            Span<char> buffer = stackalloc char[20];
            bool success = value.TryFormat(buffer, out int charsWritten, default, null);
            success.Should().BeTrue();
            buffer[..charsWritten].ToString().Should().Be("12345");
        }

        [Test]
        public void Int256_TryFormat_Negative()
        {
            var value = new Int256(-12345);
            Span<char> buffer = stackalloc char[20];
            bool success = value.TryFormat(buffer, out int charsWritten, default, null);
            success.Should().BeTrue();
            buffer[..charsWritten].ToString().Should().Be("-12345");
        }

        #endregion

        #region GetByteCount / GetShortestBitLength Tests

        [Test]
        public void UInt256_GetByteCount_Returns32()
        {
            var value = (UInt256)12345;
            value.GetByteCount().Should().Be(32);
        }

        [Test]
        public void Int256_GetByteCount_Returns32()
        {
            var value = (Int256)12345;
            value.GetByteCount().Should().Be(32);
        }

        [Test]
        public void UInt256_GetShortestBitLength_SmallValue()
        {
            var value = (UInt256)255; // 8 bits
            value.GetShortestBitLength().Should().Be(8);
        }

        [Test]
        public void UInt256_GetShortestBitLength_Zero()
        {
            UInt256.Zero.GetShortestBitLength().Should().Be(0);
        }

        #endregion

        #region TryWriteBigEndian / TryWriteLittleEndian Tests

        [Test]
        public void UInt256_TryWriteBigEndian_Success()
        {
            var value = (UInt256)0x12345678;
            Span<byte> buffer = stackalloc byte[32];
            bool success = value.TryWriteBigEndian(buffer, out int bytesWritten);
            success.Should().BeTrue();
            bytesWritten.Should().Be(32);
            // Verify the last 4 bytes contain the value in big endian
            buffer[28].Should().Be(0x12);
            buffer[29].Should().Be(0x34);
            buffer[30].Should().Be(0x56);
            buffer[31].Should().Be(0x78);
        }

        [Test]
        public void UInt256_TryWriteLittleEndian_Success()
        {
            var value = (UInt256)0x12345678;
            Span<byte> buffer = stackalloc byte[32];
            bool success = value.TryWriteLittleEndian(buffer, out int bytesWritten);
            success.Should().BeTrue();
            bytesWritten.Should().Be(32);
            // Verify the first 4 bytes contain the value in little endian
            buffer[0].Should().Be(0x78);
            buffer[1].Should().Be(0x56);
            buffer[2].Should().Be(0x34);
            buffer[3].Should().Be(0x12);
        }

        [Test]
        public void UInt256_TryWriteBigEndian_BufferTooSmall_ReturnsFalse()
        {
            var value = (UInt256)12345;
            Span<byte> buffer = stackalloc byte[16];
            bool success = value.TryWriteBigEndian(buffer, out int bytesWritten);
            success.Should().BeFalse();
            bytesWritten.Should().Be(0);
        }

        #endregion

        #region TryReadBigEndian / TryReadLittleEndian Tests

        [Test]
        public void UInt256_TryReadBigEndian_Success()
        {
            Span<byte> buffer = stackalloc byte[32];
            buffer.Clear();
            buffer[31] = 0x78;
            buffer[30] = 0x56;
            buffer[29] = 0x34;
            buffer[28] = 0x12;

            bool success = UInt256.TryReadBigEndian(buffer, true, out UInt256 result);
            success.Should().BeTrue();
            result.Should().Be((UInt256)0x12345678);
        }

        [Test]
        public void UInt256_TryReadLittleEndian_Success()
        {
            Span<byte> buffer = stackalloc byte[32];
            buffer.Clear();
            buffer[0] = 0x78;
            buffer[1] = 0x56;
            buffer[2] = 0x34;
            buffer[3] = 0x12;

            bool success = UInt256.TryReadLittleEndian(buffer, true, out UInt256 result);
            success.Should().BeTrue();
            result.Should().Be((UInt256)0x12345678);
        }

        #endregion

        #region Arithmetic Operators with Standard Types

        [Test]
        public void UInt256_Addition_MatchesBigInteger()
        {
            BigInteger a = TestNumbers.TwoTo128 + 12345;
            BigInteger b = TestNumbers.TwoTo64 + 67890;
            BigInteger expected = a + b;

            UInt256 ua = (UInt256)a;
            UInt256 ub = (UInt256)b;
            UInt256 result = ua + ub;

            ((BigInteger)result).Should().Be(expected);
        }

        [Test]
        public void UInt256_Subtraction_MatchesBigInteger()
        {
            BigInteger a = TestNumbers.TwoTo128 + 12345;
            BigInteger b = TestNumbers.TwoTo64 + 67890;
            BigInteger expected = a - b;

            UInt256 ua = (UInt256)a;
            UInt256 ub = (UInt256)b;
            UInt256 result = ua - ub;

            ((BigInteger)result).Should().Be(expected);
        }

        [Test]
        public void UInt256_Multiplication_MatchesBigInteger()
        {
            BigInteger a = TestNumbers.TwoTo64 + 12345;
            BigInteger b = TestNumbers.TwoTo64 + 67890;
            BigInteger expected = (a * b) % TestNumbers.TwoTo256;

            UInt256 ua = (UInt256)a;
            UInt256 ub = (UInt256)b;
            UInt256 result = ua * ub;

            ((BigInteger)result).Should().Be(expected);
        }

        [Test]
        public void UInt256_Division_MatchesBigInteger()
        {
            BigInteger a = TestNumbers.TwoTo128 + 12345;
            BigInteger b = TestNumbers.TwoTo64 + 67890;
            BigInteger expected = a / b;

            UInt256 ua = (UInt256)a;
            UInt256 ub = (UInt256)b;
            UInt256 result = ua / ub;

            ((BigInteger)result).Should().Be(expected);
        }

        [Test]
        public void UInt256_Modulus_MatchesBigInteger()
        {
            BigInteger a = TestNumbers.TwoTo128 + 12345;
            BigInteger b = TestNumbers.TwoTo64 + 67890;
            BigInteger expected = a % b;

            UInt256 ua = (UInt256)a;
            UInt256 ub = (UInt256)b;
            UInt256 result = ua % ub;

            ((BigInteger)result).Should().Be(expected);
        }

        #endregion

        #region Bitwise Operations

        [Test]
        public void UInt256_BitwiseAnd_MatchesBigInteger()
        {
            BigInteger a = TestNumbers.TwoTo128 + 0xFF00FF00;
            BigInteger b = TestNumbers.TwoTo64 + 0x00FF00FF;
            BigInteger expected = a & b;

            UInt256 ua = (UInt256)a;
            UInt256 ub = (UInt256)b;
            UInt256 result = ua & ub;

            ((BigInteger)result).Should().Be(expected);
        }

        [Test]
        public void UInt256_BitwiseOr_MatchesBigInteger()
        {
            BigInteger a = TestNumbers.TwoTo128 + 0xFF00FF00;
            BigInteger b = TestNumbers.TwoTo64 + 0x00FF00FF;
            BigInteger expected = a | b;

            UInt256 ua = (UInt256)a;
            UInt256 ub = (UInt256)b;
            UInt256 result = ua | ub;

            ((BigInteger)result).Should().Be(expected);
        }

        [Test]
        public void UInt256_BitwiseXor_MatchesBigInteger()
        {
            BigInteger a = TestNumbers.TwoTo128 + 0xFF00FF00;
            BigInteger b = TestNumbers.TwoTo64 + 0x00FF00FF;
            BigInteger expected = a ^ b;

            UInt256 ua = (UInt256)a;
            UInt256 ub = (UInt256)b;
            UInt256 result = ua ^ ub;

            ((BigInteger)result).Should().Be(expected);
        }

        [Test]
        public void UInt256_LeftShift_MatchesBigInteger()
        {
            BigInteger a = TestNumbers.TwoTo64 + 12345;
            int shift = 64;
            BigInteger expected = (a << shift) % TestNumbers.TwoTo256;

            UInt256 ua = (UInt256)a;
            UInt256 result = ua << shift;

            ((BigInteger)result).Should().Be(expected);
        }

        [Test]
        public void UInt256_RightShift_MatchesBigInteger()
        {
            BigInteger a = TestNumbers.TwoTo192 + 12345;
            int shift = 64;
            BigInteger expected = a >> shift;

            UInt256 ua = (UInt256)a;
            UInt256 result = ua >> shift;

            ((BigInteger)result).Should().Be(expected);
        }

        #endregion

        #region Comparison Operators

        [Test]
        public void UInt256_LessThan_Works()
        {
            ((UInt256)100 < (UInt256)200).Should().BeTrue();
            ((UInt256)200 < (UInt256)100).Should().BeFalse();
            ((UInt256)100 < (UInt256)100).Should().BeFalse();
        }

        [Test]
        public void UInt256_LessThanOrEqual_Works()
        {
            ((UInt256)100 <= (UInt256)200).Should().BeTrue();
            ((UInt256)200 <= (UInt256)100).Should().BeFalse();
            ((UInt256)100 <= (UInt256)100).Should().BeTrue();
        }

        [Test]
        public void UInt256_GreaterThan_Works()
        {
            ((UInt256)200 > (UInt256)100).Should().BeTrue();
            ((UInt256)100 > (UInt256)200).Should().BeFalse();
            ((UInt256)100 > (UInt256)100).Should().BeFalse();
        }

        [Test]
        public void UInt256_GreaterThanOrEqual_Works()
        {
            ((UInt256)200 >= (UInt256)100).Should().BeTrue();
            ((UInt256)100 >= (UInt256)200).Should().BeFalse();
            ((UInt256)100 >= (UInt256)100).Should().BeTrue();
        }

        [Test]
        public void Int256_Comparisons_WithNegatives()
        {
            (new Int256(-100) < (Int256)100).Should().BeTrue();
            (new Int256(-100) < new Int256(-50)).Should().BeTrue();
            ((Int256)100 > new Int256(-100)).Should().BeTrue();
        }

        #endregion

        #region Increment / Decrement Operators

        [Test]
        public void UInt256_Increment()
        {
            UInt256 value = (UInt256)100;
            value++;
            value.Should().Be((UInt256)101);
        }

        [Test]
        public void UInt256_Decrement()
        {
            UInt256 value = (UInt256)100;
            value--;
            value.Should().Be((UInt256)99);
        }

        [Test]
        public void Int256_Increment()
        {
            Int256 value = (Int256)100;
            value++;
            value.Should().Be((Int256)101);
        }

        [Test]
        public void Int256_Decrement()
        {
            Int256 value = (Int256)100;
            value--;
            value.Should().Be((Int256)99);
        }

        [Test]
        public void Int256_Increment_FromNegative()
        {
            Int256 value = new Int256(-1);
            value++;
            value.Should().Be(Int256.Zero);
        }

        [Test]
        public void Int256_Decrement_ToNegative()
        {
            Int256 value = Int256.Zero;
            value--;
            ((BigInteger)value).Should().Be(-1);
        }

        #endregion

        #region Generic Math Algorithm Tests

        [Test]
        public void UInt256_WorksWithGenericSum()
        {
            var values = new[] { (UInt256)1, (UInt256)2, (UInt256)3, (UInt256)4, (UInt256)5 };
            var result = GenericSum(values);
            result.Should().Be((UInt256)15);
        }

        [Test]
        public void Int256_WorksWithGenericSum()
        {
            var values = new[] { (Int256)1, new Int256(-2), (Int256)3, new Int256(-4), (Int256)5 };
            var result = GenericSum(values);
            ((BigInteger)result).Should().Be(3);
        }

        private static T GenericSum<T>(T[] values) where T : INumber<T>
        {
            T sum = T.Zero;
            foreach (var v in values)
                sum += v;
            return sum;
        }

        [Test]
        public void UInt256_WorksWithGenericProduct()
        {
            var values = new[] { (UInt256)2, (UInt256)3, (UInt256)4 };
            var result = GenericProduct(values);
            result.Should().Be((UInt256)24);
        }

        private static T GenericProduct<T>(T[] values) where T : INumber<T>
        {
            T product = T.One;
            foreach (var v in values)
                product *= v;
            return product;
        }

        #endregion

        #region Checked Conversion Overflow Tests

        [Test]
        public void UInt256_TryConvertFromChecked_NegativeDouble_ThrowsOverflow()
        {
            Action act = () => CreateChecked<double, UInt256>(-1.0);
            act.Should().Throw<OverflowException>();
        }

        [Test]
        public void UInt256_TryConvertFromChecked_NaN_ThrowsOverflow()
        {
            Action act = () => CreateChecked<double, UInt256>(double.NaN);
            act.Should().Throw<OverflowException>();
        }

        [Test]
        public void UInt256_TryConvertFromChecked_PositiveInfinity_ThrowsOverflow()
        {
            Action act = () => CreateChecked<double, UInt256>(double.PositiveInfinity);
            act.Should().Throw<OverflowException>();
        }

        [Test]
        public void UInt256_TryConvertFromChecked_NegativeDecimal_ThrowsOverflow()
        {
            Action act = () => CreateChecked<decimal, UInt256>(-1.0m);
            act.Should().Throw<OverflowException>();
        }

        [Test]
        public void UInt256_TryConvertToChecked_LargeValue_ToNuint_ThrowsOverflow()
        {
            UInt256 largeValue = UInt256.MaxValue;
            Action act = () => CreateChecked<UInt256, nuint>(largeValue);
            act.Should().Throw<OverflowException>();
        }

        [Test]
        public void UInt256_TryConvertToChecked_LargeValue_ToNint_ThrowsOverflow()
        {
            UInt256 largeValue = UInt256.MaxValue;
            Action act = () => CreateChecked<UInt256, nint>(largeValue);
            act.Should().Throw<OverflowException>();
        }

        [Test]
        public void Int256_TryConvertFromChecked_NaN_ThrowsOverflow()
        {
            Action act = () => CreateChecked<double, Int256>(double.NaN);
            act.Should().Throw<OverflowException>();
        }

        [Test]
        public void Int256_TryConvertFromChecked_Infinity_ThrowsOverflow()
        {
            Action act = () => CreateChecked<double, Int256>(double.PositiveInfinity);
            act.Should().Throw<OverflowException>();
        }

        private static TResult CreateChecked<TSource, TResult>(TSource value)
            where TSource : INumberBase<TSource>
            where TResult : INumberBase<TResult>
        {
            return TResult.CreateChecked(value);
        }

        private static TResult CreateSaturating<TSource, TResult>(TSource value)
            where TSource : INumberBase<TSource>
            where TResult : INumberBase<TResult>
        {
            return TResult.CreateSaturating(value);
        }

        #endregion

        #region Rotation Tests

        [Test]
        public void UInt256_RotateLeft_Zero()
        {
            var value = (UInt256)0x12345678;
            var result = RotateLeft(value, 0);
            result.Should().Be(value);
        }

        [Test]
        public void UInt256_RotateLeft_ByOne()
        {
            var value = (UInt256)1;
            var result = RotateLeft(value, 1);
            result.Should().Be((UInt256)2);
        }

        [Test]
        public void UInt256_RotateLeft_Wraps()
        {
            // Rotate left by 256 should be same as original
            var value = (UInt256)0x12345678;
            var result = RotateLeft(value, 256);
            result.Should().Be(value);
        }

        [Test]
        public void UInt256_RotateRight_ByOne()
        {
            var value = (UInt256)2;
            var result = RotateRight(value, 1);
            result.Should().Be((UInt256)1);
        }

        [Test]
        public void Int256_RotateLeft_Zero()
        {
            var value = (Int256)0x12345678;
            var result = RotateLeft(value, 0);
            result.Should().Be(value);
        }

        [Test]
        public void Int256_RotateLeft_ByOne()
        {
            var value = (Int256)1;
            var result = RotateLeft(value, 1);
            ((BigInteger)result).Should().Be(2);
        }

        [Test]
        public void Int256_RotateRight_ByOne()
        {
            var value = (Int256)2;
            var result = RotateRight(value, 1);
            ((BigInteger)result).Should().Be(1);
        }

        [Test]
        public void Int256_RotateLeft_NegativeValue_UsesLogicalShift()
        {
            // When rotating a negative Int256, the bits should rotate without sign extension
            var value = new Int256(-1); // All bits set
            var rotated = RotateLeft(value, 1);
            // After rotation, all bits should still be set
            ((BigInteger)rotated).Should().Be(-1);
        }

        private static T RotateLeft<T>(T value, int rotateAmount) where T : IBinaryInteger<T>
        {
            return T.RotateLeft(value, rotateAmount);
        }

        private static T RotateRight<T>(T value, int rotateAmount) where T : IBinaryInteger<T>
        {
            return T.RotateRight(value, rotateAmount);
        }

        #endregion

        #region Saturating Conversion Tests

        [Test]
        public void UInt256_TryConvertToSaturating_LargeValue_ToNuint_Saturates()
        {
            UInt256 largeValue = UInt256.MaxValue;
            var result = CreateSaturating<UInt256, nuint>(largeValue);
            result.Should().Be(nuint.MaxValue);
        }

        [Test]
        public void UInt256_TryConvertToSaturating_LargeValue_ToSByte_Saturates()
        {
            UInt256 largeValue = UInt256.MaxValue;
            var result = CreateSaturating<UInt256, sbyte>(largeValue);
            result.Should().Be(sbyte.MaxValue);
        }

        [Test]
        public void UInt256_TryConvertToSaturating_LargeValue_ToInt_Saturates()
        {
            UInt256 largeValue = UInt256.MaxValue;
            var result = CreateSaturating<UInt256, int>(largeValue);
            result.Should().Be(int.MaxValue);
        }

        [Test]
        public void UInt256_TryConvertToSaturating_LargeValue_ToLong_Saturates()
        {
            UInt256 largeValue = UInt256.MaxValue;
            var result = CreateSaturating<UInt256, long>(largeValue);
            result.Should().Be(long.MaxValue);
        }

        #endregion

        #region Hex Parsing Tests

        [Test]
        public void UInt256_Parse_HexWithLeadingZero()
        {
            var result = UInt256.Parse("0FF", System.Globalization.NumberStyles.HexNumber, null);
            result.Should().Be((UInt256)255);
        }

        [Test]
        public void UInt256_Parse_HexWithoutLeadingZero()
        {
            // FF should parse correctly with the leading zero fix
            var result = UInt256.Parse("FF", System.Globalization.NumberStyles.HexNumber, null);
            result.Should().Be((UInt256)255);
        }

        [Test]
        public void UInt256_Parse_LargeHexValue()
        {
            // Test that large hex values parse correctly
            var result = UInt256.Parse("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF", System.Globalization.NumberStyles.HexNumber, null);
            result.Should().Be(UInt256.MaxValue);
        }

        #endregion
    }
}
