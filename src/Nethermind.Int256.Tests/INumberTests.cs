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

        #region Abs Tests with TestCaseSource

        [TestCaseSource(typeof(UnaryOps), nameof(UnaryOps.TestCases))]
        public void UInt256_Abs_MatchesBigInteger(BigInteger testValue)
        {
            var value = (UInt256)testValue;
            var result = UInt256.Abs(value);
            ((BigInteger)result).Should().Be(testValue);
        }

        [TestCaseSource(typeof(UnaryOps), nameof(UnaryOps.SignedTestCases))]
        public void Int256_Abs_MatchesBigInteger(BigInteger testValue)
        {
            var value = new Int256(testValue);
            var result = Int256.Abs(value);
            ((BigInteger)result).Should().Be(BigInteger.Abs(testValue));
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

        #region Arithmetic Operators with TestCaseSource

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public void UInt256_Addition_MatchesBigInteger((BigInteger A, BigInteger B) test)
        {
            BigInteger expected = (test.A + test.B) % TestNumbers.TwoTo256;

            UInt256 ua = (UInt256)test.A;
            UInt256 ub = (UInt256)test.B;
            UInt256 result = ua + ub;

            ((BigInteger)result).Should().Be(expected);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public void UInt256_Subtraction_MatchesBigInteger((BigInteger A, BigInteger B) test)
        {
            if (test.A < test.B)
                return; // Skip underflow cases for unsigned subtraction

            BigInteger expected = test.A - test.B;

            UInt256 ua = (UInt256)test.A;
            UInt256 ub = (UInt256)test.B;
            UInt256 result = ua - ub;

            ((BigInteger)result).Should().Be(expected);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public void UInt256_Multiplication_MatchesBigInteger((BigInteger A, BigInteger B) test)
        {
            BigInteger expected = (test.A * test.B) % TestNumbers.TwoTo256;

            UInt256 ua = (UInt256)test.A;
            UInt256 ub = (UInt256)test.B;
            UInt256 result = ua * ub;

            ((BigInteger)result).Should().Be(expected);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public void UInt256_Division_MatchesBigInteger((BigInteger A, BigInteger B) test)
        {
            if (test.B.IsZero)
                return; // Skip division by zero

            BigInteger expected = test.A / test.B;

            UInt256 ua = (UInt256)test.A;
            UInt256 ub = (UInt256)test.B;
            UInt256 result = ua / ub;

            ((BigInteger)result).Should().Be(expected);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public void UInt256_Modulus_MatchesBigInteger((BigInteger A, BigInteger B) test)
        {
            if (test.B.IsZero)
                return; // Skip modulus by zero

            BigInteger expected = test.A % test.B;

            UInt256 ua = (UInt256)test.A;
            UInt256 ub = (UInt256)test.B;
            UInt256 result = ua % ub;

            ((BigInteger)result).Should().Be(expected);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedTestCases))]
        public void Int256_Addition_MatchesBigInteger((BigInteger A, BigInteger B) test)
        {
            BigInteger sum = test.A + test.B;
            // Check if result is within Int256 range
            if (sum > TestNumbers.Int256Max || sum < TestNumbers.Int256Min)
                return;

            Int256 a = new Int256(test.A);
            Int256 b = new Int256(test.B);
            Int256 result = a + b;

            ((BigInteger)result).Should().Be(sum);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedTestCases))]
        public void Int256_Subtraction_MatchesBigInteger((BigInteger A, BigInteger B) test)
        {
            BigInteger diff = test.A - test.B;
            // Check if result is within Int256 range
            if (diff > TestNumbers.Int256Max || diff < TestNumbers.Int256Min)
                return;

            Int256 a = new Int256(test.A);
            Int256 b = new Int256(test.B);
            Int256 result = a - b;

            ((BigInteger)result).Should().Be(diff);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedTestCases))]
        public void Int256_Multiplication_MatchesBigInteger((BigInteger A, BigInteger B) test)
        {
            BigInteger product = test.A * test.B;
            // Check if result is within Int256 range
            if (product > TestNumbers.Int256Max || product < TestNumbers.Int256Min)
                return;

            Int256 a = new Int256(test.A);
            Int256 b = new Int256(test.B);
            Int256 result = a * b;

            ((BigInteger)result).Should().Be(product);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedTestCases))]
        public void Int256_Division_MatchesBigInteger((BigInteger A, BigInteger B) test)
        {
            if (test.B.IsZero)
                return; // Skip division by zero

            BigInteger quotient = test.A / test.B;
            // Check if result is within Int256 range
            if (quotient > TestNumbers.Int256Max || quotient < TestNumbers.Int256Min)
                return;

            Int256 a = new Int256(test.A);
            Int256 b = new Int256(test.B);
            Int256 result = a / b;

            ((BigInteger)result).Should().Be(quotient);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedTestCases))]
        public void Int256_Modulus_MatchesBigInteger((BigInteger A, BigInteger B) test)
        {
            if (test.B.IsZero)
                return; // Skip modulus by zero

            BigInteger remainder = test.A % test.B;

            Int256 a = new Int256(test.A);
            Int256 b = new Int256(test.B);
            Int256 result = a % b;

            ((BigInteger)result).Should().Be(remainder);
        }

        #endregion

        #region Bitwise Operations with TestCaseSource

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public void UInt256_BitwiseAnd_MatchesBigInteger((BigInteger A, BigInteger B) test)
        {
            BigInteger expected = test.A & test.B;

            UInt256 ua = (UInt256)test.A;
            UInt256 ub = (UInt256)test.B;
            UInt256 result = ua & ub;

            ((BigInteger)result).Should().Be(expected);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public void UInt256_BitwiseOr_MatchesBigInteger((BigInteger A, BigInteger B) test)
        {
            BigInteger expected = test.A | test.B;

            UInt256 ua = (UInt256)test.A;
            UInt256 ub = (UInt256)test.B;
            UInt256 result = ua | ub;

            ((BigInteger)result).Should().Be(expected);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public void UInt256_BitwiseXor_MatchesBigInteger((BigInteger A, BigInteger B) test)
        {
            BigInteger expected = test.A ^ test.B;

            UInt256 ua = (UInt256)test.A;
            UInt256 ub = (UInt256)test.B;
            UInt256 result = ua ^ ub;

            ((BigInteger)result).Should().Be(expected);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.ShiftTestCases))]
        public void UInt256_LeftShift_MatchesBigInteger((BigInteger A, int Shift) test)
        {
            BigInteger expected = (test.A << test.Shift) % TestNumbers.TwoTo256;

            UInt256 ua = (UInt256)test.A;
            UInt256 result = ua << test.Shift;

            ((BigInteger)result).Should().Be(expected);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.ShiftTestCases))]
        public void UInt256_RightShift_MatchesBigInteger((BigInteger A, int Shift) test)
        {
            BigInteger expected = test.A >> test.Shift;

            UInt256 ua = (UInt256)test.A;
            UInt256 result = ua >> test.Shift;

            ((BigInteger)result).Should().Be(expected);
        }

        [TestCaseSource(typeof(UnaryOps), nameof(UnaryOps.TestCases))]
        public void UInt256_BitwiseComplement_MatchesBigInteger(BigInteger testValue)
        {
            BigInteger expected = TestNumbers.UInt256Max - testValue; // ~x for unsigned = MaxValue - x

            UInt256 u = (UInt256)testValue;
            UInt256 result = ~u;

            ((BigInteger)result).Should().Be(expected);
        }

        #endregion

        #region Comparison Operators with TestCaseSource

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public void UInt256_LessThan_MatchesBigInteger((BigInteger A, BigInteger B) test)
        {
            bool expected = test.A < test.B;

            UInt256 ua = (UInt256)test.A;
            UInt256 ub = (UInt256)test.B;
            bool result = ua < ub;

            result.Should().Be(expected);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public void UInt256_LessThanOrEqual_MatchesBigInteger((BigInteger A, BigInteger B) test)
        {
            bool expected = test.A <= test.B;

            UInt256 ua = (UInt256)test.A;
            UInt256 ub = (UInt256)test.B;
            bool result = ua <= ub;

            result.Should().Be(expected);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public void UInt256_GreaterThan_MatchesBigInteger((BigInteger A, BigInteger B) test)
        {
            bool expected = test.A > test.B;

            UInt256 ua = (UInt256)test.A;
            UInt256 ub = (UInt256)test.B;
            bool result = ua > ub;

            result.Should().Be(expected);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public void UInt256_GreaterThanOrEqual_MatchesBigInteger((BigInteger A, BigInteger B) test)
        {
            bool expected = test.A >= test.B;

            UInt256 ua = (UInt256)test.A;
            UInt256 ub = (UInt256)test.B;
            bool result = ua >= ub;

            result.Should().Be(expected);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public void UInt256_Equality_MatchesBigInteger((BigInteger A, BigInteger B) test)
        {
            bool expected = test.A == test.B;

            UInt256 ua = (UInt256)test.A;
            UInt256 ub = (UInt256)test.B;
            bool result = ua == ub;

            result.Should().Be(expected);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedTestCases))]
        public void Int256_LessThan_MatchesBigInteger((BigInteger A, BigInteger B) test)
        {
            bool expected = test.A < test.B;

            Int256 a = new Int256(test.A);
            Int256 b = new Int256(test.B);
            bool result = a < b;

            result.Should().Be(expected);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedTestCases))]
        public void Int256_GreaterThan_MatchesBigInteger((BigInteger A, BigInteger B) test)
        {
            bool expected = test.A > test.B;

            Int256 a = new Int256(test.A);
            Int256 b = new Int256(test.B);
            bool result = a > b;

            result.Should().Be(expected);
        }

        [Test]
        public void Int256_Comparisons_WithNegatives()
        {
            (new Int256(-100) < (Int256)100).Should().BeTrue();
            (new Int256(-100) < new Int256(-50)).Should().BeTrue();
            ((Int256)100 > new Int256(-100)).Should().BeTrue();
        }

        #endregion

        #region Increment / Decrement Operators with TestCaseSource

        [TestCaseSource(typeof(UnaryOps), nameof(UnaryOps.TestCases))]
        public void UInt256_Increment_MatchesBigInteger(BigInteger testValue)
        {
            if (testValue >= TestNumbers.UInt256Max)
                return; // Skip values that would overflow

            BigInteger expected = testValue + 1;

            UInt256 value = (UInt256)testValue;
            value++;

            ((BigInteger)value).Should().Be(expected);
        }

        [TestCaseSource(typeof(UnaryOps), nameof(UnaryOps.TestCases))]
        public void UInt256_Decrement_MatchesBigInteger(BigInteger testValue)
        {
            if (testValue <= 0)
                return; // Skip values that would underflow

            BigInteger expected = testValue - 1;

            UInt256 value = (UInt256)testValue;
            value--;

            ((BigInteger)value).Should().Be(expected);
        }

        [TestCaseSource(typeof(UnaryOps), nameof(UnaryOps.SignedTestCases))]
        public void Int256_Increment_MatchesBigInteger(BigInteger testValue)
        {
            if (testValue >= TestNumbers.Int256Max)
                return; // Skip values that would overflow

            BigInteger expected = testValue + 1;

            Int256 value = new Int256(testValue);
            value++;

            ((BigInteger)value).Should().Be(expected);
        }

        [TestCaseSource(typeof(UnaryOps), nameof(UnaryOps.SignedTestCases))]
        public void Int256_Decrement_MatchesBigInteger(BigInteger testValue)
        {
            if (testValue <= TestNumbers.Int256Min)
                return; // Skip values that would underflow

            BigInteger expected = testValue - 1;

            Int256 value = new Int256(testValue);
            value--;

            ((BigInteger)value).Should().Be(expected);
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

        #region Sign Tests with TestCaseSource

        [TestCaseSource(typeof(UnaryOps), nameof(UnaryOps.TestCases))]
        public void UInt256_Sign_MatchesBigInteger(BigInteger testValue)
        {
            int expected = testValue.Sign;

            UInt256 value = (UInt256)testValue;
            int result = UInt256.Sign(value);

            result.Should().Be(expected);
        }

        [TestCaseSource(typeof(UnaryOps), nameof(UnaryOps.SignedTestCases))]
        public void Int256_Sign_MatchesBigInteger(BigInteger testValue)
        {
            int expected = testValue.Sign;

            Int256 value = new Int256(testValue);
            int result = value.Sign;

            result.Should().Be(expected);
        }

        #endregion

        #region PopCount Tests with TestCaseSource

        [TestCaseSource(typeof(UnaryOps), nameof(UnaryOps.TestCases))]
        public void UInt256_PopCount_MatchesBigInteger(BigInteger testValue)
        {
            int expected = 0;
            BigInteger temp = testValue;
            while (temp > 0)
            {
                expected += (int)(temp & 1);
                temp >>= 1;
            }

            UInt256 value = (UInt256)testValue;
            UInt256 result = UInt256.PopCount(value);

            ((BigInteger)result).Should().Be(expected);
        }

        #endregion

        #region DivRem Tests with TestCaseSource

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public void UInt256_DivRem_MatchesBigInteger((BigInteger A, BigInteger B) test)
        {
            if (test.B.IsZero)
                return; // Skip division by zero

            BigInteger expectedQuotient = BigInteger.DivRem(test.A, test.B, out BigInteger expectedRemainder);

            var (quotient, remainder) = UInt256.DivRem((UInt256)test.A, (UInt256)test.B);

            ((BigInteger)quotient).Should().Be(expectedQuotient);
            ((BigInteger)remainder).Should().Be(expectedRemainder);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedTestCases))]
        public void Int256_DivRem_MatchesBigInteger((BigInteger A, BigInteger B) test)
        {
            if (test.B.IsZero)
                return; // Skip division by zero

            BigInteger expectedQuotient = BigInteger.DivRem(test.A, test.B, out BigInteger expectedRemainder);

            var (quotient, remainder) = Int256.DivRem(new Int256(test.A), new Int256(test.B));

            ((BigInteger)quotient).Should().Be(expectedQuotient);
            ((BigInteger)remainder).Should().Be(expectedRemainder);
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

        #region TryConvertFromSaturating Additional Tests

        [Test]
        public void UInt256_CreateSaturating_FromNegativeBigInteger_ReturnsZero()
        {
            BigInteger negative = -12345;
            var result = CreateSaturating<BigInteger, UInt256>(negative);
            result.Should().Be(UInt256.Zero);
        }

        [Test]
        public void UInt256_CreateSaturating_FromLargeBigInteger_ReturnsMax()
        {
            BigInteger tooLarge = TestNumbers.UInt256Max + 1;
            var result = CreateSaturating<BigInteger, UInt256>(tooLarge);
            result.Should().Be(UInt256.MaxValue);
        }

        [Test]
        public void UInt256_CreateSaturating_FromNegativeFloat_ReturnsZero()
        {
            var result = CreateSaturating<float, UInt256>(-1.0f);
            result.Should().Be(UInt256.Zero);
        }

        [Test]
        public void UInt256_CreateSaturating_FromNaN_ReturnsZero()
        {
            var result = CreateSaturating<double, UInt256>(double.NaN);
            result.Should().Be(UInt256.Zero);
        }

        [Test]
        public void UInt256_CreateSaturating_FromPositiveInfinity_ReturnsMax()
        {
            var result = CreateSaturating<double, UInt256>(double.PositiveInfinity);
            result.Should().Be(UInt256.MaxValue);
        }

        [Test]
        public void Int256_CreateSaturating_FromNaN_ReturnsMinValue()
        {
            var result = CreateSaturating<double, Int256>(double.NaN);
            result.Should().Be(Int256.MinValue);
        }

        [Test]
        public void Int256_CreateSaturating_FromPositiveInfinity_ReturnsMaxValue()
        {
            var result = CreateSaturating<double, Int256>(double.PositiveInfinity);
            result.Should().Be(Int256.MaxValue);
        }

        [Test]
        public void Int256_CreateSaturating_FromNegativeInfinity_ReturnsMinValue()
        {
            var result = CreateSaturating<double, Int256>(double.NegativeInfinity);
            result.Should().Be(Int256.MinValue);
        }

        #endregion

        #region TryConvertFromTruncating Tests

        [Test]
        public void UInt256_CreateTruncating_FromNegativeByte_Truncates()
        {
            sbyte value = -1; // 0xFF when interpreted as unsigned
            var result = CreateTruncating<sbyte, UInt256>(value);
            result.Should().Be((UInt256)255); // unchecked((byte)(-1)) = 255
        }

        private static TResult CreateTruncating<TSource, TResult>(TSource value)
            where TSource : INumberBase<TSource>
            where TResult : INumberBase<TResult>
        {
            return TResult.CreateTruncating(value);
        }

        #endregion

        #region Int256 Additional Type Conversion Tests

        [Test]
        public void Int256_CreateChecked_FromInt128()
        {
            Int128 value = Int128.MaxValue;
            var result = CreateChecked<Int128, Int256>(value);
            ((BigInteger)result).Should().Be((BigInteger)value);
        }

        [Test]
        public void Int256_CreateChecked_FromNegativeInt128()
        {
            Int128 value = Int128.MinValue;
            var result = CreateChecked<Int128, Int256>(value);
            ((BigInteger)result).Should().Be((BigInteger)value);
        }

        [Test]
        public void Int256_CreateChecked_ToInt128_SmallValue()
        {
            var value = (Int256)12345;
            var result = CreateChecked<Int256, Int128>(value);
            result.Should().Be((Int128)12345);
        }

        [Test]
        public void Int256_CreateChecked_ToInt128_Overflow_Throws()
        {
            var value = Int256.MaxValue;
            Action act = () => CreateChecked<Int256, Int128>(value);
            act.Should().Throw<OverflowException>();
        }

        [Test]
        public void UInt256_CreateChecked_FromUInt128()
        {
            UInt128 value = UInt128.MaxValue;
            var result = CreateChecked<UInt128, UInt256>(value);
            ((BigInteger)result).Should().Be((BigInteger)value);
        }

        [Test]
        public void UInt256_CreateChecked_ToUInt128_SmallValue()
        {
            var value = (UInt256)12345;
            var result = CreateChecked<UInt256, UInt128>(value);
            result.Should().Be((UInt128)12345);
        }

        [Test]
        public void UInt256_CreateChecked_ToUInt128_Overflow_Throws()
        {
            var value = UInt256.MaxValue;
            Action act = () => CreateChecked<UInt256, UInt128>(value);
            act.Should().Throw<OverflowException>();
        }

        #endregion

        #region Int256 Negative Value Operations

        [Test]
        public void Int256_Increment_NegativeValueCrossingZero()
        {
            Int256 value = new Int256(-1);
            value++;
            value.Should().Be(Int256.Zero);
        }

        [Test]
        public void Int256_Decrement_ZeroCrossingToNegative()
        {
            Int256 value = Int256.Zero;
            value--;
            ((BigInteger)value).Should().Be(-1);
        }

        [Test]
        public void Int256_Subtraction_ResultingInNegative()
        {
            Int256 a = (Int256)10;
            Int256 b = (Int256)20;
            Int256 result = a - b;
            ((BigInteger)result).Should().Be(-10);
        }

        [Test]
        public void Int256_Multiplication_NegativeByPositive()
        {
            Int256 a = new Int256(-5);
            Int256 b = (Int256)10;
            Int256 result = a * b;
            ((BigInteger)result).Should().Be(-50);
        }

        [Test]
        public void Int256_Multiplication_NegativeByNegative()
        {
            Int256 a = new Int256(-5);
            Int256 b = new Int256(-10);
            Int256 result = a * b;
            ((BigInteger)result).Should().Be(50);
        }

        [Test]
        public void Int256_Division_NegativeByPositive()
        {
            Int256 a = new Int256(-50);
            Int256 b = (Int256)10;
            Int256 result = a / b;
            ((BigInteger)result).Should().Be(-5);
        }

        [Test]
        public void Int256_Modulus_NegativeValue()
        {
            Int256 a = new Int256(-17);
            Int256 b = (Int256)5;
            var (quotient, remainder) = Int256.DivRem(a, b);
            ((BigInteger)quotient).Should().Be(-3);
            ((BigInteger)remainder).Should().Be(-2);
        }

        [Test]
        public void Int256_UnaryNegation()
        {
            Int256 value = (Int256)100;
            Int256 result = -value;
            ((BigInteger)result).Should().Be(-100);
        }

        [Test]
        public void Int256_UnaryNegation_NegativeValue()
        {
            Int256 value = new Int256(-100);
            Int256 result = -value;
            ((BigInteger)result).Should().Be(100);
        }

        #endregion

        #region IsPow2 Tests

        [Test]
        public void UInt256_IsPow2_One_ReturnsTrue()
        {
            IsPow2<UInt256>(UInt256.One).Should().BeTrue();
        }

        [Test]
        public void UInt256_IsPow2_Two_ReturnsTrue()
        {
            IsPow2<UInt256>((UInt256)2).Should().BeTrue();
        }

        [Test]
        public void UInt256_IsPow2_Three_ReturnsFalse()
        {
            IsPow2<UInt256>((UInt256)3).Should().BeFalse();
        }

        [Test]
        public void UInt256_IsPow2_Zero_ReturnsFalse()
        {
            IsPow2<UInt256>(UInt256.Zero).Should().BeFalse();
        }

        [Test]
        public void UInt256_IsPow2_LargePowerOfTwo()
        {
            // 2^128
            UInt256 value = (UInt256)(BigInteger.One << 128);
            IsPow2<UInt256>(value).Should().BeTrue();
        }

        [Test]
        public void Int256_IsPow2_Positive_ReturnsTrue()
        {
            IsPow2<Int256>((Int256)4).Should().BeTrue();
        }

        [Test]
        public void Int256_IsPow2_Negative_ReturnsFalse()
        {
            IsPow2<Int256>(new Int256(-4)).Should().BeFalse();
        }

        private static bool IsPow2<T>(T value) where T : IBinaryNumber<T>
        {
            return T.IsPow2(value);
        }

        #endregion

        #region Log2 Tests

        [Test]
        public void UInt256_Log2_One_ReturnsZero()
        {
            Log2<UInt256>(UInt256.One).Should().Be((UInt256)0);
        }

        [Test]
        public void UInt256_Log2_Two_ReturnsOne()
        {
            Log2<UInt256>((UInt256)2).Should().Be((UInt256)1);
        }

        [Test]
        public void UInt256_Log2_256_Returns8()
        {
            Log2<UInt256>((UInt256)256).Should().Be((UInt256)8);
        }

        [Test]
        public void UInt256_Log2_MaxValue_Returns255()
        {
            Log2<UInt256>(UInt256.MaxValue).Should().Be((UInt256)255);
        }

        private static T Log2<T>(T value) where T : IBinaryNumber<T>
        {
            return T.Log2(value);
        }

        #endregion

        #region TryReadBigEndian/TryReadLittleEndian Additional Tests

        [Test]
        public void UInt256_TryReadBigEndian_ShortBuffer_ReturnsFalse()
        {
            Span<byte> buffer = stackalloc byte[16];
            bool success = UInt256.TryReadBigEndian(buffer, true, out _);
            success.Should().BeFalse();
        }

        [Test]
        public void UInt256_TryReadLittleEndian_ShortBuffer_ReturnsFalse()
        {
            Span<byte> buffer = stackalloc byte[16];
            bool success = UInt256.TryReadLittleEndian(buffer, true, out _);
            success.Should().BeFalse();
        }

        [Test]
        public void Int256_TryReadBigEndian_ShortBuffer_ReturnsFalse()
        {
            Span<byte> buffer = stackalloc byte[16];
            bool success = Int256.TryReadBigEndian(buffer, false, out _);
            success.Should().BeFalse();
        }

        [Test]
        public void Int256_TryReadLittleEndian_ShortBuffer_ReturnsFalse()
        {
            Span<byte> buffer = stackalloc byte[16];
            bool success = Int256.TryReadLittleEndian(buffer, false, out _);
            success.Should().BeFalse();
        }

        [Test]
        public void Int256_TryWriteBigEndian_ShortBuffer_ReturnsFalse()
        {
            var value = (Int256)12345;
            Span<byte> buffer = stackalloc byte[16];
            bool success = value.TryWriteBigEndian(buffer, out int bytesWritten);
            success.Should().BeFalse();
            bytesWritten.Should().Be(0);
        }

        [Test]
        public void Int256_TryWriteLittleEndian_ShortBuffer_ReturnsFalse()
        {
            var value = (Int256)12345;
            Span<byte> buffer = stackalloc byte[16];
            bool success = value.TryWriteLittleEndian(buffer, out int bytesWritten);
            success.Should().BeFalse();
            bytesWritten.Should().Be(0);
        }

        [Test]
        public void Int256_TryWriteBigEndian_Success()
        {
            var value = new Int256(-12345);
            Span<byte> buffer = stackalloc byte[32];
            bool success = value.TryWriteBigEndian(buffer, out int bytesWritten);
            success.Should().BeTrue();
            bytesWritten.Should().Be(32);
        }

        [Test]
        public void Int256_TryWriteLittleEndian_Success()
        {
            var value = new Int256(-12345);
            Span<byte> buffer = stackalloc byte[32];
            bool success = value.TryWriteLittleEndian(buffer, out int bytesWritten);
            success.Should().BeTrue();
            bytesWritten.Should().Be(32);
        }

        #endregion

        #region GetShortestBitLength Additional Tests

        [Test]
        public void Int256_GetShortestBitLength_PositiveSmallValue()
        {
            var value = (Int256)255; // 8 bits
            value.GetShortestBitLength().Should().Be(8);
        }

        [Test]
        public void Int256_GetShortestBitLength_NegativeValue()
        {
            var value = new Int256(-1);
            // For -1, abs is 1 (1 bit) + 1 for sign bit = 2
            value.GetShortestBitLength().Should().Be(2);
        }

        [Test]
        public void Int256_GetShortestBitLength_Zero()
        {
            Int256.Zero.GetShortestBitLength().Should().Be(0);
        }

        [Test]
        public void Int256_GetByteCount()
        {
            ((Int256)12345).GetByteCount().Should().Be(32);
        }

        #endregion

        #region Additional Bitwise Operations

        [Test]
        public void UInt256_BitwiseComplement()
        {
            var value = (UInt256)0;
            (~value).Should().Be(UInt256.MaxValue);
        }

        [Test]
        public void Int256_BitwiseComplement()
        {
            var value = Int256.Zero;
            var result = ~value;
            ((BigInteger)result).Should().Be(-1); // ~0 = -1 in two's complement
        }

        [Test]
        public void Int256_BitwiseAnd()
        {
            var a = (Int256)0xFF00;
            var b = (Int256)0x0FF0;
            var result = a & b;
            ((BigInteger)result).Should().Be(0x0F00);
        }

        [Test]
        public void Int256_BitwiseOr()
        {
            var a = (Int256)0xFF00;
            var b = (Int256)0x0FF0;
            var result = a | b;
            ((BigInteger)result).Should().Be(0xFFF0);
        }

        [Test]
        public void Int256_BitwiseXor()
        {
            var a = (Int256)0xFF00;
            var b = (Int256)0x0FF0;
            var result = a ^ b;
            ((BigInteger)result).Should().Be(0xF0F0);
        }

        [Test]
        public void Int256_LeftShift()
        {
            var value = (Int256)1;
            var result = value << 64;
            var expected = BigInteger.One << 64;
            ((BigInteger)result).Should().Be(expected);
        }

        [Test]
        public void Int256_RightShift_Positive()
        {
            var value = (Int256)256;
            var result = value >> 4;
            ((BigInteger)result).Should().Be(16);
        }

        [Test]
        public void Int256_UnsignedRightShift()
        {
            var value = new Int256(-1);
            var result = value >>> 1; // unsigned right shift
            // After unsigned right shift, MSB should be 0
            result.Sign.Should().Be(1); // Should be positive
        }

        #endregion

        #region Radix and Identity Tests

        [Test]
        public void UInt256_Radix_IsTwo()
        {
            GetRadix<UInt256>().Should().Be(2);
        }

        [Test]
        public void Int256_Radix_IsTwo()
        {
            GetRadix<Int256>().Should().Be(2);
        }

        [Test]
        public void UInt256_AdditiveIdentity_IsZero()
        {
            GetAdditiveIdentity<UInt256>().Should().Be(UInt256.Zero);
        }

        [Test]
        public void UInt256_MultiplicativeIdentity_IsOne()
        {
            GetMultiplicativeIdentity<UInt256>().Should().Be(UInt256.One);
        }

        [Test]
        public void Int256_AdditiveIdentity_IsZero()
        {
            GetAdditiveIdentity<Int256>().Should().Be(Int256.Zero);
        }

        [Test]
        public void Int256_MultiplicativeIdentity_IsOne()
        {
            GetMultiplicativeIdentity<Int256>().Should().Be(Int256.One);
        }

        private static int GetRadix<T>() where T : INumberBase<T>
        {
            return T.Radix;
        }

        private static T GetAdditiveIdentity<T>() where T : IAdditiveIdentity<T, T>
        {
            return T.AdditiveIdentity;
        }

        private static T GetMultiplicativeIdentity<T>() where T : IMultiplicativeIdentity<T, T>
        {
            return T.MultiplicativeIdentity;
        }

        #endregion

        #region IsNegative/IsPositive Tests

        [Test]
        public void UInt256_IsNegative_AlwaysFalse()
        {
            IsNegative<UInt256>(UInt256.Zero).Should().BeFalse();
            IsNegative<UInt256>(UInt256.MaxValue).Should().BeFalse();
        }

        [Test]
        public void UInt256_IsPositive_AlwaysTrue()
        {
            IsPositive<UInt256>(UInt256.Zero).Should().BeTrue();
            IsPositive<UInt256>(UInt256.MaxValue).Should().BeTrue();
        }

        [Test]
        public void Int256_IsNegative_NegativeValue_ReturnsTrue()
        {
            IsNegative<Int256>(new Int256(-1)).Should().BeTrue();
            IsNegative<Int256>(Int256.MinValue).Should().BeTrue();
        }

        [Test]
        public void Int256_IsNegative_PositiveValue_ReturnsFalse()
        {
            IsNegative<Int256>(Int256.One).Should().BeFalse();
            IsNegative<Int256>(Int256.Zero).Should().BeFalse();
        }

        [Test]
        public void Int256_IsPositive_PositiveValue_ReturnsTrue()
        {
            IsPositive<Int256>(Int256.One).Should().BeTrue();
            IsPositive<Int256>(Int256.Zero).Should().BeTrue();
        }

        [Test]
        public void Int256_IsPositive_NegativeValue_ReturnsFalse()
        {
            IsPositive<Int256>(new Int256(-1)).Should().BeFalse();
        }

        private static bool IsNegative<T>(T value) where T : INumberBase<T>
        {
            return T.IsNegative(value);
        }

        private static bool IsPositive<T>(T value) where T : INumberBase<T>
        {
            return T.IsPositive(value);
        }

        #endregion

        #region IsZero Tests

        [Test]
        public void UInt256_IsZero_Zero_ReturnsTrue()
        {
            IsZero<UInt256>(UInt256.Zero).Should().BeTrue();
        }

        [Test]
        public void UInt256_IsZero_NonZero_ReturnsFalse()
        {
            IsZero<UInt256>(UInt256.One).Should().BeFalse();
        }

        [Test]
        public void Int256_IsZero_Zero_ReturnsTrue()
        {
            IsZero<Int256>(Int256.Zero).Should().BeTrue();
        }

        [Test]
        public void Int256_IsZero_NonZero_ReturnsFalse()
        {
            IsZero<Int256>(Int256.One).Should().BeFalse();
            IsZero<Int256>(new Int256(-1)).Should().BeFalse();
        }

        private static bool IsZero<T>(T value) where T : INumberBase<T>
        {
            return T.IsZero(value);
        }

        #endregion

        #region UnaryPlus Tests

        [Test]
        public void UInt256_UnaryPlus_ReturnsValue()
        {
            var value = (UInt256)12345;
            (+value).Should().Be(value);
        }

        [Test]
        public void Int256_UnaryPlus_PositiveValue_ReturnsValue()
        {
            var value = (Int256)12345;
            (+value).Should().Be(value);
        }

        [Test]
        public void Int256_UnaryPlus_NegativeValue_ReturnsValue()
        {
            var value = new Int256(-12345);
            (+value).Should().Be(value);
        }

        #endregion

        #region Int256 TryParse With Range Validation Tests

        [Test]
        public void Int256_TryParse_ValueExceedingMaxValue_ReturnsFalse()
        {
            // A value larger than Int256.MaxValue
            BigInteger tooLarge = (BigInteger.One << 255);
            string tooLargeStr = tooLarge.ToString();
            bool success = Int256.TryParse(tooLargeStr, out Int256 result);
            success.Should().BeFalse();
            result.Should().Be(Int256.Zero);
        }

        [Test]
        public void Int256_TryParse_ValueBelowMinValue_ReturnsFalse()
        {
            // A value smaller than Int256.MinValue
            BigInteger tooSmall = -(BigInteger.One << 256);
            string tooSmallStr = tooSmall.ToString();
            bool success = Int256.TryParse(tooSmallStr, out Int256 result);
            success.Should().BeFalse();
            result.Should().Be(Int256.Zero);
        }

        [Test]
        public void Int256_TryParse_ValidMaxValue_ReturnsTrue()
        {
            BigInteger maxValue = (BigInteger.One << 255) - 1;
            string maxValueStr = maxValue.ToString();
            bool success = Int256.TryParse(maxValueStr, out Int256 result);
            success.Should().BeTrue();
            result.Should().Be(Int256.MaxValue);
        }

        [Test]
        public void Int256_TryParse_ValidMinValue_ReturnsTrue()
        {
            BigInteger minValue = -(BigInteger.One << 255);
            string minValueStr = minValue.ToString();
            bool success = Int256.TryParse(minValueStr, out Int256 result);
            success.Should().BeTrue();
            result.Should().Be(Int256.MinValue);
        }

        #endregion
    }
}
