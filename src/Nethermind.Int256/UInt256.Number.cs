using System;
using System.Diagnostics.CodeAnalysis;
using System.Globalization;
using System.Numerics;
using System.Runtime.CompilerServices;

[assembly: InternalsVisibleTo("Nethermind.Int256.Test")]

namespace Nethermind.Int256
{
    public readonly partial struct UInt256 : INumber<UInt256>
    {
        static bool IComparisonOperators<UInt256, UInt256, bool>.operator >(UInt256 left, UInt256 right) => LessThan(right, left);

        static bool IComparisonOperators<UInt256, UInt256, bool>.operator >=(UInt256 left, UInt256 right) => !LessThan(left, right);

        static bool IComparisonOperators<UInt256, UInt256, bool>.operator <(UInt256 left, UInt256 right) => LessThan(left, right);

        static bool IComparisonOperators<UInt256, UInt256, bool>.operator <=(UInt256 left, UInt256 right) => !LessThan(right, left);

        static UInt256 IModulusOperators<UInt256, UInt256, UInt256>.operator %(UInt256 left, UInt256 right)
        {
            Mod(in left, in right, out UInt256 result);
            return result;
        }

        static UInt256 IAdditionOperators<UInt256, UInt256, UInt256>.operator +(UInt256 left, UInt256 right)
        {
            Add(in left, in right, out UInt256 result);
            return result;
        }

        static UInt256 IDecrementOperators<UInt256>.operator --(UInt256 value)
        {
            Subtract(in value, One, out UInt256 result);
            return result;
        }

        static UInt256 IDivisionOperators<UInt256, UInt256, UInt256>.operator /(UInt256 left, UInt256 right)
        {
            Divide(in left, in right, out UInt256 result);
            return result;
        }

        static bool IEqualityOperators<UInt256, UInt256, bool>.operator ==(UInt256 left, UInt256 right) => left.Equals(right);

        static bool IEqualityOperators<UInt256, UInt256, bool>.operator !=(UInt256 left, UInt256 right) => !left.Equals(right);

        static UInt256 IIncrementOperators<UInt256>.operator ++(UInt256 value)
        {
            Add(in value, One, out UInt256 result);
            return result;
        }

        static UInt256 IMultiplyOperators<UInt256, UInt256, UInt256>.operator *(UInt256 left, UInt256 right)
        {
            Multiply(in left, in right, out UInt256 result);
            return result;
        }

        static UInt256 ISubtractionOperators<UInt256, UInt256, UInt256>.operator -(UInt256 left, UInt256 right)
        {
            Subtract(in left, in right, out UInt256 result);
            return result;
        }

        static UInt256 IUnaryNegationOperators<UInt256, UInt256>.operator -(UInt256 value) => Negate(in value);

        static UInt256 IUnaryPlusOperators<UInt256, UInt256>.operator +(UInt256 value) => value;

        static UInt256 INumberBase<UInt256>.One => UInt256.One;

        static int INumberBase<UInt256>.Radix => throw new NotImplementedException();

        static UInt256 INumberBase<UInt256>.Zero => UInt256.Zero;

        static UInt256 IAdditiveIdentity<UInt256, UInt256>.AdditiveIdentity => Zero;
        static UInt256 IMultiplicativeIdentity<UInt256, UInt256>.MultiplicativeIdentity => UInt256.One;

        [DoesNotReturn]
        private static void ThrowDivideByZeroException() => throw new DivideByZeroException("y == 0");

        [DoesNotReturn]
        private static void ThrowArithmeticException(in UInt256 a, in UInt256 b) => throw new ArithmeticException($"Underflow in subtraction {a} - {b}");

        [DoesNotReturn]
        private static void ThrowOverflowException() => throw new OverflowException("y <= hi");

        [DoesNotReturn]
        private static void ThrowNotSupportedException() => throw new NotSupportedException();

        [DoesNotReturn]
        private static ulong ThrowIndexOutOfRangeException() => throw new IndexOutOfRangeException();

        static UInt256 INumberBase<UInt256>.Abs(UInt256 value) => value;

        static bool INumberBase<UInt256>.IsCanonical(UInt256 value) => true;

        static bool INumberBase<UInt256>.IsComplexNumber(UInt256 value) => false;

        static bool INumberBase<UInt256>.IsEvenInteger(UInt256 value)
        {
            Mod(in value, 2, out UInt256 res);
            return res == One;
        }

        static bool INumberBase<UInt256>.IsFinite(UInt256 value) => IsFinite;

        static bool INumberBase<UInt256>.IsImaginaryNumber(UInt256 value) => false;

        static bool INumberBase<UInt256>.IsInfinity(UInt256 value) => !IsFinite;

        static bool INumberBase<UInt256>.IsInteger(UInt256 value) => true;

        static bool INumberBase<UInt256>.IsNaN(UInt256 value) => false;

        static bool INumberBase<UInt256>.IsNegative(UInt256 value) => false;

        static bool INumberBase<UInt256>.IsNegativeInfinity(UInt256 value) => false;

        static bool INumberBase<UInt256>.IsNormal(UInt256 value) => true;

        static bool INumberBase<UInt256>.IsOddInteger(UInt256 value)
        {
            Mod(in value, 2, out UInt256 res);
            return res == Zero;
        }

        static bool INumberBase<UInt256>.IsPositive(UInt256 value) => true;

        static bool INumberBase<UInt256>.IsPositiveInfinity(UInt256 value) => false;

        static bool INumberBase<UInt256>.IsRealNumber(UInt256 value) => true; // N c R ?



        static bool INumberBase<UInt256>.IsZero(UInt256 value) => value == UInt256.Zero;

        static UInt256 INumberBase<UInt256>.MaxMagnitude(UInt256 x, UInt256 y) => Max(in x, in y);

        static UInt256 INumberBase<UInt256>.MaxMagnitudeNumber(UInt256 x, UInt256 y) => Max(in x, in y); //INumberBase<UInt256>.MaxMagnitude(x, y);

        static UInt256 INumberBase<UInt256>.MinMagnitude(UInt256 x, UInt256 y) => Min(in x, in y);

        static UInt256 INumberBase<UInt256>.MinMagnitudeNumber(UInt256 x, UInt256 y) => Min(in x, in y); //UInt256.MinMagnitude(x, y);
        static UInt256 INumberBase<UInt256>.Parse(ReadOnlySpan<char> s, NumberStyles style, IFormatProvider? provider)
        {
            TryParse(s, style, provider ?? CultureInfo.InvariantCulture, out UInt256 result);
            return result;
        }

        static UInt256 INumberBase<UInt256>.Parse(string s, NumberStyles style, IFormatProvider? provider)
        {
            TryParse(s, style, provider ?? CultureInfo.InvariantCulture, out UInt256 result);
            return result;
        }


        string IFormattable.ToString(string? format, IFormatProvider? formatProvider)
        {
            return ToString(format, formatProvider);
        }
        static bool INumberBase<UInt256>.TryParse(ReadOnlySpan<char> s, NumberStyles style, IFormatProvider? provider, out UInt256 result)
        {
            return TryParse(s, style, provider ?? CultureInfo.InvariantCulture, out result);
        }

        static UInt256 ISpanParsable<UInt256>.Parse(ReadOnlySpan<char> s, IFormatProvider? provider)
        {
            TryParse(s, NumberStyles.Integer, provider ?? CultureInfo.InvariantCulture, out UInt256 res);
            return res;
        }

        static bool ISpanParsable<UInt256>.TryParse(ReadOnlySpan<char> s, IFormatProvider? provider, out UInt256 result)
        {
            return TryParse(s, NumberStyles.Integer, provider ?? CultureInfo.InvariantCulture, out result);
        }

        static UInt256 IParsable<UInt256>.Parse(string s, IFormatProvider? provider)
        {
            TryParse(s, NumberStyles.Integer, provider ?? CultureInfo.InvariantCulture, out UInt256 res);
            return res;
        }

        static bool INumberBase<UInt256>.IsSubnormal(UInt256 value)
        {
            throw new NotImplementedException();
        }
        static bool IParsable<UInt256>.TryParse(string? s, IFormatProvider? provider, out UInt256 result)
        {
            return TryParse(s ?? String.Empty, NumberStyles.Integer, provider ?? CultureInfo.InvariantCulture, out result);
        }

        static bool INumberBase<UInt256>.TryConvertFromChecked<TOther>(TOther value, out UInt256 result)
        {
            throw new NotImplementedException();
        }

        static bool INumberBase<UInt256>.TryConvertFromSaturating<TOther>(TOther value, out UInt256 result)
        {
            throw new NotImplementedException();
        }

        static bool INumberBase<UInt256>.TryConvertFromTruncating<TOther>(TOther value, out UInt256 result)
        {
            throw new NotImplementedException();
        }

        static bool INumberBase<UInt256>.TryConvertToChecked<TOther>(UInt256 value, out TOther result)
        {
            throw new NotImplementedException();
        }

        static bool INumberBase<UInt256>.TryConvertToSaturating<TOther>(UInt256 value, out TOther result)
        {
            throw new NotImplementedException();
        }

        static bool INumberBase<UInt256>.TryConvertToTruncating<TOther>(UInt256 value, out TOther result)
        {
            throw new NotImplementedException();
        }


        bool ISpanFormattable.TryFormat(Span<char> destination, out int charsWritten, ReadOnlySpan<char> format, IFormatProvider? provider)
        {
            throw new NotImplementedException();
        }

    }
}
