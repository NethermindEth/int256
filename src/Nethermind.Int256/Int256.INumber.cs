using System;
using System.Globalization;
using System.Numerics;
using System.Runtime.CompilerServices;

[assembly: InternalsVisibleTo("Nethermind.Int256.Test")]

namespace Nethermind.Int256
{
    public readonly partial struct Int256 : INumber<Int256>
    {
        static Int256 INumberBase<Int256>.One => One;
        static int INumberBase<Int256>.Radix => throw new NotImplementedException();
        static Int256 INumberBase<Int256>.Zero => Zero;
        static Int256 IAdditiveIdentity<Int256, Int256>.AdditiveIdentity => Zero;
        static Int256 IMultiplicativeIdentity<Int256, Int256>.MultiplicativeIdentity => One;

        static Int256 INumberBase<Int256>.Abs(Int256 value)
        {
            value.Abs(out Int256 result);
            return result;
        }

        static bool INumberBase<Int256>.IsCanonical(Int256 value)
        {
            throw new NotImplementedException();
        }

        static bool INumberBase<Int256>.IsComplexNumber(Int256 value)
            => false;
        static bool INumberBase<Int256>.IsEvenInteger(Int256 value)
        {
            Mod(in value, 2, out Int256 res);
            return res == Zero;
        }

        static bool INumberBase<Int256>.IsFinite(Int256 value)
            => IsFinate;

        static bool INumberBase<Int256>.IsImaginaryNumber(Int256 value)
            => false;
        static bool INumberBase<Int256>.IsInfinity(Int256 value)
            => !IsFinate;

        static bool INumberBase<Int256>.IsInteger(Int256 value)
            => true;

        static bool INumberBase<Int256>.IsNaN(Int256 value)
            => false;
        static bool INumberBase<Int256>.IsNegative(Int256 value)
            => value < 0;

        static bool INumberBase<Int256>.IsNegativeInfinity(Int256 value)
            => false;
        static bool INumberBase<Int256>.IsNormal(Int256 value) => throw new NotImplementedException();

        static bool INumberBase<Int256>.IsOddInteger(Int256 value)
        {
            Mod(in value, 2, out Int256 res);
            return res == One;
        }

        static bool INumberBase<Int256>.IsPositive(Int256 value)
            => value > 0;

        static bool INumberBase<Int256>.IsPositiveInfinity(Int256 value)
            => false;

        static bool INumberBase<Int256>.IsRealNumber(Int256 value)
            => true; // N c R

        static bool INumberBase<Int256>.IsSubnormal(Int256 value)
        {
            throw new NotImplementedException();
        }

        static bool INumberBase<Int256>.IsZero(Int256 value)
            => value == Zero;

        static Int256 INumberBase<Int256>.MaxMagnitude(Int256 x, Int256 y)
            => MaxOf(x, y);

        static Int256 INumberBase<Int256>.MaxMagnitudeNumber(Int256 x, Int256 y)
            => MaxOf(x, y);

        static Int256 INumberBase<Int256>.MinMagnitude(Int256 x, Int256 y)
            => MinOf(x, y);

        static Int256 INumberBase<Int256>.MinMagnitudeNumber(Int256 x, Int256 y)
            => MinOf(x, y);

        static Int256 INumberBase<Int256>.Parse(ReadOnlySpan<char> s, NumberStyles style, IFormatProvider? provider)
        {
            UInt256.TryParse(s, style, provider ?? CultureInfo.InvariantCulture, out UInt256 result);
            return new Int256(result);
        }

        static Int256 INumberBase<Int256>.Parse(string s, NumberStyles style, IFormatProvider? provider)
        {
            UInt256.TryParse(s, style, provider ?? CultureInfo.InvariantCulture, out UInt256 result);
            return new Int256(result);
        }

        static Int256 ISpanParsable<Int256>.Parse(ReadOnlySpan<char> s, IFormatProvider? provider)
        {
            UInt256.TryParse(s, NumberStyles.Integer, provider ?? CultureInfo.InvariantCulture, out UInt256 result);
            return new Int256(result);
        }

        static Int256 IParsable<Int256>.Parse(string s, IFormatProvider? provider)
        {
            UInt256.TryParse(s, NumberStyles.Integer, provider ?? CultureInfo.InvariantCulture, out UInt256 result);
            return new Int256(result);
        }

        static bool INumberBase<Int256>.TryParse(ReadOnlySpan<char> s, NumberStyles style, IFormatProvider? provider, out Int256 result)
        {
            if (UInt256.TryParse(s, style, provider ?? CultureInfo.InvariantCulture, out UInt256 uresult))
            {
                result = new Int256(uresult);
                return true;
            }
            result = default;
            return false;
        }

        static bool INumberBase<Int256>.TryParse(string? s, NumberStyles style, IFormatProvider? provider, out Int256 result)
        {
            if (UInt256.TryParse(s ?? String.Empty, style, provider ?? CultureInfo.InvariantCulture, out UInt256 uresult))
            {
                result = new Int256(uresult);
                return true;
            }
            result = default;
            return false;
        }

        static bool ISpanParsable<Int256>.TryParse(ReadOnlySpan<char> s, IFormatProvider? provider, out Int256 result)
        {
            if (UInt256.TryParse(s, NumberStyles.Integer, provider ?? CultureInfo.InvariantCulture, out UInt256 uresult))
            {
                result = new Int256(uresult);
                return true;
            }
            result = default;
            return false;
        }

        static bool IParsable<Int256>.TryParse(string? s, IFormatProvider? provider, out Int256 result)
        {
            if (UInt256.TryParse(s ?? String.Empty, NumberStyles.Integer, provider ?? CultureInfo.InvariantCulture, out UInt256 uresult))
            {
                result = new Int256(uresult);
                return true;
            }
            result = default;
            return false;
        }

        int IComparable.CompareTo(object? obj) => this.CompareTo(obj);
        int IComparable<Int256>.CompareTo(Int256 other) => this.CompareTo(other);

        bool IEquatable<Int256>.Equals(Int256 other)
        {
            return this == other;
        }

        string IFormattable.ToString(string? format, IFormatProvider? formatProvider)
        {
            return this.ToString(format, formatProvider);
        }

        static Int256 IUnaryPlusOperators<Int256, Int256>.operator +(Int256 value)
        {
            if (value > 0)
            {
                return value;
            }
            Neg(value, out Int256 opposite);
            return opposite;
        }

        static Int256 IAdditionOperators<Int256, Int256, Int256>.operator +(Int256 left, Int256 right)
        {
            Add(in left, in right, out Int256 result);
            return result;
        }

        static Int256 IUnaryNegationOperators<Int256, Int256>.operator -(Int256 value)
        {
            if (value < 0)
            {
                return value;
            }
            Neg(value, out Int256 opposite);
            return opposite;
        }

        static Int256 ISubtractionOperators<Int256, Int256, Int256>.operator -(Int256 left, Int256 right)
        {
            Subtract(in left, in right, out Int256 result);
            return result;
        }

        static Int256 IIncrementOperators<Int256>.operator ++(Int256 value)
        {
            Add(in value, One, out Int256 result);
            return result;
        }

        static Int256 IDecrementOperators<Int256>.operator --(Int256 value)
        {
            Subtract(in value, One, out Int256 result);
            return result;
        }

        static Int256 IMultiplyOperators<Int256, Int256, Int256>.operator *(Int256 left, Int256 right)
        {
            Multiply(in left, in right, out Int256 result);
            return result;
        }

        static Int256 IDivisionOperators<Int256, Int256, Int256>.operator /(Int256 left, Int256 right)
        {
            Divide(in left, in right, out Int256 result);
            return result;
        }

        static Int256 IModulusOperators<Int256, Int256, Int256>.operator %(Int256 left, Int256 right)
        {
            Mod(in left, in right, out Int256 result);
            return result;
        }

        static bool IEqualityOperators<Int256, Int256, bool>.operator ==(Int256 left, Int256 right)
        {
            return left.Equals(right);
        }

        static bool IEqualityOperators<Int256, Int256, bool>.operator !=(Int256 left, Int256 right)
        {
            return !left.Equals(right);
        }

        static bool IComparisonOperators<Int256, Int256, bool>.operator <(Int256 left, Int256 right)
        {
            return left < right;
        }

        static bool IComparisonOperators<Int256, Int256, bool>.operator >(Int256 left, Int256 right)
        {
            return left > right;
        }

        static bool IComparisonOperators<Int256, Int256, bool>.operator <=(Int256 left, Int256 right)
        {
            return !(left > right);
        }

        static bool IComparisonOperators<Int256, Int256, bool>.operator >=(Int256 left, Int256 right)
        {
            return !(left < right);
        }


        bool ISpanFormattable.TryFormat(Span<char> destination, out int charsWritten, ReadOnlySpan<char> format, IFormatProvider? provider)
        {
            throw new NotImplementedException();
        }

        static bool INumberBase<Int256>.TryConvertFromChecked<TOther>(TOther value, out Int256 result)
        {
            throw new NotImplementedException();
        }

        static bool INumberBase<Int256>.TryConvertFromSaturating<TOther>(TOther value, out Int256 result)
        {
            throw new NotImplementedException();
        }

        static bool INumberBase<Int256>.TryConvertFromTruncating<TOther>(TOther value, out Int256 result)
        {
            throw new NotImplementedException();
        }

        static bool INumberBase<Int256>.TryConvertToChecked<TOther>(Int256 value, out TOther result)
        {
            throw new NotImplementedException();
        }

        static bool INumberBase<Int256>.TryConvertToSaturating<TOther>(Int256 value, out TOther result)
        {
            throw new NotImplementedException();
        }

        static bool INumberBase<Int256>.TryConvertToTruncating<TOther>(Int256 value, out TOther result)
        {
            throw new NotImplementedException();
        }

    }
}
