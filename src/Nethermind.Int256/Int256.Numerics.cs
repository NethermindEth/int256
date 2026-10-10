// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Globalization;
using System.Numerics;
using System.Runtime.CompilerServices;

namespace Nethermind.Int256;

// Generic math, laid out as for UInt256: explicit interface members forward to the public `in` operators.
// Unchecked operators wrap, as Add and Divide do (MinValue / -1 gives MinValue, the EVM's SDIV);
// checked operators throw on any overflow.
public readonly partial struct Int256 : INumber<Int256>, IMinMaxValue<Int256>, ISignedNumber<Int256>
{
    private const ulong SignBit = 0x8000_0000_0000_0000;

    public static Int256 operator -(in Int256 a, in Int256 b)
    {
        Subtract(in a, in b, out Int256 res);
        return res;
    }

    /// <summary>Negates <paramref name="a"/>, wrapping: the negation of <c>MinValue</c> is itself.</summary>
    public static Int256 operator -(in Int256 a)
    {
        Neg(in a, out Int256 res);
        return res;
    }

    public static Int256 operator +(in Int256 a) => a;

    public static Int256 operator *(in Int256 a, in Int256 b)
    {
        Multiply(in a, in b, out Int256 res);
        return res;
    }

    /// <summary>Divides, truncating toward zero; <c>MinValue / -1</c> wraps to <c>MinValue</c>.</summary>
    /// <exception cref="DivideByZeroException"><paramref name="b"/> is zero.</exception>
    public static Int256 operator /(in Int256 a, in Int256 b)
    {
        Divide(in a, in b, out Int256 res);
        return res;
    }

    /// <summary>The remainder, which takes the sign of <paramref name="a"/>.</summary>
    /// <exception cref="DivideByZeroException"><paramref name="b"/> is zero.</exception>
    public static Int256 operator %(in Int256 a, in Int256 b)
    {
        Mod(in a, in b, out Int256 res);
        return res;
    }

    public static Int256 operator ++(in Int256 a)
    {
        UInt256.Add(in a._value, new UInt256(1ul), out UInt256 res);
        return new Int256(res);
    }

    public static Int256 operator --(in Int256 a)
    {
        UInt256.Subtract(in a._value, new UInt256(1ul), out UInt256 res);
        return new Int256(res);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool operator <=(in Int256 a, in Int256 b) => !(b < a);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool operator >=(in Int256 a, in Int256 b) => !(a < b);

    private static Int256 MinValueLiteral => new(new UInt256(0, 0, 0, SignBit));

    private static Int256 MaxValueLiteral => new(new UInt256(ulong.MaxValue, ulong.MaxValue, ulong.MaxValue, SignBit - 1));

    static Int256 IAdditiveIdentity<Int256, Int256>.AdditiveIdentity => default;

    static Int256 IMultiplicativeIdentity<Int256, Int256>.MultiplicativeIdentity => new(new UInt256(1ul));

    static Int256 IMinMaxValue<Int256>.MinValue => MinValueLiteral;

    static Int256 IMinMaxValue<Int256>.MaxValue => MaxValueLiteral;

    static Int256 ISignedNumber<Int256>.NegativeOne => new(new UInt256(ulong.MaxValue, ulong.MaxValue, ulong.MaxValue, ulong.MaxValue));

    static Int256 INumberBase<Int256>.One => new(new UInt256(1ul));

    static Int256 INumberBase<Int256>.Zero => default;

    static int INumberBase<Int256>.Radix => 2;

    // Operators

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static Int256 IAdditionOperators<Int256, Int256, Int256>.operator +(Int256 left, Int256 right) => left + right;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static Int256 IAdditionOperators<Int256, Int256, Int256>.operator checked +(Int256 left, Int256 right)
    {
        Int256 res = left + right;
        // Overflow when both operands share a sign the result does not.
        if ((long)((left._value.u3 ^ res._value.u3) & (right._value.u3 ^ res._value.u3)) < 0) UInt256.ThrowOverflowException();
        return res;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static Int256 ISubtractionOperators<Int256, Int256, Int256>.operator -(Int256 left, Int256 right) => left - right;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static Int256 ISubtractionOperators<Int256, Int256, Int256>.operator checked -(Int256 left, Int256 right)
    {
        Int256 res = left - right;
        // Overflow when the operand signs differ and the result's sign is not the left operand's.
        if ((long)((left._value.u3 ^ right._value.u3) & (left._value.u3 ^ res._value.u3)) < 0) UInt256.ThrowOverflowException();
        return res;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static Int256 IMultiplyOperators<Int256, Int256, Int256>.operator *(Int256 left, Int256 right) => left * right;

    static Int256 IMultiplyOperators<Int256, Int256, Int256>.operator checked *(Int256 left, Int256 right)
    {
        bool negative = left.IsNegative ^ right.IsNegative;
        UInt256 a = Magnitude(in left);
        UInt256 b = Magnitude(in right);
        // The product's magnitude may reach 2^255 only when the result is negative.
        if (UInt256.MultiplyOverflow(in a, in b, out UInt256 product)
            || (product.u3 >= SignBit && !(negative && product.u3 == SignBit && (product.u0 | product.u1 | product.u2) == 0)))
        {
            UInt256.ThrowOverflowException();
        }

        Int256 res = new(product);
        return negative ? -res : res;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static Int256 IDivisionOperators<Int256, Int256, Int256>.operator /(Int256 left, Int256 right) => left / right;

    static Int256 IDivisionOperators<Int256, Int256, Int256>.operator checked /(Int256 left, Int256 right)
    {
        if (IsMinValue(in left) && (right._value.u0 & right._value.u1 & right._value.u2 & right._value.u3) == ulong.MaxValue)
        {
            UInt256.ThrowOverflowException();
        }

        return left / right;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static Int256 IModulusOperators<Int256, Int256, Int256>.operator %(Int256 left, Int256 right) => left % right;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static Int256 IIncrementOperators<Int256>.operator ++(Int256 value) => ++value;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static Int256 IIncrementOperators<Int256>.operator checked ++(Int256 value)
    {
        if (IsMaxValue(in value)) UInt256.ThrowOverflowException();
        return ++value;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static Int256 IDecrementOperators<Int256>.operator --(Int256 value) => --value;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static Int256 IDecrementOperators<Int256>.operator checked --(Int256 value)
    {
        if (IsMinValue(in value)) UInt256.ThrowOverflowException();
        return --value;
    }

    static Int256 IUnaryPlusOperators<Int256, Int256>.operator +(Int256 value) => value;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static Int256 IUnaryNegationOperators<Int256, Int256>.operator -(Int256 value) => -value;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static Int256 IUnaryNegationOperators<Int256, Int256>.operator checked -(Int256 value)
    {
        if (IsMinValue(in value)) UInt256.ThrowOverflowException();
        return -value;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool IEqualityOperators<Int256, Int256, bool>.operator ==(Int256 left, Int256 right) => left == right;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool IEqualityOperators<Int256, Int256, bool>.operator !=(Int256 left, Int256 right) => left != right;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool IComparisonOperators<Int256, Int256, bool>.operator <(Int256 left, Int256 right) => left < right;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool IComparisonOperators<Int256, Int256, bool>.operator <=(Int256 left, Int256 right) => left <= right;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool IComparisonOperators<Int256, Int256, bool>.operator >(Int256 left, Int256 right) => left > right;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool IComparisonOperators<Int256, Int256, bool>.operator >=(Int256 left, Int256 right) => left >= right;

    // INumberBase

    /// <summary>Unlike the instance <see cref="Abs(out Int256)"/>, throws for <c>MinValue</c>, as <see cref="Math.Abs(long)"/> does.</summary>
    static Int256 INumberBase<Int256>.Abs(Int256 value)
    {
        if (!value.IsNegative) return value;
        if (IsMinValue(in value)) UInt256.ThrowOverflowException();
        return -value;
    }

    static bool INumberBase<Int256>.IsCanonical(Int256 value) => true;

    static bool INumberBase<Int256>.IsComplexNumber(Int256 value) => false;

    static bool INumberBase<Int256>.IsEvenInteger(Int256 value) => (value._value.u0 & 1) == 0;

    static bool INumberBase<Int256>.IsFinite(Int256 value) => true;

    static bool INumberBase<Int256>.IsImaginaryNumber(Int256 value) => false;

    static bool INumberBase<Int256>.IsInfinity(Int256 value) => false;

    static bool INumberBase<Int256>.IsInteger(Int256 value) => true;

    static bool INumberBase<Int256>.IsNaN(Int256 value) => false;

    static bool INumberBase<Int256>.IsNegative(Int256 value) => value.IsNegative;

    static bool INumberBase<Int256>.IsNegativeInfinity(Int256 value) => false;

    static bool INumberBase<Int256>.IsNormal(Int256 value) => !value.IsZero;

    static bool INumberBase<Int256>.IsOddInteger(Int256 value) => (value._value.u0 & 1) != 0;

    static bool INumberBase<Int256>.IsPositive(Int256 value) => !value.IsNegative;

    static bool INumberBase<Int256>.IsPositiveInfinity(Int256 value) => false;

    static bool INumberBase<Int256>.IsRealNumber(Int256 value) => true;

    static bool INumberBase<Int256>.IsSubnormal(Int256 value) => false;

    static bool INumberBase<Int256>.IsZero(Int256 value) => value.IsZero;

    static Int256 INumberBase<Int256>.MaxMagnitude(Int256 x, Int256 y) => MaxMagnitude(in x, in y);

    static Int256 INumberBase<Int256>.MaxMagnitudeNumber(Int256 x, Int256 y) => MaxMagnitude(in x, in y);

    static Int256 INumberBase<Int256>.MinMagnitude(Int256 x, Int256 y) => MinMagnitude(in x, in y);

    static Int256 INumberBase<Int256>.MinMagnitudeNumber(Int256 x, Int256 y) => MinMagnitude(in x, in y);

    static Int256 INumberBase<Int256>.MultiplyAddEstimate(Int256 left, Int256 right, Int256 addend) => left * right + addend;

    // MinValue has the greatest magnitude; on a tie, the positive value is the greater.
    private static Int256 MaxMagnitude(in Int256 x, in Int256 y)
    {
        int order = Magnitude(in x).CompareTo(Magnitude(in y));
        return order > 0 || (order == 0 && !x.IsNegative) ? x : y;
    }

    private static Int256 MinMagnitude(in Int256 x, in Int256 y)
    {
        int order = Magnitude(in x).CompareTo(Magnitude(in y));
        return order < 0 || (order == 0 && x.IsNegative) ? x : y;
    }

    // INumber

    static Int256 INumber<Int256>.Clamp(Int256 value, Int256 min, Int256 max)
    {
        if (min > max) UInt256.ThrowMinMaxException(min, max);
        return value < min ? min : value > max ? max : value;
    }

    static Int256 INumber<Int256>.CopySign(Int256 value, Int256 sign)
    {
        if (value.IsNegative == sign.IsNegative) return value;
        if (IsMinValue(in value)) UInt256.ThrowOverflowException();
        return -value;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static Int256 INumber<Int256>.Max(Int256 x, Int256 y) => x < y ? y : x;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static Int256 INumber<Int256>.MaxNumber(Int256 x, Int256 y) => x < y ? y : x;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static Int256 INumber<Int256>.Min(Int256 x, Int256 y) => y < x ? y : x;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static Int256 INumber<Int256>.MinNumber(Int256 x, Int256 y) => y < x ? y : x;

    static int INumber<Int256>.Sign(Int256 value) => value.Sign;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool IsMinValue(in Int256 value) =>
        value._value.u3 == SignBit && (value._value.u0 | value._value.u1 | value._value.u2) == 0;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool IsMaxValue(in Int256 value) =>
        value._value.u3 == SignBit - 1 && (value._value.u0 & value._value.u1 & value._value.u2) == ulong.MaxValue;

    /// <summary>The absolute value as unsigned, so <c>MinValue</c> gives 2^255.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static UInt256 Magnitude(in Int256 value)
    {
        if (!value.IsNegative) return value._value;
        UInt256.Subtract(default, in value._value, out UInt256 magnitude);
        return magnitude;
    }

    // Parsing

    static Int256 IParsable<Int256>.Parse(string s, IFormatProvider? provider)
    {
        ArgumentNullException.ThrowIfNull(s);
        return ParseCore(s, NumberStyles.Integer, provider);
    }

    static bool IParsable<Int256>.TryParse([NotNullWhen(true)] string? s, IFormatProvider? provider, out Int256 result)
    {
        if (s is null)
        {
            result = default;
            return false;
        }

        return TryParseCore(s, NumberStyles.Integer, provider, out result);
    }

    static Int256 ISpanParsable<Int256>.Parse(ReadOnlySpan<char> s, IFormatProvider? provider) =>
        ParseCore(s, NumberStyles.Integer, provider);

    static bool ISpanParsable<Int256>.TryParse(ReadOnlySpan<char> s, IFormatProvider? provider, out Int256 result) =>
        TryParseCore(s, NumberStyles.Integer, provider, out result);

    static Int256 INumberBase<Int256>.Parse(string s, NumberStyles style, IFormatProvider? provider)
    {
        ArgumentNullException.ThrowIfNull(s);
        return ParseCore(s, style, provider);
    }

    static Int256 INumberBase<Int256>.Parse(ReadOnlySpan<char> s, NumberStyles style, IFormatProvider? provider) =>
        ParseCore(s, style, provider);

    static bool INumberBase<Int256>.TryParse([NotNullWhen(true)] string? s, NumberStyles style, IFormatProvider? provider, out Int256 result)
    {
        if (s is null)
        {
            result = default;
            return false;
        }

        return TryParseCore(s, style, provider, out result);
    }

    static bool INumberBase<Int256>.TryParse(ReadOnlySpan<char> s, NumberStyles style, IFormatProvider? provider, out Int256 result) =>
        TryParseCore(s, style, provider, out result);

    private static Int256 ParseCore(ReadOnlySpan<char> s, NumberStyles style, IFormatProvider? provider) =>
        TryParseCore(s, style, provider, out Int256 result) ? result : throw new FormatException();

    private static bool TryParseCore(ReadOnlySpan<char> s, NumberStyles style, IFormatProvider? provider, out Int256 result)
    {
        // Hex is the 256-bit two's complement, as Int128 reads it: 64 F's is -1.
        if ((style & NumberStyles.AllowHexSpecifier) != 0)
        {
            bool parsed = UInt256.TryParseHex(s, out UInt256 bits);
            result = new Int256(bits);
            return parsed;
        }

        NumberFormatInfo info = NumberFormatInfo.GetInstance(provider);
        if (style == NumberStyles.Integer && info.PositiveSign == "+" && info.NegativeSign == "-")
        {
            s = UInt256.TrimWhiteSpace(s);
            // The digit check keeps "-+1" and "- 1" out: the unsigned parser accepts a sign and trims.
            bool negative = s.Length > 1 && s[0] == '-' && char.IsAsciiDigit(s[1]);
            if (UInt256.TryParseDecimal(negative ? s[1..] : s, out UInt256 magnitude)
                && (magnitude.u3 < SignBit || (negative && magnitude.u3 == SignBit && (magnitude.u0 | magnitude.u1 | magnitude.u2) == 0)))
            {
                result = new Int256(magnitude);
                if (negative) result = -result;
                return true;
            }

            result = default;
            return false;
        }

        if (BigInteger.TryParse(s, style, provider, out BigInteger big) && big.GetBitLength() <= 255)
        {
            result = FromBigIntegerInRange(big);
            return true;
        }

        result = default;
        return false;
    }

    // Formatting

    /// <summary>
    /// Formats the value. An empty format writes a '-' and the digits, as <see cref="ToString()"/> always has;
    /// <c>"D"</c> and <c>"G"</c> do the same when the culture's negative sign is '-'. Other formats go through
    /// <see cref="BigInteger"/>.
    /// </summary>
    [SkipLocalsInit]
    public string ToString([StringSyntax(StringSyntaxAttribute.NumericFormat)] string? format, IFormatProvider? provider)
    {
        if (!IsPlainDecimal(format, provider)) return ((BigInteger)this).ToString(format, provider);

        Span<char> buffer = stackalloc char[80];
        UInt256.TryFormatDecimal(Magnitude(in this), buffer, out int written, IsNegative);
        return new string(buffer[..written]);
    }

    /// <inheritdoc cref="ToString(string?, IFormatProvider?)"/>
    public bool TryFormat(Span<char> destination, out int charsWritten,
        [StringSyntax(StringSyntaxAttribute.NumericFormat)] ReadOnlySpan<char> format = default, IFormatProvider? provider = null) =>
        IsPlainDecimal(format, provider)
            ? UInt256.TryFormatDecimal(Magnitude(in this), destination, out charsWritten, IsNegative)
            : ((BigInteger)this).TryFormat(destination, out charsWritten, format, provider);

    /// <inheritdoc cref="ToString(string?, IFormatProvider?)"/>
    public bool TryFormat(Span<byte> utf8Destination, out int bytesWritten,
        [StringSyntax(StringSyntaxAttribute.NumericFormat)] ReadOnlySpan<char> format = default, IFormatProvider? provider = null) =>
        IsPlainDecimal(format, provider)
            ? UInt256.TryFormatDecimal(Magnitude(in this), utf8Destination, out bytesWritten, IsNegative)
            : ((IUtf8SpanFormattable)(BigInteger)this).TryFormat(utf8Destination, out bytesWritten, format, provider);

    private bool IsPlainDecimal(ReadOnlySpan<char> format, IFormatProvider? provider) =>
        format.Length == 0
        || (UInt256.IsDecimalFormat(format) && (!IsNegative || NumberFormatInfo.GetInstance(provider).NegativeSign == "-"));

    // Conversions

    /// <inheritdoc cref="INumberBase{TSelf}.CreateChecked{TOther}(TOther)"/>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Int256 CreateChecked<TOther>(TOther value) where TOther : INumberBase<TOther>
    {
        Int256 result;
        if (typeof(TOther) == typeof(Int256))
        {
            result = (Int256)(object)value;
        }
        else if (!TryConvertFrom(value, ConversionMode.Checked, out result) && !TOther.TryConvertToChecked(value, out result))
        {
            ThrowNotSupportedException();
        }

        return result;
    }

    /// <inheritdoc cref="INumberBase{TSelf}.CreateSaturating{TOther}(TOther)"/>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Int256 CreateSaturating<TOther>(TOther value) where TOther : INumberBase<TOther>
    {
        Int256 result;
        if (typeof(TOther) == typeof(Int256))
        {
            result = (Int256)(object)value;
        }
        else if (!TryConvertFrom(value, ConversionMode.Saturating, out result) && !TOther.TryConvertToSaturating(value, out result))
        {
            ThrowNotSupportedException();
        }

        return result;
    }

    /// <inheritdoc cref="INumberBase{TSelf}.CreateTruncating{TOther}(TOther)"/>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Int256 CreateTruncating<TOther>(TOther value) where TOther : INumberBase<TOther>
    {
        Int256 result;
        if (typeof(TOther) == typeof(Int256))
        {
            result = (Int256)(object)value;
        }
        else if (!TryConvertFrom(value, ConversionMode.Truncating, out result) && !TOther.TryConvertToTruncating(value, out result))
        {
            ThrowNotSupportedException();
        }

        return result;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool INumberBase<Int256>.TryConvertFromChecked<TOther>(TOther value, out Int256 result) =>
        TryConvertFrom(value, ConversionMode.Checked, out result);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool INumberBase<Int256>.TryConvertFromSaturating<TOther>(TOther value, out Int256 result) =>
        TryConvertFrom(value, ConversionMode.Saturating, out result);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool INumberBase<Int256>.TryConvertFromTruncating<TOther>(TOther value, out Int256 result) =>
        TryConvertFrom(value, ConversionMode.Truncating, out result);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool INumberBase<Int256>.TryConvertToChecked<TOther>(Int256 value, [MaybeNullWhen(false)] out TOther result) =>
        TryConvertTo(in value, ConversionMode.Checked, out result);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool INumberBase<Int256>.TryConvertToSaturating<TOther>(Int256 value, [MaybeNullWhen(false)] out TOther result) =>
        TryConvertTo(in value, ConversionMode.Saturating, out result);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool INumberBase<Int256>.TryConvertToTruncating<TOther>(Int256 value, [MaybeNullWhen(false)] out TOther result) =>
        TryConvertTo(in value, ConversionMode.Truncating, out result);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool TryConvertFrom<TOther>(TOther value, ConversionMode mode, out Int256 result)
        where TOther : INumberBase<TOther>
    {
        if (typeof(TOther) == typeof(byte))
        {
            result = new Int256(new UInt256((byte)(object)value));
        }
        else if (typeof(TOther) == typeof(char))
        {
            result = new Int256(new UInt256((char)(object)value));
        }
        else if (typeof(TOther) == typeof(ushort))
        {
            result = new Int256(new UInt256((ushort)(object)value));
        }
        else if (typeof(TOther) == typeof(uint))
        {
            result = new Int256(new UInt256((uint)(object)value));
        }
        else if (typeof(TOther) == typeof(ulong))
        {
            result = new Int256(new UInt256((ulong)(object)value));
        }
        else if (typeof(TOther) == typeof(nuint))
        {
            result = new Int256(new UInt256((nuint)(object)value));
        }
        else if (typeof(TOther) == typeof(UInt128))
        {
            UInt128 actual = (UInt128)(object)value;
            result = new Int256(new UInt256((ulong)actual, (ulong)(actual >> 64)));
        }
        else if (typeof(TOther) == typeof(sbyte))
        {
            result = new Int256((long)(sbyte)(object)value);
        }
        else if (typeof(TOther) == typeof(short))
        {
            result = new Int256((long)(short)(object)value);
        }
        else if (typeof(TOther) == typeof(int))
        {
            result = new Int256((long)(int)(object)value);
        }
        else if (typeof(TOther) == typeof(long))
        {
            result = new Int256((long)(object)value);
        }
        else if (typeof(TOther) == typeof(nint))
        {
            result = new Int256((long)(nint)(object)value);
        }
        else if (typeof(TOther) == typeof(Int128))
        {
            Int128 actual = (Int128)(object)value;
            ulong upper = (ulong)(actual >> 64);
            ulong fill = (ulong)((long)upper >> 63);
            result = new Int256(new UInt256((ulong)actual, upper, fill, fill));
        }
        else if (typeof(TOther) == typeof(UInt256))
        {
            result = FromUInt256((UInt256)(object)value, mode);
        }
        else if (typeof(TOther) == typeof(double))
        {
            result = FromDouble((double)(object)value, mode);
        }
        else if (typeof(TOther) == typeof(float))
        {
            result = FromDouble((float)(object)value, mode);
        }
        else if (typeof(TOther) == typeof(Half))
        {
            result = FromDouble((double)(Half)(object)value, mode);
        }
        else if (typeof(TOther) == typeof(decimal))
        {
            decimal actual = (decimal)(object)value;
            UInt128 magnitude = (UInt128)Math.Abs(decimal.Truncate(actual));
            result = new Int256(new UInt256((ulong)magnitude, (ulong)(magnitude >> 64)));
            if (actual < 0) result = -result;
        }
        else if (typeof(TOther) == typeof(BigInteger))
        {
            result = FromBigInteger((BigInteger)(object)value, mode);
        }
        else
        {
            result = default;
            return false;
        }

        return true;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool TryConvertTo<TOther>(in Int256 value, ConversionMode mode, [MaybeNullWhen(false)] out TOther result)
        where TOther : INumberBase<TOther>
    {
        if (typeof(TOther) == typeof(byte))
        {
            result = (TOther)(object)(byte)NarrowUnsigned(in value, byte.MaxValue, mode);
        }
        else if (typeof(TOther) == typeof(char))
        {
            result = (TOther)(object)(char)NarrowUnsigned(in value, char.MaxValue, mode);
        }
        else if (typeof(TOther) == typeof(ushort))
        {
            result = (TOther)(object)(ushort)NarrowUnsigned(in value, ushort.MaxValue, mode);
        }
        else if (typeof(TOther) == typeof(uint))
        {
            result = (TOther)(object)(uint)NarrowUnsigned(in value, uint.MaxValue, mode);
        }
        else if (typeof(TOther) == typeof(ulong))
        {
            result = (TOther)(object)NarrowUnsigned(in value, ulong.MaxValue, mode);
        }
        else if (typeof(TOther) == typeof(nuint))
        {
            result = (TOther)(object)(nuint)NarrowUnsigned(in value, nuint.MaxValue, mode);
        }
        else if (typeof(TOther) == typeof(sbyte))
        {
            result = (TOther)(object)(sbyte)NarrowSigned(in value, sbyte.MinValue, sbyte.MaxValue, mode);
        }
        else if (typeof(TOther) == typeof(short))
        {
            result = (TOther)(object)(short)NarrowSigned(in value, short.MinValue, short.MaxValue, mode);
        }
        else if (typeof(TOther) == typeof(int))
        {
            result = (TOther)(object)(int)NarrowSigned(in value, int.MinValue, int.MaxValue, mode);
        }
        else if (typeof(TOther) == typeof(long))
        {
            result = (TOther)(object)NarrowSigned(in value, long.MinValue, long.MaxValue, mode);
        }
        else if (typeof(TOther) == typeof(nint))
        {
            result = (TOther)(object)(nint)NarrowSigned(in value, nint.MinValue, nint.MaxValue, mode);
        }
        else if (typeof(TOther) == typeof(UInt128))
        {
            UInt128 actual = new(value._value.u1, value._value.u0);
            if ((value._value.u2 | value._value.u3) != 0 && mode != ConversionMode.Truncating)
            {
                if (mode == ConversionMode.Checked) UInt256.ThrowOverflowException();
                actual = value.IsNegative ? UInt128.MinValue : UInt128.MaxValue;
            }

            result = (TOther)(object)actual;
        }
        else if (typeof(TOther) == typeof(Int128))
        {
            Int128 actual = new(value._value.u1, value._value.u0);
            ulong fill = (ulong)((long)value._value.u1 >> 63);
            if ((value._value.u2 != fill || value._value.u3 != fill) && mode != ConversionMode.Truncating)
            {
                if (mode == ConversionMode.Checked) UInt256.ThrowOverflowException();
                actual = value.IsNegative ? Int128.MinValue : Int128.MaxValue;
            }

            result = (TOther)(object)actual;
        }
        else if (typeof(TOther) == typeof(double))
        {
            double magnitude = UInt256.ToDouble(Magnitude(in value));
            result = (TOther)(object)(value.IsNegative ? -magnitude : magnitude);
        }
        else if (typeof(TOther) == typeof(float))
        {
            float magnitude = UInt256.ToSingle(Magnitude(in value));
            result = (TOther)(object)(value.IsNegative ? -magnitude : magnitude);
        }
        else if (typeof(TOther) == typeof(Half))
        {
            Half magnitude = UInt256.ToHalf(Magnitude(in value));
            result = (TOther)(object)(value.IsNegative ? -magnitude : magnitude);
        }
        else if (typeof(TOther) == typeof(decimal))
        {
            result = (TOther)(object)UInt256.ToDecimal(Magnitude(in value), value.IsNegative, mode);
        }
        else if (typeof(TOther) == typeof(BigInteger))
        {
            result = (TOther)(object)(BigInteger)value;
        }
        else
        {
            result = default;
            return false;
        }

        return true;
    }

    /// <summary>The low limb when the value is in <c>[0, max]</c>; otherwise throws, saturates or truncates.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong NarrowUnsigned(in Int256 value, ulong max, ConversionMode mode)
    {
        UInt256 bits = value._value;
        if ((bits.u1 | bits.u2 | bits.u3) == 0 && bits.u0 <= max) return bits.u0;
        if (mode == ConversionMode.Checked) UInt256.ThrowOverflowException();
        if (mode == ConversionMode.Saturating) return value.IsNegative ? 0 : max;
        return bits.u0;
    }

    /// <summary>The low limb when the value is in <c>[min, max]</c>; otherwise throws, saturates or truncates.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static long NarrowSigned(in Int256 value, long min, long max, ConversionMode mode)
    {
        UInt256 bits = value._value;
        long low = (long)bits.u0;
        ulong fill = (ulong)(low >> 63);
        if (bits.u1 == fill && bits.u2 == fill && bits.u3 == fill && low >= min && low <= max) return low;
        if (mode == ConversionMode.Checked) UInt256.ThrowOverflowException();
        if (mode == ConversionMode.Saturating) return value.IsNegative ? min : max;
        return low;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static Int256 FromUInt256(in UInt256 value, ConversionMode mode)
    {
        if (value.u3 >= SignBit && mode != ConversionMode.Truncating)
        {
            if (mode == ConversionMode.Checked) UInt256.ThrowOverflowException();
            return MaxValueLiteral;
        }

        return new Int256(value);
    }

    /// <summary>Truncates toward zero; truncating behaves as saturating, with NaN giving zero, as for <see cref="Int128"/>.</summary>
    private static Int256 FromDouble(double value, ConversionMode mode)
    {
        double twoTo255 = BitConverter.UInt64BitsToDouble(0x4FE0_0000_0000_0000);
        // No double lies strictly between -2^255 - 1 and -2^255, so -2^255 is the only boundary needed.
        if (mode == ConversionMode.Checked && !(value >= -twoTo255 && value < twoTo255)) UInt256.ThrowOverflowException();
        if (value >= twoTo255) return MaxValueLiteral;
        if (value <= -twoTo255) return MinValueLiteral;

        Int256 magnitude = new(UInt256.FromDoubleInRange(Math.Abs(value)));
        return value < 0 ? -magnitude : magnitude;
    }

    private static Int256 FromBigInteger(BigInteger value, ConversionMode mode)
    {
        if (value.GetBitLength() <= 255) return FromBigIntegerInRange(value);
        if (mode == ConversionMode.Checked) UInt256.ThrowOverflowException();
        if (mode == ConversionMode.Saturating) return value.Sign < 0 ? MinValueLiteral : MaxValueLiteral;
        return new Int256(UInt256.CreateTruncating(value));
    }

    /// <summary>Writes the two's complement bytes over a sign-filled buffer.</summary>
    private static Int256 FromBigIntegerInRange(BigInteger value)
    {
        Span<byte> bytes = stackalloc byte[32];
        bytes.Fill(value.Sign < 0 ? (byte)0xFF : (byte)0);
        value.TryWriteBytes(bytes, out _);
        return new Int256(bytes, isBigEndian: false);
    }

    [DoesNotReturn, StackTraceHidden]
    private static void ThrowNotSupportedException() => throw new NotSupportedException();
}
