// SPDX-FileCopyrightText: 2023 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Diagnostics.CodeAnalysis;
using System.Globalization;
using System.Numerics;
using System.Runtime.CompilerServices;

namespace Nethermind.Int256;

public readonly partial struct Int256
{
    #region Additional Operators for Interface Compliance

    public static bool operator ==(Int256 a, Int256 b) => a.Equals(b);
    public static bool operator !=(Int256 a, Int256 b) => !a.Equals(b);
    public static bool operator <(Int256 a, Int256 b)
    {
        int aSign = a.Sign;
        int bSign = b.Sign;

        if (aSign >= 0)
        {
            if (bSign < 0)
                return false;
        }
        else if (bSign >= 0)
        {
            return true;
        }

        return a._value < b._value;
    }
    public static bool operator >(Int256 a, Int256 b) => b < a;
    [OverloadResolutionPriority(1)]
    public static bool operator <=(in Int256 a, in Int256 b) => !(b < a);
    public static bool operator <=(Int256 a, Int256 b) => !(b < a);
    [OverloadResolutionPriority(1)]
    public static bool operator >=(in Int256 a, in Int256 b) => !(a < b);
    public static bool operator >=(Int256 a, Int256 b) => !(a < b);

    [OverloadResolutionPriority(1)]
    public static Int256 operator -(in Int256 a, in Int256 b)
    {
        Subtract(in a, in b, out Int256 res);
        return res;
    }

    public static Int256 operator -(Int256 a, Int256 b)
    {
        Subtract(in a, in b, out Int256 res);
        return res;
    }

    [OverloadResolutionPriority(1)]
    public static Int256 operator *(in Int256 a, in Int256 b)
    {
        Multiply(in a, in b, out Int256 res);
        return res;
    }

    public static Int256 operator *(Int256 a, Int256 b)
    {
        Multiply(in a, in b, out Int256 res);
        return res;
    }

    [OverloadResolutionPriority(1)]
    public static Int256 operator /(in Int256 a, in Int256 b)
    {
        Divide(in a, in b, out Int256 res);
        return res;
    }

    public static Int256 operator /(Int256 a, Int256 b)
    {
        Divide(in a, in b, out Int256 res);
        return res;
    }

    [OverloadResolutionPriority(1)]
    public static Int256 operator %(in Int256 a, in Int256 b)
    {
        Mod(in a, in b, out Int256 res);
        return res;
    }

    public static Int256 operator %(Int256 a, Int256 b)
    {
        Mod(in a, in b, out Int256 res);
        return res;
    }

    [OverloadResolutionPriority(1)]
    public static Int256 operator ++(in Int256 a)
    {
        Add(in a, One, out Int256 res);
        return res;
    }

    public static Int256 operator ++(Int256 a)
    {
        Add(in a, One, out Int256 res);
        return res;
    }

    [OverloadResolutionPriority(1)]
    public static Int256 operator --(in Int256 a)
    {
        Subtract(in a, One, out Int256 res);
        return res;
    }

    public static Int256 operator --(Int256 a)
    {
        Subtract(in a, One, out Int256 res);
        return res;
    }

    public static Int256 operator +(Int256 value) => value;

    public static Int256 operator -(Int256 value)
    {
        Neg(in value, out Int256 res);
        return res;
    }

    [OverloadResolutionPriority(1)]
    public static Int256 operator &(in Int256 a, in Int256 b)
    {
        And(in a, in b, out Int256 res);
        return res;
    }

    public static Int256 operator &(Int256 a, Int256 b)
    {
        And(in a, in b, out Int256 res);
        return res;
    }

    [OverloadResolutionPriority(1)]
    public static Int256 operator |(in Int256 a, in Int256 b)
    {
        Or(in a, in b, out Int256 res);
        return res;
    }

    public static Int256 operator |(Int256 a, Int256 b)
    {
        Or(in a, in b, out Int256 res);
        return res;
    }

    [OverloadResolutionPriority(1)]
    public static Int256 operator ^(in Int256 a, in Int256 b)
    {
        Xor(in a, in b, out Int256 res);
        return res;
    }

    public static Int256 operator ^(Int256 a, Int256 b)
    {
        Xor(in a, in b, out Int256 res);
        return res;
    }

    [OverloadResolutionPriority(1)]
    public static Int256 operator ~(in Int256 a)
    {
        Not(in a, out Int256 res);
        return res;
    }

    public static Int256 operator ~(Int256 a)
    {
        Not(in a, out Int256 res);
        return res;
    }

    [OverloadResolutionPriority(1)]
    public static Int256 operator <<(in Int256 a, int n)
    {
        LeftShift(in a, n, out Int256 res);
        return res;
    }

    public static Int256 operator <<(Int256 a, int n)
    {
        LeftShift(in a, n, out Int256 res);
        return res;
    }

    [OverloadResolutionPriority(1)]
    public static Int256 operator >>(in Int256 a, int n)
    {
        RightShift(in a, n, out Int256 res);
        return res;
    }

    public static Int256 operator >>(Int256 a, int n)
    {
        RightShift(in a, n, out Int256 res);
        return res;
    }

    public static Int256 operator >>>(Int256 value, int shiftAmount)
    {
        UInt256.Rsh(in value._value, shiftAmount, out UInt256 result);
        return new Int256(result);
    }

    #endregion

    #region INumberBase<Int256> Implementation

    static Int256 INumberBase<Int256>.One => One;
    static int INumberBase<Int256>.Radix => 2;
    static Int256 INumberBase<Int256>.Zero => Zero;
    static Int256 IAdditiveIdentity<Int256, Int256>.AdditiveIdentity => Zero;
    static Int256 IMultiplicativeIdentity<Int256, Int256>.MultiplicativeIdentity => One;

    public static Int256 Abs(Int256 value)
    {
        if (value.Sign >= 0)
            return value;
        Neg(in value, out Int256 result);
        return result;
    }

    static bool INumberBase<Int256>.IsCanonical(Int256 value) => true;
    static bool INumberBase<Int256>.IsComplexNumber(Int256 value) => false;
    public static bool IsEvenInteger(Int256 value) => (value._value.u0 & 1) == 0;
    static bool INumberBase<Int256>.IsFinite(Int256 value) => true;
    static bool INumberBase<Int256>.IsImaginaryNumber(Int256 value) => false;
    static bool INumberBase<Int256>.IsInfinity(Int256 value) => false;
    static bool INumberBase<Int256>.IsInteger(Int256 value) => true;
    static bool INumberBase<Int256>.IsNaN(Int256 value) => false;
    static bool INumberBase<Int256>.IsNegative(Int256 value) => value.Sign < 0;
    static bool INumberBase<Int256>.IsNegativeInfinity(Int256 value) => false;
    static bool INumberBase<Int256>.IsNormal(Int256 value) => !value.IsZero;
    public static bool IsOddInteger(Int256 value) => (value._value.u0 & 1) != 0;
    static bool INumberBase<Int256>.IsPositive(Int256 value) => value.Sign >= 0;
    static bool INumberBase<Int256>.IsPositiveInfinity(Int256 value) => false;
    static bool INumberBase<Int256>.IsRealNumber(Int256 value) => true;
    static bool INumberBase<Int256>.IsSubnormal(Int256 value) => false;
    static bool INumberBase<Int256>.IsZero(Int256 value) => value.IsZero;

    public static Int256 MaxMagnitude(Int256 x, Int256 y)
    {
        var absX = Abs(x);
        var absY = Abs(y);
        return absX > absY ? x : y;
    }

    public static Int256 MaxMagnitudeNumber(Int256 x, Int256 y) => MaxMagnitude(x, y);

    public static Int256 MinMagnitude(Int256 x, Int256 y)
    {
        var absX = Abs(x);
        var absY = Abs(y);
        return absX < absY ? x : y;
    }

    public static Int256 MinMagnitudeNumber(Int256 x, Int256 y) => MinMagnitude(x, y);

    public static Int256 Parse(string s, NumberStyles style, IFormatProvider? provider)
        => TryParse(s.AsSpan(), style, provider ?? CultureInfo.InvariantCulture, out Int256 result)
            ? result
            : throw new FormatException();

    public static Int256 Parse(ReadOnlySpan<char> s, NumberStyles style, IFormatProvider? provider)
        => TryParse(s, style, provider ?? CultureInfo.InvariantCulture, out Int256 result)
            ? result
            : throw new FormatException();

    static Int256 ISpanParsable<Int256>.Parse(ReadOnlySpan<char> s, IFormatProvider? provider)
        => TryParse(s, out Int256 result)
            ? result
            : throw new FormatException();

    static Int256 IParsable<Int256>.Parse(string s, IFormatProvider? provider)
        => TryParse(s, out Int256 result)
            ? result
            : throw new FormatException();

    public static bool TryParse([NotNullWhen(true)] string? s, NumberStyles style, IFormatProvider? provider, out Int256 result)
    {
        if (s is null)
        {
            result = Zero;
            return false;
        }
        return TryParse(s.AsSpan(), style, provider, out result);
    }

    public static bool TryParse(ReadOnlySpan<char> s, NumberStyles style, IFormatProvider? provider, out Int256 result)
    {
        if (BigInteger.TryParse(s, style, provider, out BigInteger big))
        {
            result = new Int256(big);
            return true;
        }
        result = Zero;
        return false;
    }

    public static bool TryParse([NotNullWhen(true)] string? s, out Int256 result)
    {
        if (s is null)
        {
            result = Zero;
            return false;
        }
        return TryParse(s.AsSpan(), out result);
    }

    public static bool TryParse(ReadOnlySpan<char> s, out Int256 result)
    {
        bool isHex = s.StartsWith("0x", StringComparison.OrdinalIgnoreCase);
        var style = isHex ? NumberStyles.HexNumber : NumberStyles.Integer;
        var span = isHex ? s[2..] : s;
        return TryParse(span, style, CultureInfo.InvariantCulture, out result);
    }

    static bool ISpanParsable<Int256>.TryParse(ReadOnlySpan<char> s, IFormatProvider? provider, out Int256 result)
        => TryParse(s, out result);

    static bool IParsable<Int256>.TryParse([NotNullWhen(true)] string? s, IFormatProvider? provider, out Int256 result)
        => TryParse(s, out result);

    static bool INumberBase<Int256>.TryConvertFromChecked<TOther>(TOther value, out Int256 result)
        => TryConvertFromChecked(value, out result);

    static bool INumberBase<Int256>.TryConvertFromSaturating<TOther>(TOther value, out Int256 result)
        => TryConvertFromSaturating(value, out result);

    static bool INumberBase<Int256>.TryConvertFromTruncating<TOther>(TOther value, out Int256 result)
        => TryConvertFromTruncating(value, out result);

    static bool INumberBase<Int256>.TryConvertToChecked<TOther>(Int256 value, [MaybeNullWhen(false)] out TOther result)
        => TryConvertToChecked(value, out result);

    static bool INumberBase<Int256>.TryConvertToSaturating<TOther>(Int256 value, [MaybeNullWhen(false)] out TOther result)
        => TryConvertToSaturating(value, out result);

    static bool INumberBase<Int256>.TryConvertToTruncating<TOther>(Int256 value, [MaybeNullWhen(false)] out TOther result)
        => TryConvertToTruncating(value, out result);

    private static bool TryConvertFromChecked<TOther>(TOther value, out Int256 result) where TOther : INumberBase<TOther>
    {
        if (typeof(TOther) == typeof(BigInteger))
        {
            result = new Int256((BigInteger)(object)value);
            return true;
        }
        if (typeof(TOther) == typeof(long))
        {
            result = (long)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(int))
        {
            result = (Int256)(int)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(short))
        {
            result = (Int256)(int)(short)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(sbyte))
        {
            result = (Int256)(int)(sbyte)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(nint))
        {
            result = new Int256((nint)(object)value);
            return true;
        }
        if (typeof(TOther) == typeof(Int128))
        {
            var v = (Int128)(object)value;
            Span<byte> bytes = stackalloc byte[16];
            System.Buffers.Binary.BinaryPrimitives.WriteInt128LittleEndian(bytes, v);
            Span<byte> fullBytes = stackalloc byte[32];
            bytes.CopyTo(fullBytes);
            if (v < 0)
                fullBytes[16..].Fill(0xFF);
            result = new Int256(fullBytes, isBigEndian: false);
            return true;
        }
        if (typeof(TOther) == typeof(ulong))
        {
            result = (Int256)(ulong)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(uint))
        {
            result = (Int256)(ulong)(uint)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(ushort))
        {
            result = (Int256)(ulong)(ushort)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(byte))
        {
            result = (Int256)(ulong)(byte)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(nuint))
        {
            result = (Int256)(ulong)(nuint)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(UInt128))
        {
            var v = (UInt128)(object)value;
            if (v > (UInt128)((BigInteger.One << 255) - 1))
            {
                throw new OverflowException();
            }
            result = new Int256(new UInt256((ulong)v, (ulong)(v >> 64), 0, 0));
            return true;
        }
        if (typeof(TOther) == typeof(Half))
        {
            var v = (double)(Half)(object)value;
            if (double.IsNaN(v) || double.IsInfinity(v))
            {
                throw new OverflowException();
            }
            result = new Int256(new BigInteger(v));
            return true;
        }
        if (typeof(TOther) == typeof(float))
        {
            var v = (float)(object)value;
            if (float.IsNaN(v) || float.IsInfinity(v))
            {
                throw new OverflowException();
            }
            result = new Int256(new BigInteger(v));
            return true;
        }
        if (typeof(TOther) == typeof(double))
        {
            var v = (double)(object)value;
            if (double.IsNaN(v) || double.IsInfinity(v))
            {
                throw new OverflowException();
            }
            result = new Int256(new BigInteger(v));
            return true;
        }
        if (typeof(TOther) == typeof(decimal))
        {
            var v = (decimal)(object)value;
            result = new Int256(new BigInteger(v));
            return true;
        }

        result = default;
        return false;
    }

    private static bool TryConvertFromSaturating<TOther>(TOther value, out Int256 result) where TOther : INumberBase<TOther>
    {
        if (typeof(TOther) == typeof(double))
        {
            var v = (double)(object)value;
            if (double.IsNaN(v) || double.IsNegativeInfinity(v))
            {
                result = Min;
                return true;
            }
            if (double.IsPositiveInfinity(v))
            {
                result = Max;
                return true;
            }
        }
        if (typeof(TOther) == typeof(float))
        {
            var v = (float)(object)value;
            if (float.IsNaN(v) || float.IsNegativeInfinity(v))
            {
                result = Min;
                return true;
            }
            if (float.IsPositiveInfinity(v))
            {
                result = Max;
                return true;
            }
        }
        if (typeof(TOther) == typeof(Half))
        {
            var v = (Half)(object)value;
            if (Half.IsNaN(v) || Half.IsNegativeInfinity(v))
            {
                result = Min;
                return true;
            }
            if (Half.IsPositiveInfinity(v))
            {
                result = Max;
                return true;
            }
        }
        return TryConvertFromChecked(value, out result);
    }

    private static bool TryConvertFromTruncating<TOther>(TOther value, out Int256 result) where TOther : INumberBase<TOther>
        => TryConvertFromChecked(value, out result);

    private static bool TryConvertToChecked<TOther>(Int256 value, [MaybeNullWhen(false)] out TOther result) where TOther : INumberBase<TOther>
    {
        if (typeof(TOther) == typeof(BigInteger))
        {
            result = (TOther)(object)(BigInteger)value;
            return true;
        }
        if (typeof(TOther) == typeof(long))
        {
            result = (TOther)(object)value.ToInt64(null);
            return true;
        }
        if (typeof(TOther) == typeof(int))
        {
            result = (TOther)(object)value.ToInt32(null);
            return true;
        }
        if (typeof(TOther) == typeof(short))
        {
            result = (TOther)(object)value.ToInt16(null);
            return true;
        }
        if (typeof(TOther) == typeof(sbyte))
        {
            result = (TOther)(object)value.ToSByte(null);
            return true;
        }
        if (typeof(TOther) == typeof(nint))
        {
            var big = (BigInteger)value;
            if (big < nint.MinValue || big > nint.MaxValue)
                throw new OverflowException();
            result = (TOther)(object)(nint)big;
            return true;
        }
        if (typeof(TOther) == typeof(Int128))
        {
            var big = (BigInteger)value;
            if (big < (BigInteger)Int128.MinValue || big > (BigInteger)Int128.MaxValue)
                throw new OverflowException();
            result = (TOther)(object)(Int128)big;
            return true;
        }
        if (typeof(TOther) == typeof(ulong))
        {
            result = (TOther)(object)value.ToUInt64(null);
            return true;
        }
        if (typeof(TOther) == typeof(uint))
        {
            result = (TOther)(object)value.ToUInt32(null);
            return true;
        }
        if (typeof(TOther) == typeof(ushort))
        {
            result = (TOther)(object)value.ToUInt16(null);
            return true;
        }
        if (typeof(TOther) == typeof(byte))
        {
            result = (TOther)(object)value.ToByte(null);
            return true;
        }
        if (typeof(TOther) == typeof(nuint))
        {
            var big = (BigInteger)value;
            if (big < 0 || big > nuint.MaxValue)
                throw new OverflowException();
            result = (TOther)(object)(nuint)(ulong)big;
            return true;
        }
        if (typeof(TOther) == typeof(UInt128))
        {
            var big = (BigInteger)value;
            if (big < 0 || big > (BigInteger)UInt128.MaxValue)
                throw new OverflowException();
            result = (TOther)(object)(UInt128)big;
            return true;
        }
        if (typeof(TOther) == typeof(double))
        {
            result = (TOther)(object)value.ToDouble(null);
            return true;
        }
        if (typeof(TOther) == typeof(float))
        {
            result = (TOther)(object)value.ToSingle(null);
            return true;
        }
        if (typeof(TOther) == typeof(Half))
        {
            result = (TOther)(object)(Half)value.ToDouble(null);
            return true;
        }
        if (typeof(TOther) == typeof(decimal))
        {
            result = (TOther)(object)value.ToDecimal(null);
            return true;
        }

        result = default;
        return false;
    }

    private static bool TryConvertToSaturating<TOther>(Int256 value, [MaybeNullWhen(false)] out TOther result) where TOther : INumberBase<TOther>
    {
        if (typeof(TOther) == typeof(byte))
        {
            var big = (BigInteger)value;
            result = (TOther)(object)(big < 0 ? (byte)0 : big > byte.MaxValue ? byte.MaxValue : (byte)big);
            return true;
        }
        if (typeof(TOther) == typeof(ushort))
        {
            var big = (BigInteger)value;
            result = (TOther)(object)(big < 0 ? (ushort)0 : big > ushort.MaxValue ? ushort.MaxValue : (ushort)big);
            return true;
        }
        if (typeof(TOther) == typeof(uint))
        {
            var big = (BigInteger)value;
            result = (TOther)(object)(big < 0 ? 0u : big > uint.MaxValue ? uint.MaxValue : (uint)big);
            return true;
        }
        if (typeof(TOther) == typeof(ulong))
        {
            var big = (BigInteger)value;
            result = (TOther)(object)(big < 0 ? 0ul : big > ulong.MaxValue ? ulong.MaxValue : (ulong)big);
            return true;
        }
        if (typeof(TOther) == typeof(nuint))
        {
            var big = (BigInteger)value;
            result = (TOther)(object)(big < 0 ? (nuint)0 : big > nuint.MaxValue ? nuint.MaxValue : (nuint)(ulong)big);
            return true;
        }
        if (typeof(TOther) == typeof(UInt128))
        {
            if (value.Sign < 0)
            {
                result = (TOther)(object)UInt128.Zero;
                return true;
            }
            if ((value._value.u2 | value._value.u3) != 0)
            {
                result = (TOther)(object)UInt128.MaxValue;
                return true;
            }
            result = (TOther)(object)new UInt128(value._value.u1, value._value.u0);
            return true;
        }
        if (typeof(TOther) == typeof(sbyte))
        {
            var big = (BigInteger)value;
            result = (TOther)(object)(big < sbyte.MinValue ? sbyte.MinValue : big > sbyte.MaxValue ? sbyte.MaxValue : (sbyte)big);
            return true;
        }
        if (typeof(TOther) == typeof(short))
        {
            var big = (BigInteger)value;
            result = (TOther)(object)(big < short.MinValue ? short.MinValue : big > short.MaxValue ? short.MaxValue : (short)big);
            return true;
        }
        if (typeof(TOther) == typeof(int))
        {
            var big = (BigInteger)value;
            result = (TOther)(object)(big < int.MinValue ? int.MinValue : big > int.MaxValue ? int.MaxValue : (int)big);
            return true;
        }
        if (typeof(TOther) == typeof(long))
        {
            var big = (BigInteger)value;
            result = (TOther)(object)(big < long.MinValue ? long.MinValue : big > long.MaxValue ? long.MaxValue : (long)big);
            return true;
        }
        if (typeof(TOther) == typeof(nint))
        {
            var big = (BigInteger)value;
            result = (TOther)(object)(big < nint.MinValue ? nint.MinValue : big > nint.MaxValue ? nint.MaxValue : (nint)big);
            return true;
        }
        if (typeof(TOther) == typeof(Int128))
        {
            var big = (BigInteger)value;
            result = (TOther)(object)(big < (BigInteger)Int128.MinValue ? Int128.MinValue : big > (BigInteger)Int128.MaxValue ? Int128.MaxValue : (Int128)big);
            return true;
        }
        return TryConvertToChecked(value, out result);
    }

    private static bool TryConvertToTruncating<TOther>(Int256 value, [MaybeNullWhen(false)] out TOther result) where TOther : INumberBase<TOther>
    {
        if (typeof(TOther) == typeof(BigInteger))
        {
            result = (TOther)(object)(BigInteger)value;
            return true;
        }
        if (typeof(TOther) == typeof(long))
        {
            result = (TOther)(object)(long)value._value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(int))
        {
            result = (TOther)(object)(int)value._value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(short))
        {
            result = (TOther)(object)(short)value._value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(sbyte))
        {
            result = (TOther)(object)(sbyte)value._value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(nint))
        {
            result = (TOther)(object)(nint)value._value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(Int128))
        {
            result = (TOther)(object)new Int128(value._value.u1, value._value.u0);
            return true;
        }
        if (typeof(TOther) == typeof(ulong))
        {
            result = (TOther)(object)value._value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(uint))
        {
            result = (TOther)(object)(uint)value._value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(ushort))
        {
            result = (TOther)(object)(ushort)value._value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(byte))
        {
            result = (TOther)(object)(byte)value._value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(nuint))
        {
            result = (TOther)(object)(nuint)value._value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(UInt128))
        {
            result = (TOther)(object)new UInt128(value._value.u1, value._value.u0);
            return true;
        }
        if (typeof(TOther) == typeof(double))
        {
            result = (TOther)(object)value.ToDouble(null);
            return true;
        }
        if (typeof(TOther) == typeof(float))
        {
            result = (TOther)(object)value.ToSingle(null);
            return true;
        }
        if (typeof(TOther) == typeof(Half))
        {
            result = (TOther)(object)(Half)value.ToDouble(null);
            return true;
        }
        if (typeof(TOther) == typeof(decimal))
        {
            result = (TOther)(object)value.ToDecimal(null);
            return true;
        }

        result = default;
        return false;
    }

    #endregion

    #region INumber<Int256> Implementation

    public static Int256 Clamp(Int256 value, Int256 min, Int256 max)
    {
        if (min > max)
            throw new ArgumentException($"'{min}' cannot be greater than '{max}'.");
        if (value < min)
            return min;
        if (value > max)
            return max;
        return value;
    }

    public static Int256 CopySign(Int256 value, Int256 sign)
    {
        var absValue = Abs(value);
        return sign.Sign < 0 ? -absValue : absValue;
    }

    static int INumber<Int256>.Sign(Int256 value) => value.Sign;

    #endregion

    #region IBinaryInteger<Int256> Implementation

    public static (Int256 Quotient, Int256 Remainder) DivRem(Int256 left, Int256 right)
    {
        Divide(in left, in right, out Int256 quotient);
        Mod(in left, in right, out Int256 remainder);
        return (quotient, remainder);
    }

    public static Int256 LeadingZeroCount(Int256 value)
    {
        if (value.Sign < 0)
            return Zero;
        return (Int256)(ulong)UInt256.LeadingZeroCount(value._value);
    }

    public static Int256 PopCount(Int256 value)
        => (Int256)(ulong)UInt256.PopCount(value._value);

    public static Int256 TrailingZeroCount(Int256 value)
        => (Int256)(ulong)UInt256.TrailingZeroCount(value._value);

    public static bool TryReadBigEndian(ReadOnlySpan<byte> source, bool isUnsigned, out Int256 value)
    {
        if (source.Length < 32)
        {
            value = default;
            return false;
        }

        value = new Int256(source[..32], isBigEndian: true);
        return true;
    }

    public static bool TryReadLittleEndian(ReadOnlySpan<byte> source, bool isUnsigned, out Int256 value)
    {
        if (source.Length < 32)
        {
            value = default;
            return false;
        }

        value = new Int256(source[..32], isBigEndian: false);
        return true;
    }

    public int GetByteCount() => 32;

    public int GetShortestBitLength()
    {
        if (Sign >= 0)
            return _value.BitLen;

        Neg(out Int256 abs);
        return abs._value.BitLen + 1;
    }

    public bool TryWriteBigEndian(Span<byte> destination, out int bytesWritten)
    {
        if (destination.Length < 32)
        {
            bytesWritten = 0;
            return false;
        }

        _value.ToBigEndian(destination[..32]);
        bytesWritten = 32;
        return true;
    }

    public bool TryWriteLittleEndian(Span<byte> destination, out int bytesWritten)
    {
        if (destination.Length < 32)
        {
            bytesWritten = 0;
            return false;
        }

        _value.ToLittleEndian(destination[..32]);
        bytesWritten = 32;
        return true;
    }

    static Int256 IBinaryInteger<Int256>.RotateLeft(Int256 value, int rotateAmount)
    {
        rotateAmount &= 255;
        if (rotateAmount == 0)
            return value;

        UInt256.Lsh(in value._value, rotateAmount, out UInt256 left);
        UInt256.Rsh(in value._value, 256 - rotateAmount, out UInt256 right);
        UInt256 result = left | right;
        return new Int256(result);
    }

    static Int256 IBinaryInteger<Int256>.RotateRight(Int256 value, int rotateAmount)
    {
        rotateAmount &= 255;
        if (rotateAmount == 0)
            return value;

        UInt256.Rsh(in value._value, rotateAmount, out UInt256 right);
        UInt256.Lsh(in value._value, 256 - rotateAmount, out UInt256 left);
        UInt256 result = right | left;
        return new Int256(result);
    }

    #endregion

    #region IBinaryNumber<Int256> Implementation

    static bool IBinaryNumber<Int256>.IsPow2(Int256 value)
    {
        if (value.Sign <= 0)
            return false;
        int popCount = BitOperations.PopCount(value._value.u0) +
                      BitOperations.PopCount(value._value.u1) +
                      BitOperations.PopCount(value._value.u2) +
                      BitOperations.PopCount(value._value.u3);
        return popCount == 1;
    }

    static Int256 IBinaryNumber<Int256>.Log2(Int256 value)
    {
        if (value.Sign <= 0)
            throw new ArgumentException("Cannot compute Log2 of zero or negative number");
        return (Int256)(ulong)(255 - (int)(ulong)UInt256.LeadingZeroCount(value._value));
    }

    #endregion

    #region ISignedNumber<Int256> Implementation

    static Int256 ISignedNumber<Int256>.NegativeOne => MinusOne;

    #endregion

    #region IMinMaxValue<Int256> Implementation

    static Int256 IMinMaxValue<Int256>.MinValue => Min;
    static Int256 IMinMaxValue<Int256>.MaxValue => Max;

    #endregion

    #region ISpanFormattable Implementation

    public bool TryFormat(Span<char> destination, out int charsWritten, ReadOnlySpan<char> format, IFormatProvider? provider)
    {
        var bigInt = (BigInteger)this;
        return bigInt.TryFormat(destination, out charsWritten, format, provider);
    }

    public string ToString(string? format, IFormatProvider? formatProvider)
        => ((BigInteger)this).ToString(format, formatProvider);

    #endregion
}
