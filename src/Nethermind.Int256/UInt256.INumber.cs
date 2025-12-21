// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Diagnostics.CodeAnalysis;
using System.Numerics;
using System.Runtime.CompilerServices;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    /// <inheritdoc />
    static UInt256 INumberBase<UInt256>.One => One;

    /// <inheritdoc />
    static int INumberBase<UInt256>.Radix => 2;

    /// <inheritdoc />
    static UInt256 INumberBase<UInt256>.Zero => Zero;

    /// <inheritdoc />
    static UInt256 IAdditiveIdentity<UInt256, UInt256>.AdditiveIdentity => Zero;

    /// <inheritdoc />
    static UInt256 IMultiplicativeIdentity<UInt256, UInt256>.MultiplicativeIdentity => One;

    [OverloadResolutionPriority(1)]
    public static UInt256 Abs(in UInt256 value) => value;
    /// <inheritdoc />
    public static UInt256 Abs(UInt256 value) => Abs(in value);

    /// <inheritdoc />
    static bool INumberBase<UInt256>.IsCanonical(UInt256 value) => true;

    /// <inheritdoc />
    static bool INumberBase<UInt256>.IsComplexNumber(UInt256 value) => false;

    /// <inheritdoc />
    public static bool IsEvenInteger(UInt256 value) => (value.u0 & 1) == 0;

    /// <inheritdoc />
    static bool INumberBase<UInt256>.IsFinite(UInt256 value) => true;

    /// <inheritdoc />
    static bool INumberBase<UInt256>.IsImaginaryNumber(UInt256 value) => false;

    /// <inheritdoc />
    static bool INumberBase<UInt256>.IsInfinity(UInt256 value) => false;

    /// <inheritdoc />
    static bool INumberBase<UInt256>.IsInteger(UInt256 value) => true;

    /// <inheritdoc />
    static bool INumberBase<UInt256>.IsNaN(UInt256 value) => false;

    /// <inheritdoc />
    static bool INumberBase<UInt256>.IsNegative(UInt256 value) => false;

    /// <inheritdoc />
    static bool INumberBase<UInt256>.IsNegativeInfinity(UInt256 value) => false;

    /// <inheritdoc />
    static bool INumberBase<UInt256>.IsNormal(UInt256 value) => !value.IsZero;

    /// <inheritdoc />
    public static bool IsOddInteger(UInt256 value) => (value.u0 & 1) != 0;

    /// <inheritdoc />
    static bool INumberBase<UInt256>.IsPositive(UInt256 value) => true;

    /// <inheritdoc />
    static bool INumberBase<UInt256>.IsPositiveInfinity(UInt256 value) => false;

    /// <inheritdoc />
    static bool INumberBase<UInt256>.IsRealNumber(UInt256 value) => true;

    /// <inheritdoc />
    static bool INumberBase<UInt256>.IsSubnormal(UInt256 value) => false;

    /// <inheritdoc />
    static bool INumberBase<UInt256>.IsZero(UInt256 value) => value.IsZero;

    /// <inheritdoc />
    public static UInt256 MaxMagnitude(UInt256 x, UInt256 y) => Max(in x, in y);

    /// <inheritdoc />
    public static UInt256 MaxMagnitudeNumber(UInt256 x, UInt256 y) => Max(in x, in y);

    /// <inheritdoc />
    public static UInt256 MinMagnitude(UInt256 x, UInt256 y) => Min(in x, in y);

    /// <inheritdoc />
    public static UInt256 MinMagnitudeNumber(UInt256 x, UInt256 y) => Min(in x, in y);

    /// <inheritdoc />
    static UInt256 ISpanParsable<UInt256>.Parse(ReadOnlySpan<char> s, IFormatProvider? provider)
        => TryParse(s, out UInt256 result)
            ? result
            : throw new FormatException();

    /// <inheritdoc />
    static UInt256 IParsable<UInt256>.Parse(string s, IFormatProvider? provider)
        => TryParse(s, out UInt256 result)
            ? result
            : throw new FormatException();

    /// <inheritdoc />
    static bool ISpanParsable<UInt256>.TryParse(ReadOnlySpan<char> s, IFormatProvider? provider, out UInt256 result)
        => TryParse(s, out result);

    /// <inheritdoc />
    static bool IParsable<UInt256>.TryParse([NotNullWhen(true)] string? s, IFormatProvider? provider, out UInt256 result)
        => TryParse(s, out result);

    /// <inheritdoc />
    static bool INumberBase<UInt256>.TryConvertFromChecked<TOther>(TOther value, out UInt256 result)
        => TryConvertFromChecked(value, out result);

    /// <inheritdoc />
    static bool INumberBase<UInt256>.TryConvertFromSaturating<TOther>(TOther value, out UInt256 result)
        => TryConvertFromSaturating(value, out result);

    /// <inheritdoc />
    static bool INumberBase<UInt256>.TryConvertFromTruncating<TOther>(TOther value, out UInt256 result)
        => TryConvertFromTruncating(value, out result);

    /// <inheritdoc />
    static bool INumberBase<UInt256>.TryConvertToChecked<TOther>(UInt256 value, [MaybeNullWhen(false)] out TOther result)
        => TryConvertToChecked(value, out result);

    /// <inheritdoc />
    static bool INumberBase<UInt256>.TryConvertToSaturating<TOther>(UInt256 value, [MaybeNullWhen(false)] out TOther result)
        => TryConvertToSaturating(value, out result);

    /// <inheritdoc />
    static bool INumberBase<UInt256>.TryConvertToTruncating<TOther>(UInt256 value, [MaybeNullWhen(false)] out TOther result)
        => TryConvertToTruncating(value, out result);

    private static bool TryConvertFromChecked<TOther>(TOther value, out UInt256 result) where TOther : INumberBase<TOther>
    {
        if (typeof(TOther) == typeof(byte))
        {
            result = (byte)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(sbyte))
        {
            var v = (sbyte)(object)value;
            if (v < 0) ThrowOverflowException();
            result = (ulong)v;
            return true;
        }
        if (typeof(TOther) == typeof(ushort))
        {
            result = (ushort)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(short))
        {
            var v = (short)(object)value;
            if (v < 0) ThrowOverflowException();
            result = (ulong)v;
            return true;
        }
        if (typeof(TOther) == typeof(uint))
        {
            result = (uint)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(int))
        {
            var v = (int)(object)value;
            if (v < 0) ThrowOverflowException();
            result = (ulong)v;
            return true;
        }
        if (typeof(TOther) == typeof(ulong))
        {
            result = (ulong)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(long))
        {
            var v = (long)(object)value;
            if (v < 0) ThrowOverflowException();
            result = (ulong)v;
            return true;
        }
        if (typeof(TOther) == typeof(UInt128))
        {
            var v = (UInt128)(object)value;
            result = new UInt256((ulong)v, (ulong)(v >> 64), 0, 0);
            return true;
        }
        if (typeof(TOther) == typeof(Int128))
        {
            var v = (Int128)(object)value;
            if (v < 0) ThrowOverflowException();
            result = new UInt256((ulong)v, (ulong)(v >> 64), 0, 0);
            return true;
        }
        if (typeof(TOther) == typeof(nuint))
        {
            result = (nuint)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(nint))
        {
            var v = (nint)(object)value;
            if (v < 0) ThrowOverflowException();
            result = (ulong)v;
            return true;
        }
        if (typeof(TOther) == typeof(Half))
        {
            var v = (Half)(object)value;
            double dv = (double)v;
            if (dv < 0 || double.IsNaN(dv) || double.IsInfinity(dv)) ThrowOverflowException();
            result = (UInt256)dv;
            return true;
        }
        if (typeof(TOther) == typeof(float))
        {
            var v = (float)(object)value;
            double dv = v;
            if (dv < 0 || double.IsNaN(dv) || double.IsInfinity(dv)) ThrowOverflowException();
            result = (UInt256)dv;
            return true;
        }
        if (typeof(TOther) == typeof(double))
        {
            var v = (double)(object)value;
            if (v < 0 || double.IsNaN(v) || double.IsInfinity(v)) ThrowOverflowException();
            result = (UInt256)v;
            return true;
        }
        if (typeof(TOther) == typeof(decimal))
        {
            var v = (decimal)(object)value;
            if (v < 0) ThrowOverflowException();
            result = (UInt256)new BigInteger(v);
            return true;
        }
        if (typeof(TOther) == typeof(BigInteger))
        {
            var v = (BigInteger)(object)value;
            if (v < 0 || v > (BigInteger)MaxValue) ThrowOverflowException();
            result = (UInt256)v;
            return true;
        }
        if (typeof(TOther) == typeof(UInt256))
        {
            result = (UInt256)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(Int256))
        {
            var v = (Int256)(object)value;
            if (v.Sign < 0) ThrowOverflowException();
            result = (UInt256)v;
            return true;
        }

        result = default;
        return false;
    }

    private static bool TryConvertFromSaturating<TOther>(TOther value, out UInt256 result) where TOther : INumberBase<TOther>
    {
        if (typeof(TOther) == typeof(byte))
        {
            result = (byte)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(sbyte))
        {
            var v = (sbyte)(object)value;
            result = v < 0 ? Zero : (ulong)v;
            return true;
        }
        if (typeof(TOther) == typeof(ushort))
        {
            result = (ushort)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(short))
        {
            var v = (short)(object)value;
            result = v < 0 ? Zero : (ulong)v;
            return true;
        }
        if (typeof(TOther) == typeof(uint))
        {
            result = (uint)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(int))
        {
            var v = (int)(object)value;
            result = v < 0 ? Zero : (ulong)v;
            return true;
        }
        if (typeof(TOther) == typeof(ulong))
        {
            result = (ulong)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(long))
        {
            var v = (long)(object)value;
            result = v < 0 ? Zero : (ulong)v;
            return true;
        }
        if (typeof(TOther) == typeof(UInt128))
        {
            var v = (UInt128)(object)value;
            result = new UInt256((ulong)v, (ulong)(v >> 64), 0, 0);
            return true;
        }
        if (typeof(TOther) == typeof(Int128))
        {
            var v = (Int128)(object)value;
            result = v < 0 ? Zero : new UInt256((ulong)v, (ulong)(v >> 64), 0, 0);
            return true;
        }
        if (typeof(TOther) == typeof(nuint))
        {
            result = (nuint)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(nint))
        {
            var v = (nint)(object)value;
            result = v < 0 ? Zero : (ulong)v;
            return true;
        }
        if (typeof(TOther) == typeof(Half))
        {
            var v = (double)(Half)(object)value;
            result = (v < 0 || double.IsNaN(v) || double.IsNegativeInfinity(v))
                ? Zero
                : double.IsPositiveInfinity(v) ? MaxValue : (UInt256)v;
            return true;
        }
        if (typeof(TOther) == typeof(float))
        {
            var v = (float)(object)value;
            result = (v < 0 || float.IsNaN(v) || float.IsNegativeInfinity(v))
                ? Zero
                : float.IsPositiveInfinity(v) ? MaxValue : (UInt256)(double)v;
            return true;
        }
        if (typeof(TOther) == typeof(double))
        {
            var v = (double)(object)value;
            result = (v < 0 || double.IsNaN(v) || double.IsNegativeInfinity(v))
                ? Zero
                : double.IsPositiveInfinity(v) ? MaxValue : (UInt256)v;
            return true;
        }
        if (typeof(TOther) == typeof(decimal))
        {
            var v = (decimal)(object)value;
            result = v < 0 ? Zero : (UInt256)new BigInteger(v);
            return true;
        }
        if (typeof(TOther) == typeof(BigInteger))
        {
            var v = (BigInteger)(object)value;
            result = v < 0 ? Zero : v > (BigInteger)MaxValue ? MaxValue : (UInt256)v;
            return true;
        }
        if (typeof(TOther) == typeof(UInt256))
        {
            result = (UInt256)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(Int256))
        {
            var v = (Int256)(object)value;
            result = v.Sign < 0 ? Zero : (UInt256)v;
            return true;
        }

        result = default;
        return false;
    }

    private static bool TryConvertFromTruncating<TOther>(TOther value, out UInt256 result) where TOther : INumberBase<TOther>
    {
        if (typeof(TOther) == typeof(byte))
        {
            result = (byte)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(sbyte))
        {
            var v = (sbyte)(object)value;
            result = (ulong)unchecked((byte)v);
            return true;
        }
        if (typeof(TOther) == typeof(ushort))
        {
            result = (ushort)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(short))
        {
            var v = (short)(object)value;
            result = (ulong)unchecked((ushort)v);
            return true;
        }
        if (typeof(TOther) == typeof(uint))
        {
            result = (uint)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(int))
        {
            var v = (int)(object)value;
            result = (ulong)unchecked((uint)v);
            return true;
        }
        if (typeof(TOther) == typeof(ulong))
        {
            result = (ulong)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(long))
        {
            var v = (long)(object)value;
            result = unchecked((ulong)v);
            return true;
        }
        if (typeof(TOther) == typeof(UInt128))
        {
            var v = (UInt128)(object)value;
            result = new UInt256((ulong)v, (ulong)(v >> 64), 0, 0);
            return true;
        }
        if (typeof(TOther) == typeof(Int128))
        {
            var v = (Int128)(object)value;
            result = new UInt256((ulong)v, (ulong)(v >> 64), 0, 0);
            return true;
        }
        if (typeof(TOther) == typeof(nuint))
        {
            result = (nuint)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(nint))
        {
            var v = (nint)(object)value;
            result = unchecked((ulong)v);
            return true;
        }
        if (typeof(TOther) == typeof(Half))
        {
            var v = (double)(Half)(object)value;
            result = (v < 0 || double.IsNaN(v) || double.IsNegativeInfinity(v))
                ? Zero
                : (double.IsPositiveInfinity(v) ? MaxValue : (UInt256)v);
            return true;
        }
        if (typeof(TOther) == typeof(float))
        {
            var v = (float)(object)value;
            result = (v < 0 || float.IsNaN(v) || float.IsNegativeInfinity(v))
                ? Zero
                : (float.IsPositiveInfinity(v) ? MaxValue : (UInt256)(double)v);
            return true;
        }
        if (typeof(TOther) == typeof(double))
        {
            var v = (double)(object)value;
            result = (v < 0 || double.IsNaN(v) || double.IsNegativeInfinity(v))
                ? Zero
                : (double.IsPositiveInfinity(v) ? MaxValue : (UInt256)v);
            return true;
        }
        if (typeof(TOther) == typeof(decimal))
        {
            var v = (decimal)(object)value;
            result = v < 0 ? Zero : (UInt256)new BigInteger(v);
            return true;
        }
        if (typeof(TOther) == typeof(BigInteger))
        {
            var v = (BigInteger)(object)value;
            // For truncating, we take the least significant 256 bits
            var bytes = v.ToByteArray();
            if (bytes.Length >= 32)
            {
                result = new UInt256(bytes.AsSpan()[..32], isBigEndian: false);
            }
            else
            {
                Span<byte> fullBytes = stackalloc byte[32];
                bytes.AsSpan().CopyTo(fullBytes);
                result = new UInt256(fullBytes, isBigEndian: false);
            }
            return true;
        }
        if (typeof(TOther) == typeof(UInt256))
        {
            result = (UInt256)(object)value;
            return true;
        }
        if (typeof(TOther) == typeof(Int256))
        {
            var v = (Int256)(object)value;
            result = (UInt256)v;
            return true;
        }

        result = default;
        return false;
    }

    private static bool TryConvertToChecked<TOther>(UInt256 value, [MaybeNullWhen(false)] out TOther result) where TOther : INumberBase<TOther>
    {
        if (typeof(TOther) == typeof(byte))
        {
            if (value.u1 != 0 || value.u2 != 0 || value.u3 != 0 || value.u0 > byte.MaxValue)
                ThrowOverflowException();
            result = (TOther)(object)(byte)value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(sbyte))
        {
            if (value.u1 != 0 || value.u2 != 0 || value.u3 != 0 || value.u0 > (ulong)sbyte.MaxValue)
                ThrowOverflowException();
            result = (TOther)(object)(sbyte)value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(ushort))
        {
            if (value.u1 != 0 || value.u2 != 0 || value.u3 != 0 || value.u0 > ushort.MaxValue)
                ThrowOverflowException();
            result = (TOther)(object)(ushort)value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(short))
        {
            if (value.u1 != 0 || value.u2 != 0 || value.u3 != 0 || value.u0 > (ulong)short.MaxValue)
                ThrowOverflowException();
            result = (TOther)(object)(short)value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(uint))
        {
            if (value.u1 != 0 || value.u2 != 0 || value.u3 != 0 || value.u0 > uint.MaxValue)
                ThrowOverflowException();
            result = (TOther)(object)(uint)value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(int))
        {
            if (value.u1 != 0 || value.u2 != 0 || value.u3 != 0 || value.u0 > (ulong)int.MaxValue)
                ThrowOverflowException();
            result = (TOther)(object)(int)value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(ulong))
        {
            if (value.u1 != 0 || value.u2 != 0 || value.u3 != 0)
                ThrowOverflowException();
            result = (TOther)(object)value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(long))
        {
            if (value.u1 != 0 || value.u2 != 0 || value.u3 != 0 || value.u0 > (ulong)long.MaxValue)
                ThrowOverflowException();
            result = (TOther)(object)(long)value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(UInt128))
        {
            if (value.u2 != 0 || value.u3 != 0)
                ThrowOverflowException();
            result = (TOther)(object)(new UInt128(value.u1, value.u0));
            return true;
        }
        if (typeof(TOther) == typeof(Int128))
        {
            if (value.u2 != 0 || value.u3 != 0 || value.u1 > (ulong)long.MaxValue)
                ThrowOverflowException();
            result = (TOther)(object)(new Int128(value.u1, value.u0));
            return true;
        }
        if (typeof(TOther) == typeof(nuint))
        {
            if (value.u1 != 0 || value.u2 != 0 || value.u3 != 0 || value.u0 > (ulong)nuint.MaxValue)
                ThrowOverflowException();
            result = (TOther)(object)(nuint)value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(nint))
        {
            if (value.u1 != 0 || value.u2 != 0 || value.u3 != 0) ThrowOverflowException();
            result = (TOther)(object)checked((nint)value.u0);
            return true;
        }
        if (typeof(TOther) == typeof(Half))
        {
            result = (TOther)(object)(Half)(double)value;
            return true;
        }
        if (typeof(TOther) == typeof(float))
        {
            result = (TOther)(object)(float)(double)value;
            return true;
        }
        if (typeof(TOther) == typeof(double))
        {
            result = (TOther)(object)(double)value;
            return true;
        }
        if (typeof(TOther) == typeof(decimal))
        {
            result = (TOther)(object)(decimal)value;
            return true;
        }
        if (typeof(TOther) == typeof(BigInteger))
        {
            result = (TOther)(object)(BigInteger)value;
            return true;
        }

        result = default;
        return false;
    }

    private static bool TryConvertToSaturating<TOther>(UInt256 value, [MaybeNullWhen(false)] out TOther result) where TOther : INumberBase<TOther>
    {
        if (typeof(TOther) == typeof(byte))
        {
            result = (TOther)(object)(((value.u1 | value.u2 | value.u3) != 0 || value.u0 > byte.MaxValue) ? byte.MaxValue : (byte)value.u0);
            return true;
        }
        if (typeof(TOther) == typeof(sbyte))
        {
            result = (TOther)(object)(((value.u1 | value.u2 | value.u3) != 0 || value.u0 > (ulong)sbyte.MaxValue) ? sbyte.MaxValue : (sbyte)value.u0);
            return true;
        }
        if (typeof(TOther) == typeof(ushort))
        {
            result = (TOther)(object)(((value.u1 | value.u2 | value.u3) != 0 || value.u0 > ushort.MaxValue) ? ushort.MaxValue : (ushort)value.u0);
            return true;
        }
        if (typeof(TOther) == typeof(short))
        {
            result = (TOther)(object)(((value.u1 | value.u2 | value.u3) != 0 || value.u0 > (ulong)short.MaxValue) ? short.MaxValue : (short)value.u0);
            return true;
        }
        if (typeof(TOther) == typeof(uint))
        {
            result = (TOther)(object)(((value.u1 | value.u2 | value.u3) != 0 || value.u0 > uint.MaxValue) ? uint.MaxValue : (uint)value.u0);
            return true;
        }
        if (typeof(TOther) == typeof(int))
        {
            result = (TOther)(object)(((value.u1 | value.u2 | value.u3) != 0 || value.u0 > (ulong)int.MaxValue) ? int.MaxValue : (int)value.u0);
            return true;
        }
        if (typeof(TOther) == typeof(ulong))
        {
            result = (TOther)(object)(((value.u1 | value.u2 | value.u3) != 0) ? ulong.MaxValue : value.u0);
            return true;
        }
        if (typeof(TOther) == typeof(long))
        {
            result = (TOther)(object)(((value.u1 | value.u2 | value.u3) != 0 || value.u0 > (ulong)long.MaxValue) ? long.MaxValue : (long)value.u0);
            return true;
        }
        if (typeof(TOther) == typeof(UInt128))
        {
            result = (TOther)(object)(((value.u2 | value.u3) != 0) ? UInt128.MaxValue : new UInt128(value.u1, value.u0));
            return true;
        }
        if (typeof(TOther) == typeof(Int128))
        {
            result = (value.u2 | value.u3) != 0 || value.u1 > (ulong)long.MaxValue
                ? (TOther)(object)Int128.MaxValue
                : (TOther)(object)(new Int128(value.u1, value.u0));
            return true;
        }
        if (typeof(TOther) == typeof(nuint))
        {
            result = (TOther)(object)(((value.u1 | value.u2 | value.u3) != 0 || value.u0 > (ulong)nuint.MaxValue) ? nuint.MaxValue : (nuint)value.u0);
            return true;
        }
        if (typeof(TOther) == typeof(nint))
        {
            result = (TOther)(object)(((value.u1 | value.u2 | value.u3) != 0 || value.u0 > (ulong)nint.MaxValue) ? nint.MaxValue : (nint)value.u0);
            return true;
        }
        if (typeof(TOther) == typeof(Half))
        {
            result = (TOther)(object)(Half)(double)value;
            return true;
        }
        if (typeof(TOther) == typeof(float))
        {
            result = (TOther)(object)(float)(double)value;
            return true;
        }
        if (typeof(TOther) == typeof(double))
        {
            result = (TOther)(object)(double)value;
            return true;
        }
        if (typeof(TOther) == typeof(decimal))
        {
            result = (TOther)(object)(decimal)value;
            return true;
        }
        if (typeof(TOther) == typeof(BigInteger))
        {
            result = (TOther)(object)(BigInteger)value;
            return true;
        }

        result = default;
        return false;
    }

    private static bool TryConvertToTruncating<TOther>(UInt256 value, [MaybeNullWhen(false)] out TOther result) where TOther : INumberBase<TOther>
    {
        if (typeof(TOther) == typeof(byte))
        {
            result = (TOther)(object)(byte)value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(sbyte))
        {
            result = (TOther)(object)(sbyte)value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(ushort))
        {
            result = (TOther)(object)(ushort)value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(short))
        {
            result = (TOther)(object)(short)value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(uint))
        {
            result = (TOther)(object)(uint)value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(int))
        {
            result = (TOther)(object)(int)value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(ulong))
        {
            result = (TOther)(object)value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(long))
        {
            result = (TOther)(object)(long)value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(UInt128))
        {
            result = (TOther)(object)(new UInt128(value.u1, value.u0));
            return true;
        }
        if (typeof(TOther) == typeof(Int128))
        {
            result = (TOther)(object)(new Int128(value.u1, value.u0));
            return true;
        }
        if (typeof(TOther) == typeof(nuint))
        {
            result = (TOther)(object)(nuint)value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(nint))
        {
            result = (TOther)(object)(nint)value.u0;
            return true;
        }
        if (typeof(TOther) == typeof(Half))
        {
            result = (TOther)(object)(Half)(double)value;
            return true;
        }
        if (typeof(TOther) == typeof(float))
        {
            result = (TOther)(object)(float)(double)value;
            return true;
        }
        if (typeof(TOther) == typeof(double))
        {
            result = (TOther)(object)(double)value;
            return true;
        }
        if (typeof(TOther) == typeof(decimal))
        {
            result = (TOther)(object)(decimal)value;
            return true;
        }
        if (typeof(TOther) == typeof(BigInteger))
        {
            result = (TOther)(object)(BigInteger)value;
            return true;
        }

        result = default;
        return false;
    }

    [OverloadResolutionPriority(1)]
    public static UInt256 Clamp(in UInt256 value, in UInt256 min, in UInt256 max)
    {
        if (min > max)
            ThrowMinMaxException(min, max);
        if (value < min)
            return min;
        if (value > max)
            return max;
        return value;
    }

    /// <inheritdoc />
    public static UInt256 Clamp(UInt256 value, UInt256 min, UInt256 max)
        => Clamp(in value, in min, in max);

    [DoesNotReturn]
    private static void ThrowMinMaxException(UInt256 min, UInt256 max)
        => throw new ArgumentException($"'{min}' cannot be greater than '{max}'.");

    /// <inheritdoc />
    public static UInt256 CopySign(UInt256 value, UInt256 sign) => value;

    /// <inheritdoc />
    public static int Sign(UInt256 value) => value.IsZero ? 0 : 1;

    /// <inheritdoc />
    [OverloadResolutionPriority(1)]
    public static UInt256 operator %(in UInt256 left, in UInt256 right)
    {
        Mod(in left, in right, out UInt256 result);
        return result;
    }

    /// <inheritdoc />
    public static UInt256 operator %(UInt256 left, UInt256 right)
    {
        Mod(in left, in right, out UInt256 result);
        return result;
    }

    /// <inheritdoc />
    [OverloadResolutionPriority(1)]
    public static UInt256 operator --(in UInt256 value)
    {
        Subtract(in value, One, out UInt256 result);
        return result;
    }

    /// <inheritdoc />
    public static UInt256 operator --(UInt256 value)
    {
        Subtract(in value, One, out UInt256 result);
        return result;
    }

    /// <inheritdoc />
    public static UInt256 operator +(UInt256 value) => value;

    /// <inheritdoc />
    public static UInt256 operator -(UInt256 value)
    {
        // For unsigned 256-bit values, unary minus is defined as two's complement: ~value + 1
        return ~value + One;
    }

    /// <inheritdoc />
    public static (UInt256 Quotient, UInt256 Remainder) DivRem(UInt256 left, UInt256 right)
    {
        Divide(in left, in right, out UInt256 quotient);
        Mod(in left, in right, out UInt256 remainder);
        return (quotient, remainder);
    }

    [OverloadResolutionPriority(1)]
    public static uint LeadingZeroCount(in UInt256 value)
        => value.LeadingZeroCount();

    /// <inheritdoc />
    public static UInt256 LeadingZeroCount(UInt256 value)
        => (UInt256)value.LeadingZeroCount();

    /// <inheritdoc />
    public static UInt256 PopCount(UInt256 value) =>
        (ulong)(BitOperations.PopCount(value.u0) +
               BitOperations.PopCount(value.u1) +
               BitOperations.PopCount(value.u2) +
               BitOperations.PopCount(value.u3));

    /// <inheritdoc />
    public static UInt256 TrailingZeroCount(UInt256 value)
    {
        if (value.u0 != 0) return (ulong)BitOperations.TrailingZeroCount(value.u0);
        if (value.u1 != 0) return (ulong)(64 + BitOperations.TrailingZeroCount(value.u1));
        if (value.u2 != 0) return (ulong)(128 + BitOperations.TrailingZeroCount(value.u2));
        if (value.u3 != 0) return (ulong)(192 + BitOperations.TrailingZeroCount(value.u3));
        return 256ul;
    }

    /// <inheritdoc />
    public static bool TryReadBigEndian(ReadOnlySpan<byte> source, bool isUnsigned, out UInt256 value)
    {
        if (source.Length < 32)
        {
            value = default;
            return false;
        }

        if (!isUnsigned && (source[0] & 0x80) != 0)
        {
            value = default;
            return false;
        }

        value = new UInt256(source[..32], isBigEndian: true);
        return true;
    }

    /// <inheritdoc />
    public static bool TryReadLittleEndian(ReadOnlySpan<byte> source, bool isUnsigned, out UInt256 value)
    {
        if (source.Length < 32)
        {
            value = default;
            return false;
        }

        if (!isUnsigned && (source[31] & 0x80) != 0)
        {
            value = default;
            return false;
        }

        value = new UInt256(source[..32], isBigEndian: false);
        return true;
    }

    /// <inheritdoc />
    public int GetByteCount() => 32;

    /// <inheritdoc />
    public int GetShortestBitLength() => BitLen;

    /// <inheritdoc />
    public bool TryWriteBigEndian(Span<byte> destination, out int bytesWritten)
    {
        if (destination.Length < 32)
        {
            bytesWritten = 0;
            return false;
        }

        ToBigEndian(destination[..32]);
        bytesWritten = 32;
        return true;
    }

    /// <inheritdoc />
    public bool TryWriteLittleEndian(Span<byte> destination, out int bytesWritten)
    {
        if (destination.Length < 32)
        {
            bytesWritten = 0;
            return false;
        }

        ToLittleEndian(destination[..32]);
        bytesWritten = 32;
        return true;
    }

    /// <inheritdoc />
    static UInt256 IBinaryInteger<UInt256>.RotateLeft(UInt256 value, int rotateAmount)
    {
        rotateAmount &= 255;
        if (rotateAmount == 0) return value;
        Lsh(in value, rotateAmount, out UInt256 left);
        Rsh(in value, 256 - rotateAmount, out UInt256 right);
        return left | right;
    }

    /// <inheritdoc />
    static UInt256 IBinaryInteger<UInt256>.RotateRight(UInt256 value, int rotateAmount)
    {
        rotateAmount &= 255;
        if (rotateAmount == 0) return value;
        Rsh(in value, rotateAmount, out UInt256 right);
        Lsh(in value, 256 - rotateAmount, out UInt256 left);
        return right | left;
    }

    /// <inheritdoc />
    static bool IBinaryNumber<UInt256>.IsPow2(UInt256 value)
    {
        int popCount = BitOperations.PopCount(value.u0) +
                      BitOperations.PopCount(value.u1) +
                      BitOperations.PopCount(value.u2) +
                      BitOperations.PopCount(value.u3);
        return popCount == 1;
    }

    /// <inheritdoc />
    static UInt256 IBinaryNumber<UInt256>.Log2(UInt256 value)
    {
        if (value.IsZero) throw new ArgumentException("Cannot compute Log2 of zero");
        return (ulong)(255 - (int)(ulong)LeadingZeroCount(value));
    }

    /// <inheritdoc />
    public static UInt256 operator >>>(UInt256 value, int shiftAmount)
    {
        Rsh(in value, shiftAmount, out UInt256 result);
        return result;
    }

    /// <inheritdoc />
    public bool TryFormat(Span<char> destination, out int charsWritten, ReadOnlySpan<char> format, IFormatProvider? provider)
    {
        var bigInt = (BigInteger)this;
        return bigInt.TryFormat(destination, out charsWritten, format, provider);
    }

    /// <inheritdoc />
    public string ToString(string? format, IFormatProvider? formatProvider)
        => ((BigInteger)this).ToString(format, formatProvider);

    /// <inheritdoc />
    static UInt256 IMinMaxValue<UInt256>.MinValue => MinValue;

    /// <inheritdoc />
    static UInt256 IMinMaxValue<UInt256>.MaxValue => MaxValue;
}
