// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Globalization;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics.Arm;
using System.Runtime.Intrinsics.X86;

namespace Nethermind.Int256;

/// <summary>Selects how a conversion treats values outside the target range.</summary>
internal enum ConversionMode
{
    Checked,
    Saturating,
    Truncating,
}

// Generic math. The interfaces take operands by value and the public operators take them by `in`, so the
// interface members are explicit implementations that forward; public by-value overloads would rebind
// every existing caller. Unchecked operators keep the public operators' semantics (subtraction throws on
// underflow, addition and multiplication wrap); checked operators throw on any overflow.
public readonly partial struct UInt256 : IBinaryInteger<UInt256>, IMinMaxValue<UInt256>, IUnsignedNumber<UInt256>
{
    /// <summary>The remainder of <paramref name="a"/> divided by <paramref name="b"/>.</summary>
    /// <exception cref="DivideByZeroException"><paramref name="b"/> is zero.</exception>
    public static UInt256 operator %(in UInt256 a, in UInt256 b)
    {
        Mod(in a, in b, out UInt256 res);
        return res;
    }

    /// <summary>Decrements <paramref name="a"/>; like subtraction, throws rather than wrapping below zero.</summary>
    /// <exception cref="OverflowException"><paramref name="a"/> is zero.</exception>
    public static UInt256 operator --(in UInt256 a)
    {
        if (a.IsZero) ThrowOverflowException();
        Subtract(in a, new UInt256(1ul), out UInt256 res);
        return res;
    }

    static UInt256 IAdditiveIdentity<UInt256, UInt256>.AdditiveIdentity => default;

    static UInt256 IMultiplicativeIdentity<UInt256, UInt256>.MultiplicativeIdentity => new(1ul);

    static UInt256 IMinMaxValue<UInt256>.MinValue => default;

    static UInt256 IMinMaxValue<UInt256>.MaxValue => new(ulong.MaxValue, ulong.MaxValue, ulong.MaxValue, ulong.MaxValue);

    static UInt256 INumberBase<UInt256>.One => new(1ul);

    static UInt256 INumberBase<UInt256>.Zero => default;

    static int INumberBase<UInt256>.Radix => 2;

    // Operators. Checked subtraction, decrement, negation and division keep the interface defaults, which
    // call the unchecked operators: those already throw on underflow or a zero divisor.

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static UInt256 IAdditionOperators<UInt256, UInt256, UInt256>.operator +(UInt256 left, UInt256 right)
    {
        AddValues(in left, in right, out UInt256 res, detectOverflow: false);
        return res;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static UInt256 IAdditionOperators<UInt256, UInt256, UInt256>.operator checked +(UInt256 left, UInt256 right)
    {
        if (AddValues(in left, in right, out UInt256 res, detectOverflow: true)) ThrowOverflowException();
        return res;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static UInt256 ISubtractionOperators<UInt256, UInt256, UInt256>.operator -(UInt256 left, UInt256 right)
    {
        if (SubtractValues(in left, in right, out UInt256 res)) ThrowOverflowException();
        return res;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static UInt256 IMultiplyOperators<UInt256, UInt256, UInt256>.operator *(UInt256 left, UInt256 right)
    {
        UInt256 x = new(left.u0, left.u1, left.u2, left.u3), y = new(right.u0, right.u1, right.u2, right.u3);
        MultiplyValues(in x, in y, out UInt256 res);
        return res;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static UInt256 IMultiplyOperators<UInt256, UInt256, UInt256>.operator checked *(UInt256 left, UInt256 right)
    {
        if (MultiplyOverflow(in left, in right, out UInt256 res)) ThrowOverflowException();
        return res;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static UInt256 IDivisionOperators<UInt256, UInt256, UInt256>.operator /(UInt256 left, UInt256 right) => left / right;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static UInt256 IModulusOperators<UInt256, UInt256, UInt256>.operator %(UInt256 left, UInt256 right) => left % right;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static UInt256 IIncrementOperators<UInt256>.operator ++(UInt256 value) => ++value;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static UInt256 IIncrementOperators<UInt256>.operator checked ++(UInt256 value)
    {
        if ((value.u0 & value.u1 & value.u2 & value.u3) == ulong.MaxValue) ThrowOverflowException();
        return ++value;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static UInt256 IDecrementOperators<UInt256>.operator --(UInt256 value) => --value;

    static UInt256 IUnaryPlusOperators<UInt256, UInt256>.operator +(UInt256 value) => value;

    /// <summary>Only zero has an unsigned negation; anything else throws, as <c>0 - value</c> does.</summary>
    static UInt256 IUnaryNegationOperators<UInt256, UInt256>.operator -(UInt256 value)
    {
        if (!value.IsZero) ThrowOverflowException();
        return default;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool IEqualityOperators<UInt256, UInt256, bool>.operator ==(UInt256 left, UInt256 right) => left == right;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool IEqualityOperators<UInt256, UInt256, bool>.operator !=(UInt256 left, UInt256 right) => left != right;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool IComparisonOperators<UInt256, UInt256, bool>.operator <(UInt256 left, UInt256 right) => left < right;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool IComparisonOperators<UInt256, UInt256, bool>.operator <=(UInt256 left, UInt256 right) => left <= right;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool IComparisonOperators<UInt256, UInt256, bool>.operator >(UInt256 left, UInt256 right) => left > right;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool IComparisonOperators<UInt256, UInt256, bool>.operator >=(UInt256 left, UInt256 right) => left >= right;

    // INumberBase

    static UInt256 INumberBase<UInt256>.Abs(UInt256 value) => value;

    static bool INumberBase<UInt256>.IsCanonical(UInt256 value) => true;

    static bool INumberBase<UInt256>.IsComplexNumber(UInt256 value) => false;

    static bool INumberBase<UInt256>.IsEvenInteger(UInt256 value) => (value.u0 & 1) == 0;

    static bool INumberBase<UInt256>.IsFinite(UInt256 value) => true;

    static bool INumberBase<UInt256>.IsImaginaryNumber(UInt256 value) => false;

    static bool INumberBase<UInt256>.IsInfinity(UInt256 value) => false;

    static bool INumberBase<UInt256>.IsInteger(UInt256 value) => true;

    static bool INumberBase<UInt256>.IsNaN(UInt256 value) => false;

    static bool INumberBase<UInt256>.IsNegative(UInt256 value) => false;

    static bool INumberBase<UInt256>.IsNegativeInfinity(UInt256 value) => false;

    static bool INumberBase<UInt256>.IsNormal(UInt256 value) => !value.IsZero;

    static bool INumberBase<UInt256>.IsOddInteger(UInt256 value) => (value.u0 & 1) != 0;

    static bool INumberBase<UInt256>.IsPositive(UInt256 value) => true;

    static bool INumberBase<UInt256>.IsPositiveInfinity(UInt256 value) => false;

    static bool INumberBase<UInt256>.IsRealNumber(UInt256 value) => true;

    static bool INumberBase<UInt256>.IsSubnormal(UInt256 value) => false;

    static bool INumberBase<UInt256>.IsZero(UInt256 value) => value.IsZero;

    static UInt256 INumberBase<UInt256>.MaxMagnitude(UInt256 x, UInt256 y) => Max(in x, in y);

    static UInt256 INumberBase<UInt256>.MaxMagnitudeNumber(UInt256 x, UInt256 y) => Max(in x, in y);

    static UInt256 INumberBase<UInt256>.MinMagnitude(UInt256 x, UInt256 y) => Min(in x, in y);

    static UInt256 INumberBase<UInt256>.MinMagnitudeNumber(UInt256 x, UInt256 y) => Min(in x, in y);

    static UInt256 INumberBase<UInt256>.MultiplyAddEstimate(UInt256 left, UInt256 right, UInt256 addend) => left * right + addend;

    // INumber

    static UInt256 INumber<UInt256>.Clamp(UInt256 value, UInt256 min, UInt256 max)
    {
        if (min > max) ThrowMinMaxException(min, max);
        return value < min ? min : value > max ? max : value;
    }

    static UInt256 INumber<UInt256>.CopySign(UInt256 value, UInt256 sign) => value;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static UInt256 INumber<UInt256>.Max(UInt256 x, UInt256 y) => Max(in x, in y);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static UInt256 INumber<UInt256>.MaxNumber(UInt256 x, UInt256 y) => Max(in x, in y);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static UInt256 INumber<UInt256>.Min(UInt256 x, UInt256 y) => Min(in x, in y);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static UInt256 INumber<UInt256>.MinNumber(UInt256 x, UInt256 y) => Min(in x, in y);

    static int INumber<UInt256>.Sign(UInt256 value) => value.IsZero ? 0 : 1;

    // IBinaryInteger. Shifts keep the public operators' EVM semantics: a count of 256 or more gives zero rather
    // than being masked to the width, as it is for the BCL integers. Rotation is modular.

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static UInt256 IBitwiseOperators<UInt256, UInt256, UInt256>.operator &(UInt256 left, UInt256 right) => left & right;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static UInt256 IBitwiseOperators<UInt256, UInt256, UInt256>.operator |(UInt256 left, UInt256 right) => left | right;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static UInt256 IBitwiseOperators<UInt256, UInt256, UInt256>.operator ^(UInt256 left, UInt256 right) => left ^ right;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static UInt256 IBitwiseOperators<UInt256, UInt256, UInt256>.operator ~(UInt256 value) => ~value;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static UInt256 IShiftOperators<UInt256, int, UInt256>.operator <<(UInt256 value, int shiftAmount) => value << shiftAmount;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static UInt256 IShiftOperators<UInt256, int, UInt256>.operator >>(UInt256 value, int shiftAmount) => value >> shiftAmount;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static UInt256 IShiftOperators<UInt256, int, UInt256>.operator >>>(UInt256 value, int shiftAmount) => value >> shiftAmount;

    static UInt256 IBinaryNumber<UInt256>.AllBitsSet => new(ulong.MaxValue, ulong.MaxValue, ulong.MaxValue, ulong.MaxValue);

    static bool IBinaryNumber<UInt256>.IsPow2(UInt256 value) => PopCount(in value) == 1;

    static UInt256 IBinaryNumber<UInt256>.Log2(UInt256 value) => new((ulong)(value.IsZero ? 0 : value.BitLen - 1));

    static (UInt256 Quotient, UInt256 Remainder) IBinaryInteger<UInt256>.DivRem(UInt256 left, UInt256 right)
    {
        DivRem(in left, in right, out UInt256 quotient, out UInt256 remainder);
        return (quotient, remainder);
    }

    static UInt256 IBinaryInteger<UInt256>.LeadingZeroCount(UInt256 value) => new((ulong)(256 - value.BitLen));

    static UInt256 IBinaryInteger<UInt256>.PopCount(UInt256 value) => new((ulong)PopCount(in value));

    static UInt256 IBinaryInteger<UInt256>.TrailingZeroCount(UInt256 value) => new((ulong)TrailingZeroCount(in value));

    static UInt256 IBinaryInteger<UInt256>.RotateLeft(UInt256 value, int rotateAmount) => RotateLeft(in value, rotateAmount);

    static UInt256 IBinaryInteger<UInt256>.RotateRight(UInt256 value, int rotateAmount) => RotateLeft(in value, -rotateAmount);

    int IBinaryInteger<UInt256>.GetByteCount() => 32;

    int IBinaryInteger<UInt256>.GetShortestBitLength() => BitLen;

    static bool IBinaryInteger<UInt256>.TryReadBigEndian(ReadOnlySpan<byte> source, bool isUnsigned, out UInt256 value) =>
        TryReadBytes(source, isBigEndian: true, isUnsigned, signedTarget: false, out value);

    static bool IBinaryInteger<UInt256>.TryReadLittleEndian(ReadOnlySpan<byte> source, bool isUnsigned, out UInt256 value) =>
        TryReadBytes(source, isBigEndian: false, isUnsigned, signedTarget: false, out value);

    bool IBinaryInteger<UInt256>.TryWriteBigEndian(Span<byte> destination, out int bytesWritten) =>
        TryWriteBytes(in this, destination, isBigEndian: true, out bytesWritten);

    bool IBinaryInteger<UInt256>.TryWriteLittleEndian(Span<byte> destination, out int bytesWritten) =>
        TryWriteBytes(in this, destination, isBigEndian: false, out bytesWritten);

    // The interface's instance defaults would box a struct receiver, so the writers are implemented here.

    int IBinaryInteger<UInt256>.WriteBigEndian(byte[] destination) => WriteBytes(in this, destination, isBigEndian: true);

    int IBinaryInteger<UInt256>.WriteBigEndian(byte[] destination, int startIndex) =>
        WriteBytes(in this, destination.AsSpan(startIndex), isBigEndian: true);

    int IBinaryInteger<UInt256>.WriteBigEndian(Span<byte> destination) => WriteBytes(in this, destination, isBigEndian: true);

    int IBinaryInteger<UInt256>.WriteLittleEndian(byte[] destination) => WriteBytes(in this, destination, isBigEndian: false);

    int IBinaryInteger<UInt256>.WriteLittleEndian(byte[] destination, int startIndex) =>
        WriteBytes(in this, destination.AsSpan(startIndex), isBigEndian: false);

    int IBinaryInteger<UInt256>.WriteLittleEndian(Span<byte> destination) => WriteBytes(in this, destination, isBigEndian: false);

    // Operands that arrive by value are copies the JIT can keep in registers, but only while every read of them takes
    // one shape. A kernel that reads both limbs and vectors puts them on the stack, and the vector store there does
    // not forward to the limb loads. AVX2 reads each operand as one Vector256 already; the 128-bit kernels and the
    // narrow-operand dispatch in front of them mix the two.

    /// <summary>Adds by-value operands; returns the carry out when <paramref name="detectOverflow"/>.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    internal static bool AddValues(in UInt256 a, in UInt256 b, out UInt256 res, bool detectOverflow)
    {
        if (!Avx2.IsSupported && (AdvSimd.IsSupported || Sse42.IsSupported))
        {
            return AddVector128(in a, in b, out res, detectOverflow, vectorOnly: true);
        }

        if (detectOverflow) return AddOverflow(in a, in b, out res);
        res = a + b;
        return false;
    }

    /// <summary>Subtracts by-value operands, wrapping; returns whether it borrowed out.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    internal static bool SubtractValues(in UInt256 a, in UInt256 b, out UInt256 res) =>
        !Avx2.IsSupported && (AdvSimd.IsSupported || Sse42.IsSupported)
            ? SubtractVector128(in a, in b, out res, vectorOnly: true)
            : SubtractUnderflow(in a, in b, out res);

    /// <summary>
    /// <see cref="Multiply(in UInt256, in UInt256, out UInt256)"/> for operands that arrive by value. Reading them
    /// only as limbs lets the JIT keep the copies in registers; the vector top-limb step would put them on the
    /// stack, where its 32-byte store does not forward to the limb loads.
    /// </summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    internal static void MultiplyValues(in UInt256 x, in UInt256 y, out UInt256 res)
    {
        ulong xTop = x.u2 | x.u3;
        ulong yTop = y.u2 | y.u3;
        ulong xHigh = x.u1 | xTop;
        ulong yHigh = y.u1 | yTop;
        if ((xHigh | yHigh) == 0)
        {
            ulong high = Multiply64(x.u0, y.u0, out ulong low);
            StoreProduct(out res, low, high, 0, 0);
        }
        else if (yHigh == 0) MultiplyByUInt64(in x, y.u0, out res);
        else if (xHigh == 0) MultiplyByUInt64(in y, x.u0, out res);
        else if ((xTop | yTop) == 0) MultiplyLimbs2x2(in x, in y, out res);
        else if (xTop == 0) MultiplyLimbs2x4(in x, in y, out res);
        else if (yTop == 0) MultiplyLimbs2x4(in y, in x, out res);
        else MultiplyLimbs4x4(in x, in y, out res, scalarTop: true);
    }

    /// <summary>Sets <paramref name="quotient"/> and <paramref name="remainder"/> from one division.</summary>
    /// <exception cref="DivideByZeroException"><paramref name="y"/> is zero.</exception>
    internal static void DivRem(in UInt256 x, in UInt256 y, out UInt256 quotient, out UInt256 remainder)
    {
        if (y.IsZero) ThrowDivideByZeroException();

        int order = x.CompareTo(in y);
        if (order <= 0)
        {
            // Copy x first: remainder may alias it.
            UInt256 dividend = x;
            quotient = new UInt256(order == 0 ? 1ul : 0ul);
            remainder = order == 0 ? default : dividend;
            return;
        }

        if (x.IsUint64)
        {
            // y < x, so it fits a limb too.
            ulong q = x.u0 / y.u0;
            ulong r = x.u0 - q * y.u0;
            quotient = new UInt256(q);
            remainder = new UInt256(r);
            return;
        }

        DivideImpl(in x, in y, out quotient, out remainder);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    internal static int PopCount(in UInt256 value) =>
        BitOperations.PopCount(value.u0) + BitOperations.PopCount(value.u1) + BitOperations.PopCount(value.u2) + BitOperations.PopCount(value.u3);

    internal static int TrailingZeroCount(in UInt256 value) =>
        value.u0 != 0 ? BitOperations.TrailingZeroCount(value.u0)
        : value.u1 != 0 ? 64 + BitOperations.TrailingZeroCount(value.u1)
        : value.u2 != 0 ? 128 + BitOperations.TrailingZeroCount(value.u2)
        : value.u3 != 0 ? 192 + BitOperations.TrailingZeroCount(value.u3)
        : 256;

    /// <summary>Rotates left by <paramref name="amount"/> modulo 256; a negative amount rotates right.</summary>
    internal static UInt256 RotateLeft(in UInt256 value, int amount)
    {
        int n = amount & 255;
        if (n == 0) return value;
        Lsh(in value, n, out UInt256 high);
        Rsh(in value, 256 - n, out UInt256 low);
        return high | low;
    }

    /// <summary>
    /// Reads two's complement bytes into 256 bits. Fails when the value does not fit: a negative source for an
    /// unsigned target, excess bytes that are not sign fill, or a signed target whose bit 255 disagrees with the
    /// source's sign.
    /// </summary>
    [SkipLocalsInit]
    internal static bool TryReadBytes(ReadOnlySpan<byte> source, bool isBigEndian, bool isUnsigned, bool signedTarget, out UInt256 value)
    {
        value = default;
        if (source.IsEmpty) return true;

        bool negative = !isUnsigned && (sbyte)(isBigEndian ? source[0] : source[^1]) < 0;
        if (negative && !signedTarget) return false;

        byte fill = negative ? (byte)0xFF : (byte)0;
        Span<byte> bytes = stackalloc byte[32];
        if (source.Length >= 32)
        {
            ReadOnlySpan<byte> excess = isBigEndian ? source[..^32] : source[32..];
            if (excess.ContainsAnyExcept(fill)) return false;
            (isBigEndian ? source[^32..] : source[..32]).CopyTo(bytes);
        }
        else
        {
            bytes.Fill(fill);
            source.CopyTo(isBigEndian ? bytes[(32 - source.Length)..] : bytes);
        }

        value = new UInt256(bytes, isBigEndian);
        return !signedTarget || (value.u3 >> 63 != 0) == negative;
    }

    internal static bool TryWriteBytes(in UInt256 value, Span<byte> destination, bool isBigEndian, out int bytesWritten)
    {
        if (destination.Length < 32)
        {
            bytesWritten = 0;
            return false;
        }

        if (isBigEndian) value.ToBigEndian(destination[..32]);
        else value.ToLittleEndian(destination[..32]);
        bytesWritten = 32;
        return true;
    }

    internal static int WriteBytes(in UInt256 value, Span<byte> destination, bool isBigEndian)
    {
        if (!TryWriteBytes(in value, destination, isBigEndian, out int bytesWritten))
        {
            throw new ArgumentException("Destination is too short.", nameof(destination));
        }

        return bytesWritten;
    }

    // Parsing. The span overload of the existing public TryParse takes the span by `in`, so these stay explicit.

    static UInt256 IParsable<UInt256>.Parse(string s, IFormatProvider? provider)
    {
        ArgumentNullException.ThrowIfNull(s);
        return ParseCore(s, NumberStyles.Integer, provider);
    }

    static bool IParsable<UInt256>.TryParse([NotNullWhen(true)] string? s, IFormatProvider? provider, out UInt256 result)
    {
        if (s is null)
        {
            result = default;
            return false;
        }

        return TryParseCore(s, NumberStyles.Integer, provider, out result);
    }

    static UInt256 ISpanParsable<UInt256>.Parse(ReadOnlySpan<char> s, IFormatProvider? provider) =>
        ParseCore(s, NumberStyles.Integer, provider);

    static bool ISpanParsable<UInt256>.TryParse(ReadOnlySpan<char> s, IFormatProvider? provider, out UInt256 result) =>
        TryParseCore(s, NumberStyles.Integer, provider, out result);

    static UInt256 INumberBase<UInt256>.Parse(string s, NumberStyles style, IFormatProvider? provider)
    {
        ArgumentNullException.ThrowIfNull(s);
        return ParseCore(s, style, provider);
    }

    static UInt256 INumberBase<UInt256>.Parse(ReadOnlySpan<char> s, NumberStyles style, IFormatProvider? provider) =>
        ParseCore(s, style, provider);

    static bool INumberBase<UInt256>.TryParse([NotNullWhen(true)] string? s, NumberStyles style, IFormatProvider? provider, out UInt256 result)
    {
        if (s is null)
        {
            result = default;
            return false;
        }

        return TryParseCore(s, style, provider, out result);
    }

    static bool INumberBase<UInt256>.TryParse(ReadOnlySpan<char> s, NumberStyles style, IFormatProvider? provider, out UInt256 result) =>
        TryParseCore(s, style, provider, out result);

    private static UInt256 ParseCore(ReadOnlySpan<char> s, NumberStyles style, IFormatProvider? provider) =>
        TryParseCore(s, style, provider, out UInt256 result) ? result : throw new FormatException();

    // Any hex style takes the limb parser: BigInteger would read a leading hex digit above 7 as a sign.
    private static bool TryParseCore(ReadOnlySpan<char> s, NumberStyles style, IFormatProvider? provider, out UInt256 result) =>
        (style & NumberStyles.AllowHexSpecifier) != 0
            ? TryParseHex(s, out result)
            : TryParse(s, style, provider!, out result);

    // Formatting

    /// <summary>
    /// Formats the value. Empty, <c>"D"</c> and <c>"G"</c> formats write the digits from the limbs, exactly as
    /// <see cref="ToString()"/>; other formats go through <see cref="BigInteger"/>.
    /// </summary>
    public string ToString([StringSyntax(StringSyntaxAttribute.NumericFormat)] string? format, IFormatProvider? provider) =>
        IsDecimalFormat(format) ? ToString() : ((BigInteger)this).ToString(format, provider);

    /// <inheritdoc cref="ToString(string?, IFormatProvider?)"/>
    public bool TryFormat(Span<char> destination, out int charsWritten,
        [StringSyntax(StringSyntaxAttribute.NumericFormat)] ReadOnlySpan<char> format = default, IFormatProvider? provider = null) =>
        IsDecimalFormat(format)
            ? TryFormatDecimal(in this, destination, out charsWritten, negative: false)
            : ((BigInteger)this).TryFormat(destination, out charsWritten, format, provider);

    /// <inheritdoc cref="ToString(string?, IFormatProvider?)"/>
    public bool TryFormat(Span<byte> utf8Destination, out int bytesWritten,
        [StringSyntax(StringSyntaxAttribute.NumericFormat)] ReadOnlySpan<char> format = default, IFormatProvider? provider = null) =>
        IsDecimalFormat(format)
            ? TryFormatDecimal(in this, utf8Destination, out bytesWritten, negative: false)
            : ((IUtf8SpanFormattable)(BigInteger)this).TryFormat(utf8Destination, out bytesWritten, format, provider);

    /// <summary>Whether <paramref name="format"/> means plain decimal digits: empty, or <c>D</c> or <c>G</c> without a precision.</summary>
    internal static bool IsDecimalFormat(ReadOnlySpan<char> format) =>
        format.Length == 0 || (format.Length == 1 && (char)(format[0] | 0x20) is 'd' or 'g');

    /// <summary>Writes the decimal digits of <paramref name="magnitude"/>, after a '-' when <paramref name="negative"/>.</summary>
    [SkipLocalsInit]
    internal static bool TryFormatDecimal(in UInt256 magnitude, Span<char> destination, out int written, bool negative)
    {
        Span<char> buffer = stackalloc char[MaxDecimalDigits + 1];
        ReadOnlySpan<char> text = FormatDecimal(in magnitude, buffer, negative);
        if (text.TryCopyTo(destination))
        {
            written = text.Length;
            return true;
        }

        written = 0;
        return false;
    }

    /// <inheritdoc cref="TryFormatDecimal(in UInt256, Span{char}, out int, bool)"/>
    [SkipLocalsInit]
    internal static bool TryFormatDecimal(in UInt256 magnitude, Span<byte> destination, out int written, bool negative)
    {
        Span<char> buffer = stackalloc char[MaxDecimalDigits + 1];
        ReadOnlySpan<char> text = FormatDecimal(in magnitude, buffer, negative);
        if (text.Length > destination.Length)
        {
            written = 0;
            return false;
        }

        // ASCII digits and '-' narrow one to one.
        for (int i = 0; i < text.Length; i++)
        {
            destination[i] = (byte)text[i];
        }

        written = text.Length;
        return true;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ReadOnlySpan<char> FormatDecimal(in UInt256 magnitude, Span<char> buffer, bool negative)
    {
        int position = WriteDecimalDigits(in magnitude, buffer);
        if (negative)
        {
            buffer[--position] = '-';
        }

        return buffer[position..];
    }

    // Conversions. The BCL types do not know these types, so both directions cover every primitive here.

    /// <inheritdoc cref="INumberBase{TSelf}.CreateChecked{TOther}(TOther)"/>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static UInt256 CreateChecked<TOther>(TOther value) where TOther : INumberBase<TOther>
    {
        UInt256 result;
        if (typeof(TOther) == typeof(UInt256))
        {
            result = (UInt256)(object)value;
        }
        else if (!TryConvertFrom(value, ConversionMode.Checked, out result) && !TOther.TryConvertToChecked(value, out result))
        {
            ThrowNotSupportedException();
        }

        return result;
    }

    /// <inheritdoc cref="INumberBase{TSelf}.CreateSaturating{TOther}(TOther)"/>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static UInt256 CreateSaturating<TOther>(TOther value) where TOther : INumberBase<TOther>
    {
        UInt256 result;
        if (typeof(TOther) == typeof(UInt256))
        {
            result = (UInt256)(object)value;
        }
        else if (!TryConvertFrom(value, ConversionMode.Saturating, out result) && !TOther.TryConvertToSaturating(value, out result))
        {
            ThrowNotSupportedException();
        }

        return result;
    }

    /// <inheritdoc cref="INumberBase{TSelf}.CreateTruncating{TOther}(TOther)"/>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static UInt256 CreateTruncating<TOther>(TOther value) where TOther : INumberBase<TOther>
    {
        UInt256 result;
        if (typeof(TOther) == typeof(UInt256))
        {
            result = (UInt256)(object)value;
        }
        else if (!TryConvertFrom(value, ConversionMode.Truncating, out result) && !TOther.TryConvertToTruncating(value, out result))
        {
            ThrowNotSupportedException();
        }

        return result;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool INumberBase<UInt256>.TryConvertFromChecked<TOther>(TOther value, out UInt256 result) =>
        TryConvertFrom(value, ConversionMode.Checked, out result);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool INumberBase<UInt256>.TryConvertFromSaturating<TOther>(TOther value, out UInt256 result) =>
        TryConvertFrom(value, ConversionMode.Saturating, out result);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool INumberBase<UInt256>.TryConvertFromTruncating<TOther>(TOther value, out UInt256 result) =>
        TryConvertFrom(value, ConversionMode.Truncating, out result);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool INumberBase<UInt256>.TryConvertToChecked<TOther>(UInt256 value, [MaybeNullWhen(false)] out TOther result) =>
        TryConvertTo(in value, ConversionMode.Checked, out result);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool INumberBase<UInt256>.TryConvertToSaturating<TOther>(UInt256 value, [MaybeNullWhen(false)] out TOther result) =>
        TryConvertTo(in value, ConversionMode.Saturating, out result);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool INumberBase<UInt256>.TryConvertToTruncating<TOther>(UInt256 value, [MaybeNullWhen(false)] out TOther result) =>
        TryConvertTo(in value, ConversionMode.Truncating, out result);

    // Every branch but one folds away per instantiation, and the mode is a constant at each call site.
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool TryConvertFrom<TOther>(TOther value, ConversionMode mode, out UInt256 result)
        where TOther : INumberBase<TOther>
    {
        if (typeof(TOther) == typeof(byte))
        {
            result = new UInt256((byte)(object)value);
        }
        else if (typeof(TOther) == typeof(char))
        {
            result = new UInt256((char)(object)value);
        }
        else if (typeof(TOther) == typeof(ushort))
        {
            result = new UInt256((ushort)(object)value);
        }
        else if (typeof(TOther) == typeof(uint))
        {
            result = new UInt256((uint)(object)value);
        }
        else if (typeof(TOther) == typeof(ulong))
        {
            result = new UInt256((ulong)(object)value);
        }
        else if (typeof(TOther) == typeof(nuint))
        {
            result = new UInt256((nuint)(object)value);
        }
        else if (typeof(TOther) == typeof(UInt128))
        {
            UInt128 actual = (UInt128)(object)value;
            result = new UInt256((ulong)actual, (ulong)(actual >> 64));
        }
        else if (typeof(TOther) == typeof(sbyte))
        {
            result = FromInt64((sbyte)(object)value, mode);
        }
        else if (typeof(TOther) == typeof(short))
        {
            result = FromInt64((short)(object)value, mode);
        }
        else if (typeof(TOther) == typeof(int))
        {
            result = FromInt64((int)(object)value, mode);
        }
        else if (typeof(TOther) == typeof(long))
        {
            result = FromInt64((long)(object)value, mode);
        }
        else if (typeof(TOther) == typeof(nint))
        {
            result = FromInt64((nint)(object)value, mode);
        }
        else if (typeof(TOther) == typeof(Int128))
        {
            result = FromInt128((Int128)(object)value, mode);
        }
        else if (typeof(TOther) == typeof(Int256))
        {
            result = FromInt256((Int256)(object)value, mode);
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
            result = FromDecimal((decimal)(object)value, mode);
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
    private static bool TryConvertTo<TOther>(in UInt256 value, ConversionMode mode, [MaybeNullWhen(false)] out TOther result)
        where TOther : INumberBase<TOther>
    {
        if (typeof(TOther) == typeof(byte))
        {
            result = (TOther)(object)(byte)Narrow(in value, byte.MaxValue, mode);
        }
        else if (typeof(TOther) == typeof(char))
        {
            result = (TOther)(object)(char)Narrow(in value, char.MaxValue, mode);
        }
        else if (typeof(TOther) == typeof(ushort))
        {
            result = (TOther)(object)(ushort)Narrow(in value, ushort.MaxValue, mode);
        }
        else if (typeof(TOther) == typeof(uint))
        {
            result = (TOther)(object)(uint)Narrow(in value, uint.MaxValue, mode);
        }
        else if (typeof(TOther) == typeof(ulong))
        {
            result = (TOther)(object)Narrow(in value, ulong.MaxValue, mode);
        }
        else if (typeof(TOther) == typeof(nuint))
        {
            result = (TOther)(object)(nuint)Narrow(in value, nuint.MaxValue, mode);
        }
        else if (typeof(TOther) == typeof(sbyte))
        {
            result = (TOther)(object)(sbyte)Narrow(in value, (ulong)sbyte.MaxValue, mode);
        }
        else if (typeof(TOther) == typeof(short))
        {
            result = (TOther)(object)(short)Narrow(in value, (ulong)short.MaxValue, mode);
        }
        else if (typeof(TOther) == typeof(int))
        {
            result = (TOther)(object)(int)Narrow(in value, int.MaxValue, mode);
        }
        else if (typeof(TOther) == typeof(long))
        {
            result = (TOther)(object)(long)Narrow(in value, long.MaxValue, mode);
        }
        else if (typeof(TOther) == typeof(nint))
        {
            result = (TOther)(object)(nint)Narrow(in value, (ulong)nint.MaxValue, mode);
        }
        else if (typeof(TOther) == typeof(UInt128))
        {
            UInt128 actual = new(value.u1, value.u0);
            if ((value.u2 | value.u3) != 0 && mode != ConversionMode.Truncating)
            {
                if (mode == ConversionMode.Checked) ThrowOverflowException();
                actual = UInt128.MaxValue;
            }

            result = (TOther)(object)actual;
        }
        else if (typeof(TOther) == typeof(Int128))
        {
            Int128 actual = new(value.u1, value.u0);
            if (((value.u2 | value.u3) != 0 || (long)value.u1 < 0) && mode != ConversionMode.Truncating)
            {
                if (mode == ConversionMode.Checked) ThrowOverflowException();
                actual = Int128.MaxValue;
            }

            result = (TOther)(object)actual;
        }
        else if (typeof(TOther) == typeof(double))
        {
            result = (TOther)(object)ToDouble(in value);
        }
        else if (typeof(TOther) == typeof(float))
        {
            result = (TOther)(object)ToSingle(in value);
        }
        else if (typeof(TOther) == typeof(Half))
        {
            result = (TOther)(object)ToHalf(in value);
        }
        else if (typeof(TOther) == typeof(decimal))
        {
            result = (TOther)(object)ToDecimal(in value, negative: false, mode);
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

    /// <summary>The low limb when the value is at most <paramref name="max"/>; otherwise throws, saturates or truncates.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong Narrow(in UInt256 value, ulong max, ConversionMode mode)
    {
        if ((value.u1 | value.u2 | value.u3) == 0 && value.u0 <= max) return value.u0;
        if (mode == ConversionMode.Checked) ThrowOverflowException();
        return mode == ConversionMode.Saturating ? max : value.u0;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static UInt256 FromInt64(long value, ConversionMode mode)
    {
        if (value >= 0) return new UInt256((ulong)value);
        if (mode == ConversionMode.Checked) ThrowOverflowException();
        return mode == ConversionMode.Saturating
            ? default
            : new UInt256((ulong)value, ulong.MaxValue, ulong.MaxValue, ulong.MaxValue);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static UInt256 FromInt128(Int128 value, ConversionMode mode)
    {
        ulong lower = (ulong)value;
        ulong upper = (ulong)(value >> 64);
        if ((long)upper >= 0) return new UInt256(lower, upper);
        if (mode == ConversionMode.Checked) ThrowOverflowException();
        return mode == ConversionMode.Saturating
            ? default
            : new UInt256(lower, upper, ulong.MaxValue, ulong.MaxValue);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static UInt256 FromInt256(in Int256 value, ConversionMode mode)
    {
        if (value.IsNegative && mode != ConversionMode.Truncating)
        {
            if (mode == ConversionMode.Checked) ThrowOverflowException();
            return default;
        }

        return value._value;
    }

    /// <summary>
    /// Truncates toward zero. Truncating behaves as saturating, as it does for <see cref="UInt128"/>: NaN and
    /// anything below one give zero, and anything from 2^256 up gives <see cref="MaxValue"/>.
    /// </summary>
    private static UInt256 FromDouble(double value, ConversionMode mode)
    {
        double twoTo256 = BitConverter.UInt64BitsToDouble(0x4FF0_0000_0000_0000);
        if (mode == ConversionMode.Checked && !(value > -1.0 && value < twoTo256)) ThrowOverflowException();
        if (value >= twoTo256) return new UInt256(ulong.MaxValue, ulong.MaxValue, ulong.MaxValue, ulong.MaxValue);
        return FromDoubleInRange(value);
    }

    /// <summary>Truncates a value below 2^256 toward zero; NaN and anything below one give zero.</summary>
    internal static UInt256 FromDoubleInRange(double value)
    {
        if (!(value >= 1.0)) return default;

        ulong bits = BitConverter.DoubleToUInt64Bits(value);
        int exponent = (int)(bits >> 52) - 1075;
        ulong mantissa = (bits & 0x000F_FFFF_FFFF_FFFF) | 0x0010_0000_0000_0000;
        if (exponent <= 0) return new UInt256(mantissa >> -exponent);

        Lsh(new UInt256(mantissa), exponent, out UInt256 res);
        return res;
    }

    private static UInt256 FromDecimal(decimal value, ConversionMode mode)
    {
        if (value < 0)
        {
            if (mode == ConversionMode.Checked && value <= -1m) ThrowOverflowException();
            return default;
        }

        UInt128 magnitude = (UInt128)value;
        return new UInt256((ulong)magnitude, (ulong)(magnitude >> 64));
    }

    private static UInt256 FromBigInteger(BigInteger value, ConversionMode mode)
    {
        if (value.Sign < 0 || value.GetBitLength() > 256)
        {
            if (mode == ConversionMode.Checked) ThrowOverflowException();
            if (mode == ConversionMode.Saturating)
            {
                return value.Sign < 0 ? default : new UInt256(ulong.MaxValue, ulong.MaxValue, ulong.MaxValue, ulong.MaxValue);
            }

            value &= (BigInteger.One << 256) - 1;
        }

        Span<byte> bytes = stackalloc byte[32];
        bytes.Clear();
        value.TryWriteBytes(bytes, out _, isUnsigned: true);
        return new UInt256(bytes);
    }

    /// <summary>Rounds to nearest, ties to even, from the top 64 bits and a sticky bit for the rest.</summary>
    internal static double ToDouble(in UInt256 value)
    {
        if (!TopBits(in value, out ulong top, out int exponent)) return value.u0;
        // 55 bits keep the round and sticky bits and convert as a signed long, which rounds correctly everywhere.
        long reduced = (long)((top >> 9) | ((top & 0x1FF) != 0 ? 1UL : 0));
        return Math.ScaleB(reduced, exponent + 9);
    }

    /// <inheritdoc cref="ToDouble"/>
    internal static float ToSingle(in UInt256 value)
    {
        if (!TopBits(in value, out ulong top, out int exponent)) return value.u0;
        // 26 bits are exact in a double, so narrowing that to float rounds once.
        long reduced = (long)((top >> 38) | ((top & 0x3F_FFFF_FFFF) != 0 ? 1UL : 0));
        return MathF.ScaleB((float)(double)reduced, exponent + 38);
    }

    // Half overflows to infinity from 65520; below 2^24 the float step is exact, leaving one rounding.
    internal static Half ToHalf(in UInt256 value) =>
        (value.u1 | value.u2 | value.u3) == 0 && value.u0 < (1UL << 24) ? (Half)(float)value.u0 : Half.PositiveInfinity;

    /// <summary>
    /// For a value above <see cref="ulong.MaxValue"/>, the 64 bits from the most significant set bit down, with
    /// bit 0 set if any lower bit is, and the power of two that scales them back.
    /// </summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool TopBits(in UInt256 value, out ulong top, out int exponent)
    {
        ulong high, low, rest;
        if (value.u3 != 0)
        {
            (high, low, rest, exponent) = (value.u3, value.u2, value.u1 | value.u0, 192);
        }
        else if (value.u2 != 0)
        {
            (high, low, rest, exponent) = (value.u2, value.u1, value.u0, 128);
        }
        else if (value.u1 != 0)
        {
            (high, low, rest, exponent) = (value.u1, value.u0, 0, 64);
        }
        else
        {
            top = 0;
            exponent = 0;
            return false;
        }

        int shift = BitOperations.LeadingZeroCount(high);
        // (low >> 1) >> (63 - shift) is low >> (64 - shift), and still 0 when shift is 0.
        top = (high << shift) | ((low >> 1) >> (63 - shift));
        top |= ((low << shift) | rest) != 0 ? 1UL : 0;
        exponent -= shift;
        return true;
    }

    internal static decimal ToDecimal(in UInt256 magnitude, bool negative, ConversionMode mode)
    {
        if ((magnitude.u2 | magnitude.u3) != 0 || magnitude.u1 > uint.MaxValue)
        {
            if (mode == ConversionMode.Checked) ThrowOverflowException();
            return negative ? decimal.MinValue : decimal.MaxValue;
        }

        return new decimal((int)magnitude.u0, (int)(magnitude.u0 >> 32), (int)magnitude.u1, negative, 0);
    }

    [DoesNotReturn, StackTraceHidden]
    internal static void ThrowOverflowException() => throw new OverflowException();

    [DoesNotReturn, StackTraceHidden]
    internal static void ThrowMinMaxException<T>(T min, T max) => throw new ArgumentException($"'{min}' cannot be greater than {max}.");
}
