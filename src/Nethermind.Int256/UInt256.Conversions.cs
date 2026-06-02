// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Buffers.Binary;
using System.Globalization;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.X86;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    public void Convert(out BigInteger big)
    {
        big = (BigInteger)this;
    }
    public TypeCode GetTypeCode() => TypeCode.Object;
    public bool ToBoolean(IFormatProvider? provider) => !IsZero;
    public byte ToByte(IFormatProvider? provider) => System.Convert.ToByte(ToDecimal(provider), provider);
    public char ToChar(IFormatProvider? provider) => System.Convert.ToChar(ToDecimal(provider), provider);
    public DateTime ToDateTime(IFormatProvider? provider) => System.Convert.ToDateTime(ToDecimal(provider), provider);
    public decimal ToDecimal(IFormatProvider? provider) => (decimal)this;
    public double ToDouble(IFormatProvider? provider) => (double)this;
    public short ToInt16(IFormatProvider? provider) => System.Convert.ToInt16(ToDecimal(provider), provider);
    public int ToInt32(IFormatProvider? provider) => System.Convert.ToInt32(ToDecimal(provider), provider);
    public long ToInt64(IFormatProvider? provider) => System.Convert.ToInt64(ToDecimal(provider), provider);
    public sbyte ToSByte(IFormatProvider? provider) => System.Convert.ToSByte(ToDecimal(provider), provider);
    public float ToSingle(IFormatProvider? provider) => System.Convert.ToSingle(ToDouble(provider), provider);
    public string ToString(IFormatProvider? provider) => ((BigInteger)this).ToString(provider);
    public object ToType(Type conversionType, IFormatProvider? provider) =>
        conversionType == typeof(BigInteger)
            ? (BigInteger)this
            : System.Convert.ChangeType(ToDecimal(provider), conversionType, provider);

    public ushort ToUInt16(IFormatProvider? provider) => System.Convert.ToUInt16(ToDecimal(provider), provider);
    public uint ToUInt32(IFormatProvider? provider) => System.Convert.ToUInt32(ToDecimal(provider), provider);
    public ulong ToUInt64(IFormatProvider? provider) => System.Convert.ToUInt64(ToDecimal(provider), provider);
    public byte[] PaddedBytes(int n)
    {
        byte[] b = new byte[n];

        for (int i = 0; i < 32 && i < n; i++)
        {
            b[n - 1 - i] = (byte)(this[i / 8] >> (8 * (i % 8)));
        }

        return b;
    }

    public byte[] ToBigEndian()
    {
        byte[] bytes = new byte[32];
        ToBigEndian(bytes);
        return bytes;
    }

    public byte[] ToLittleEndian()
    {
        byte[] bytes = new byte[32];
        ToLittleEndian(bytes);
        return bytes;
    }

    public void ToBigEndian(Span<byte> target)
    {
        if (target.Length == 32)
        {
            BinaryPrimitives.WriteUInt64BigEndian(target.Slice(0, 8), u3);
            BinaryPrimitives.WriteUInt64BigEndian(target.Slice(8, 8), u2);
            BinaryPrimitives.WriteUInt64BigEndian(target.Slice(16, 8), u1);
            BinaryPrimitives.WriteUInt64BigEndian(target.Slice(24, 8), u0);
        }
        else if (target.Length == 20)
        {
            BinaryPrimitives.WriteUInt32BigEndian(target.Slice(0, 4), (uint)u2);
            BinaryPrimitives.WriteUInt64BigEndian(target.Slice(4, 8), u1);
            BinaryPrimitives.WriteUInt64BigEndian(target.Slice(12, 8), u0);
        }
    }

    public void ToLittleEndian(Span<byte> target)
    {
        if (target.Length == 32)
        {
            if (Avx.IsSupported)
            {
                Unsafe.As<byte, Vector256<ulong>>(ref MemoryMarshal.GetReference(target)) = Unsafe.As<ulong, Vector256<ulong>>(ref Unsafe.AsRef(in u0));
            }
            else
            {
                BinaryPrimitives.WriteUInt64LittleEndian(target.Slice(0, 8), u0);
                BinaryPrimitives.WriteUInt64LittleEndian(target.Slice(8, 8), u1);
                BinaryPrimitives.WriteUInt64LittleEndian(target.Slice(16, 8), u2);
                BinaryPrimitives.WriteUInt64LittleEndian(target.Slice(24, 8), u3);
            }
        }
        else
        {
            ThrowNotSupportedException();
        }
    }

    public static UInt256 Parse(string value) => !TryParse(value, out UInt256 c) ? throw new FormatException() : c;

    public static UInt256 Parse(in ReadOnlySpan<char> value, NumberStyles numberStyles) => !TryParse(value, numberStyles, CultureInfo.InvariantCulture, out UInt256 c) ? throw new FormatException() : c;

    public static bool TryParse(string value, out UInt256 result) => TryParse(value.AsSpan(), out result);

    public static bool TryParse(ReadOnlySpan<char> value, out UInt256 result) => value.StartsWith("0x", StringComparison.OrdinalIgnoreCase)
        ? TryParseHex(value[2..], out result)
        : TryParseDecimal(value, out result);

    public static bool TryParse(string value, NumberStyles style, IFormatProvider provider, out UInt256 result) => TryParse(value.AsSpan(), style, provider, out result);

    public static bool TryParse(in ReadOnlySpan<char> value, NumberStyles style, IFormatProvider provider, out UInt256 result)
    {
        if (style == NumberStyles.HexNumber)
        {
            return TryParseHex(TrimWhiteSpace(value), out result);
        }

        NumberFormatInfo numberFormatInfo = NumberFormatInfo.GetInstance(provider);
        if (style == NumberStyles.Integer &&
            numberFormatInfo.PositiveSign == "+" &&
            numberFormatInfo.NegativeSign == "-")
        {
            return TryParseDecimal(value, out result);
        }

        return TryParseViaBigInteger(value, style, provider, out result);
    }

    private static bool TryParseHex(ReadOnlySpan<char> value, out UInt256 result)
    {
        value = TrimWhiteSpace(value);

        int start = 0;
        while (start < value.Length && value[start] == '0')
        {
            start++;
        }

        int digitCount = value.Length - start;
        if (digitCount == 0)
        {
            result = Zero;
            return value.Length != 0;
        }

        if (digitCount > 64)
        {
            result = Zero;
            return false;
        }

        int end = value.Length;
        if (!TryParseHexChunk(value, ref end, start, out ulong u0) ||
            !TryParseHexChunk(value, ref end, start, out ulong u1) ||
            !TryParseHexChunk(value, ref end, start, out ulong u2) ||
            !TryParseHexChunk(value, ref end, start, out ulong u3))
        {
            result = Zero;
            return false;
        }

        result = Create(u0, u1, u2, u3);
        return true;
    }

    private static bool TryParseDecimal(ReadOnlySpan<char> value, out UInt256 result)
    {
        value = TrimWhiteSpace(value);
        if (value.Length == 0)
        {
            result = Zero;
            return false;
        }

        int index = 0;
        if (value[0] == '+')
        {
            index = 1;
        }
        else if (value[0] == '-')
        {
            result = Zero;
            return false;
        }

        if (index == value.Length)
        {
            result = Zero;
            return false;
        }

        while (index < value.Length && value[index] == '0')
        {
            index++;
        }

        if (index == value.Length)
        {
            result = Zero;
            return true;
        }

        int digitCount = value.Length - index;
        if (digitCount > 78)
        {
            result = Zero;
            return false;
        }

        const int DecimalChunkDigitCount = 19;
        const ulong DecimalChunkBase = 10_000_000_000_000_000_000UL;

        int firstChunkDigitCount = digitCount % DecimalChunkDigitCount;
        if (firstChunkDigitCount == 0)
        {
            firstChunkDigitCount = DecimalChunkDigitCount;
        }

        if (!TryParseDecimalChunk(value, index, firstChunkDigitCount, out ulong chunk))
        {
            result = Zero;
            return false;
        }

        UInt256 parsed = Create(chunk, 0, 0, 0);
        index += firstChunkDigitCount;

        while (index < value.Length)
        {
            if (!TryParseDecimalChunk(value, index, DecimalChunkDigitCount, out chunk) ||
                !TryMultiplyByUInt64AndAdd(in parsed, DecimalChunkBase, chunk, out parsed))
            {
                result = Zero;
                return false;
            }

            index += DecimalChunkDigitCount;
        }

        result = parsed;
        return true;
    }

    private static bool TryParseHexChunk(ReadOnlySpan<char> value, ref int end, int start, out ulong chunk)
    {
        chunk = 0;
        if (end <= start)
        {
            return true;
        }

        int chunkStart = Math.Max(start, end - 16);
        bool parsed = ulong.TryParse(
            value.Slice(chunkStart, end - chunkStart),
            NumberStyles.HexNumber,
            CultureInfo.InvariantCulture,
            out chunk);
        end = chunkStart;
        return parsed;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool TryParseDecimalChunk(ReadOnlySpan<char> value, int start, int length, out ulong chunk)
    {
        chunk = 0;
        for (int i = start; i < start + length; i++)
        {
            uint digit = (uint)(value[i] - '0');
            if (digit > 9)
            {
                return false;
            }

            chunk = chunk * 10 + digit;
        }

        return true;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool TryMultiplyByUInt64AndAdd(in UInt256 value, ulong multiplier, ulong addend, out UInt256 result)
    {
        ulong high = Multiply64(value.u0, multiplier, out ulong u0);
        if (!AddToLow(addend, ref u0, ref high))
        {
            result = Zero;
            return false;
        }

        ulong carry = high;
        high = Multiply64(value.u1, multiplier, out ulong u1);
        if (!AddToLow(carry, ref u1, ref high))
        {
            result = Zero;
            return false;
        }

        carry = high;
        high = Multiply64(value.u2, multiplier, out ulong u2);
        if (!AddToLow(carry, ref u2, ref high))
        {
            result = Zero;
            return false;
        }

        carry = high;
        high = Multiply64(value.u3, multiplier, out ulong u3);
        if (!AddToLow(carry, ref u3, ref high) || high != 0)
        {
            result = Zero;
            return false;
        }

        result = Create(u0, u1, u2, u3);
        return true;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool AddToLow(ulong value, ref ulong low, ref ulong high)
    {
        ulong previous = low;
        low += value;
        if (low >= previous)
        {
            return true;
        }

        high++;
        return high != 0;
    }

    private static bool TryParseViaBigInteger(ReadOnlySpan<char> value, NumberStyles style, IFormatProvider provider, out UInt256 result)
    {
        if (!BigInteger.TryParse(value, style, provider, out BigInteger parsed) || parsed.Sign < 0)
        {
            result = Zero;
            return false;
        }

        try
        {
            result = (UInt256)parsed;
            return true;
        }
        catch (Exception e) when (e is ArgumentException or OverflowException or IndexOutOfRangeException)
        {
            result = Zero;
            return false;
        }
    }

    private static ReadOnlySpan<char> TrimWhiteSpace(ReadOnlySpan<char> value)
    {
        int start = 0;
        while (start < value.Length && char.IsWhiteSpace(value[start]))
        {
            start++;
        }

        int end = value.Length - 1;
        while (end >= start && char.IsWhiteSpace(value[end]))
        {
            end--;
        }

        return value.Slice(start, end - start + 1);
    }
}
