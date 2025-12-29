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
        ? TryParse(value.Slice(2), NumberStyles.HexNumber, CultureInfo.InvariantCulture, out result)
        : TryParse(value, NumberStyles.Integer, CultureInfo.InvariantCulture, out result);

    public static bool TryParse(string value, NumberStyles style, IFormatProvider provider, out UInt256 result) => TryParse(value.AsSpan(), style, provider, out result);

    public static bool TryParse(in ReadOnlySpan<char> value, NumberStyles style, IFormatProvider provider, out UInt256 result)
    {
        BigInteger a;
        bool bigParsedProperly;
        if ((style & NumberStyles.HexNumber) == NumberStyles.HexNumber && value[0] != 0)
        {
            Span<char> fixedHexValue = stackalloc char[value.Length + 1];
            fixedHexValue[0] = '0';
            value.CopyTo(fixedHexValue.Slice(1));
            bigParsedProperly = BigInteger.TryParse(fixedHexValue, style, provider, out a);
        }
        else
        {
            Span<char> fixedHexValue = stackalloc char[value.Length];
            value.CopyTo(fixedHexValue);
            bigParsedProperly = BigInteger.TryParse(fixedHexValue, style, provider, out a);
        }

        if (!bigParsedProperly)
        {
            result = Zero;
            return false;
        }


        result = (UInt256)a;
        return true;
    }
}
