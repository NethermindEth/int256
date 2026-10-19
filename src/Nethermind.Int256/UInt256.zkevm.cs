// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Buffers.Binary;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics;
using Arm = System.Runtime.Intrinsics.Arm;
using x64 = System.Runtime.Intrinsics.X86;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private const MethodImplOptions SubtractUnderflowInlining = MethodImplOptions.AggressiveInlining;

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void ExpOddLong(in UInt256 b, in UInt256 e, int precision, out UInt256 result)
    {
        if (precision >= ExpFourTermPrecision)
            ExpOddLongNear32(b, e, 64 - precision, out result);
        else if (precision >= 32)
            ExpNearOne32Signed(b, e, precision >= 43, out result);
        else
            ExpOddLong32(b, e, 32 - precision, out result);
    }

    private const int ExpBinomialMinBits = 80;

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void SquareExpLong(in UInt256 value, out UInt256 result)
    {
        ulong x0 = value.u0, x1 = value.u1, x2 = value.u2, x3 = value.u3;
        ulong h00 = Square64(x0, out ulong r0);
        ulong h11 = Square64(x1, out ulong l11);
        ulong h01 = Multiply64(x0, x1, out ulong l01);
        ulong h02 = Multiply64(x0, x2, out ulong l02);

        // Sum cross products before doubling: carry propagation happens once.
        ulong cross = h01 + l02;
        ulong upper = h02 + (cross < h01 ? 1UL : 0UL) + x0 * x3 + x1 * x2;
        ulong r1 = h00 + (l01 << 1);
        ulong carry = 0;
        ulong r2 = AddAndCountCarry(l11, (cross << 1) | (l01 >> 63), ref carry);
        r2 = AddAndCountCarry(r2, r1 < h00 ? 1UL : 0UL, ref carry);
        result = new UInt256(r0, r1, r2, h11 + (upper << 1) + (cross >> 63) + carry);
    }

    // Base ten first removes three guest steps from each table lookup.
    private const bool ExpPreferDecimalLookup = true;

    private const int ExpWindowMaxWidth = 5;

    // General width dispatch produces fewer guest steps and memory operations.
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void MultiplyExpPower(in UInt256 value, in UInt256 power, out UInt256 result)
        => Multiply(value, power, out result);

    // A separate wide-product call increases guest steps and memory traffic.
    private const MethodImplOptions MulModWideInlining = MethodImplOptions.AggressiveInlining;

    // Forced inlining of this reducer increases guest steps and proof work.
    private const MethodImplOptions MulMod128Inlining = (MethodImplOptions)0;

    // Guest execution requires stable hashes across runs.
    private static readonly uint _hashSeed = 2098026241U;
    private static readonly ulong _aesHashSeed0 = 0x1F83D9ABFB41BD6BUL;
    private static readonly ulong _aesHashSeed1 = 0x5BE0CD19137E2179UL;

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public readonly override int GetHashCode()
    {
        if (x64.Aes.IsSupported || Arm.Aes.IsSupported)
        {
            Vector128<byte> key = Unsafe.As<ulong, Vector128<byte>>(ref Unsafe.AsRef(in u0));
            Vector128<byte> data = Unsafe.As<ulong, Vector128<byte>>(ref Unsafe.AsRef(in u2));
            key ^= Vector128.Create(_aesHashSeed0, _aesHashSeed1).AsByte();
            Vector128<byte> mixed = HashAesRound(data, key);
            mixed = HashAesRound(mixed, key);
            return FoldHash(MumFold(mixed));
        }

        // Include the 32-byte input length in the deterministic fallback seed.
        return GetCrcHashCode(unchecked(_hashSeed + 32u));
    }

    public bool IsZero
    {
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        get => (u0 | u1 | u2 | u3) == 0;
    }

    public bool IsOne
    {
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        get => ((u0 ^ 1UL) | u1 | u2 | u3) == 0;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void Not(in UInt256 a, out UInt256 res)
        => res = new UInt256(~a.u0, ~a.u1, ~a.u2, ~a.u3);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void Or(in UInt256 a, in UInt256 b, out UInt256 res)
        => res = new UInt256(a.u0 | b.u0, a.u1 | b.u1, a.u2 | b.u2, a.u3 | b.u3);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void And(in UInt256 a, in UInt256 b, out UInt256 res)
        => res = new UInt256(a.u0 & b.u0, a.u1 & b.u1, a.u2 & b.u2, a.u3 & b.u3);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void Xor(in UInt256 a, in UInt256 b, out UInt256 res)
        => res = new UInt256(a.u0 ^ b.u0, a.u1 ^ b.u1, a.u2 ^ b.u2, a.u3 ^ b.u3);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool LessThan(in UInt256 a, in UInt256 b)
        => LessThanScalar(in a, in b);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool LessThanBoth(in UInt256 x, in UInt256 y, in UInt256 m)
        => LessThanScalar(in x, in m) && LessThanScalar(in y, in m);

    // Deliberately keep primitive overloads below Equals(in UInt256) in priority here.
    // The guest compiler eliminates its temporary; matching priorities added address work
    // and replaced short-circuit upper-limb checks with more expensive loads in measured callers.
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public bool Equals(uint other)
        => u0 == other && (u1 | u2 | u3) == 0;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public bool Equals(ulong other)
        => u0 == other && (u1 | u2 | u3) == 0;

    [OverloadResolutionPriority(1)]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public bool Equals(in UInt256 other)
        => u0 == other.u0 && u1 == other.u1 && u2 == other.u2 && u3 == other.u3;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool LessThanOrEqual(in UInt256 a, in UInt256 b)
        => !LessThan(in b, in a);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool GreaterThanOrEqual(in UInt256 a, in UInt256 b)
        => !LessThan(in a, in b);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool GreaterThan(in UInt256 a, in UInt256 b)
        => LessThan(in b, in a);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool LessThanOperator(in UInt256 a, in UInt256 b)
        => LessThan(in a, in b);

    private static partial void SubtractWithBorrow(ulong a, ulong b, ref ulong borrow, out ulong res)
    {
        // Reusing the intermediate difference reduces guest instructions.
        ulong incomingBorrow = borrow;
        ulong difference = a - b;
        res = difference - incomingBorrow;
        borrow = (a < b ? 1UL : 0UL) | (difference < incomingBorrow ? 1UL : 0UL);
    }

    public static partial bool SubtractUnderflow(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        ulong b0 = b.u0;
        if ((b.u1 | b.u2 | b.u3) == 0)
        {
            return SubtractScalarUInt64(in a, b0, out res);
        }

        // The first limb has no incoming borrow.
        ulong a0 = a.u0;
        ulong r0 = a0 - b0;
        ulong borrow = a0 < b0 ? 1UL : 0UL;
        SubtractWithBorrowSelect(a.u1, b.u1, ref borrow, out ulong r1);
        SubtractWithBorrowSelect(a.u2, b.u2, ref borrow, out ulong r2);
        SubtractWithBorrowSelect(a.u3, b.u3, ref borrow, out ulong r3);
        StoreLimbs(out res, r0, r1, r2, r3);
        return borrow != 0;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void SubtractWithBorrowSelect(ulong a, ulong b, ref ulong borrow, out ulong res)
    {
        ulong incoming = borrow;
        ulong difference = a - b;
        res = difference - incoming;
        // Equal operands propagate the incoming borrow; unequal operands generate their own.
        borrow = difference == 0 ? incoming : (a < b ? 1UL : 0UL);
    }

    /// <summary>Whether the guest's zkVM reverses a word's bytes in one instruction (Zbb's <c>rev8</c>).</summary>
    /// <remarks>
    /// False here, for the zkVMs that decode rv64im only. A guest whose zkVM has Zbb substitutes true in its ILC
    /// substitutions, which folds every branch on it away. Without Zbb, <see cref="BinaryPrimitives.ReverseEndianness(ulong)"/>
    /// is a ~30-instruction software sequence, and those zkVMs also reject misaligned accesses, so an unaligned word
    /// is loaded byte by byte anyway; gathering the bytes in big-endian order drops the reversal on top of it.
    /// </remarks>
    private static bool HasByteReverse => false;

    private static partial void ReadBigEndianLimbs(ReadOnlySpan<byte> bytes, out ulong u0, out ulong u1, out ulong u2, out ulong u3)
    {
        ref byte source = ref MemoryMarshal.GetReference(bytes);
        u3 = ReadUInt64BigEndian(ref source);
        u2 = ReadUInt64BigEndian(ref Unsafe.Add(ref source, 8));
        u1 = ReadUInt64BigEndian(ref Unsafe.Add(ref source, 16));
        u0 = ReadUInt64BigEndian(ref Unsafe.Add(ref source, 24));
    }

    private static partial void WriteBigEndianLimbs(in UInt256 value, Span<byte> target)
    {
        // The target may overlap the value, so every limb is read before the first store.
        (ulong u0, ulong u1, ulong u2, ulong u3) = (value.u0, value.u1, value.u2, value.u3);
        ref byte destination = ref MemoryMarshal.GetReference(target);
        WriteUInt64BigEndian(ref destination, u3);
        WriteUInt64BigEndian(ref Unsafe.Add(ref destination, 8), u2);
        WriteUInt64BigEndian(ref Unsafe.Add(ref destination, 16), u1);
        WriteUInt64BigEndian(ref Unsafe.Add(ref destination, 24), u0);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong ReadUInt64BigEndian(ref byte source)
    {
        if (HasByteReverse) return BinaryPrimitives.ReverseEndianness(Unsafe.ReadUnaligned<ulong>(ref source));
        return ((ulong)source << 56) | ((ulong)Unsafe.Add(ref source, 1) << 48) |
            ((ulong)Unsafe.Add(ref source, 2) << 40) | ((ulong)Unsafe.Add(ref source, 3) << 32) |
            ((ulong)Unsafe.Add(ref source, 4) << 24) | ((ulong)Unsafe.Add(ref source, 5) << 16) |
            ((ulong)Unsafe.Add(ref source, 6) << 8) | Unsafe.Add(ref source, 7);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void WriteUInt64BigEndian(ref byte destination, ulong value)
    {
        if (HasByteReverse)
        {
            Unsafe.WriteUnaligned(ref destination, BinaryPrimitives.ReverseEndianness(value));
            return;
        }

        destination = (byte)(value >> 56);
        Unsafe.Add(ref destination, 1) = (byte)(value >> 48);
        Unsafe.Add(ref destination, 2) = (byte)(value >> 40);
        Unsafe.Add(ref destination, 3) = (byte)(value >> 32);
        Unsafe.Add(ref destination, 4) = (byte)(value >> 24);
        Unsafe.Add(ref destination, 5) = (byte)(value >> 16);
        Unsafe.Add(ref destination, 6) = (byte)(value >> 8);
        Unsafe.Add(ref destination, 7) = (byte)value;
    }

    // The zkEVM build writes D, G, X and B only (UInt256.Numerics.cs): a BigInteger fallback for the culture formats
    // would link BigInteger's formatting into every guest that interpolates a UInt256.
    private static bool TryFormatOther(in UInt256 bits, bool signed, Span<char> destination, out int written,
        ReadOnlySpan<char> format, IFormatProvider? provider) => throw UnsupportedFormat(format);

    private static string FormatOther(in UInt256 bits, bool signed, string? format, IFormatProvider? provider) =>
        throw UnsupportedFormat(format);

    private static FormatException UnsupportedFormat(ReadOnlySpan<char> format) =>
        new($"Format '{format}' is not supported in the zkEVM build; use D, G, X or B.");
}
