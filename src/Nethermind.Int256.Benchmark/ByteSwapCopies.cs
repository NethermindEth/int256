// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

// Generated: the span ctor and To*Endian bodies copied verbatim from UInt256 (Current) and without AdvSimd (Old).

using System;
using System.Buffers.Binary;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.Arm;
using System.Runtime.Intrinsics.X86;

namespace Nethermind.Int256.Benchmark;

[StructLayout(LayoutKind.Sequential)]
internal readonly struct U256Current
{
    public readonly ulong u0;
    public readonly ulong u1;
    public readonly ulong u2;
    public readonly ulong u3;

    public U256Current(in ReadOnlySpan<byte> bytes, bool isBigEndian = false)
    {
        if (bytes.Length == 32)
        {
            if (isBigEndian)
            {
                if (Avx2.IsSupported)
                {
                    Unsafe.SkipInit(out u0);
                    Unsafe.SkipInit(out u1);
                    Unsafe.SkipInit(out u2);
                    Unsafe.SkipInit(out u3);
                    Vector256<byte> data = Unsafe.ReadUnaligned<Vector256<byte>>(ref MemoryMarshal.GetReference(bytes));
                    Vector256<byte> shuffle = Vector256.Create(
                        0x18191a1b1c1d1e1ful,
                        0x1011121314151617ul,
                        0x08090a0b0c0d0e0ful,
                        0x0001020304050607ul).AsByte();
                    if (Avx512Vbmi.VL.IsSupported)
                    {
                        Vector256<byte> convert = Avx512Vbmi.VL.PermuteVar32x8(data, shuffle);
                        Unsafe.As<ulong, Vector256<byte>>(ref u0) = convert;
                    }
                    else
                    {
                        Vector256<byte> convert = Avx2.Shuffle(data, shuffle);
                        Vector256<ulong> permute = Avx2.Permute4x64(Unsafe.As<Vector256<byte>, Vector256<ulong>>(ref convert), 0b_01_00_11_10);
                        Unsafe.As<ulong, Vector256<ulong>>(ref u0) = permute;
                    }
                }
                else if (AdvSimd.Arm64.IsSupported)
                {
                    Unsafe.SkipInit(out u0);
                    Unsafe.SkipInit(out u1);
                    Unsafe.SkipInit(out u2);
                    Unsafe.SkipInit(out u3);
                    // Full 32-byte reversal: REV64 reverses bytes within each 64-bit lane, EXT #8
                    // swaps the lanes, and the two 16-byte halves swap places (u0:u1 <- high half).
                    ref byte src = ref MemoryMarshal.GetReference(bytes);
                    Vector128<ulong> reversedLower = AdvSimd.ReverseElement8(Vector128.LoadUnsafe(ref src).AsUInt64());
                    Vector128<ulong> reversedUpper = AdvSimd.ReverseElement8(Vector128.LoadUnsafe(ref src, 16).AsUInt64());
                    Unsafe.As<ulong, Vector128<ulong>>(ref u0) = AdvSimd.ExtractVector128(reversedUpper, reversedUpper, 1);
                    Unsafe.As<ulong, Vector128<ulong>>(ref u2) = AdvSimd.ExtractVector128(reversedLower, reversedLower, 1);
                }
                else
                {
                    u3 = BinaryPrimitives.ReadUInt64BigEndian(bytes.Slice(0, 8));
                    u2 = BinaryPrimitives.ReadUInt64BigEndian(bytes.Slice(8, 8));
                    u1 = BinaryPrimitives.ReadUInt64BigEndian(bytes.Slice(16, 8));
                    u0 = BinaryPrimitives.ReadUInt64BigEndian(bytes.Slice(24, 8));
                }
            }
            else
            {
                if (Vector256.IsHardwareAccelerated)
                {
                    Unsafe.SkipInit(out u0);
                    Unsafe.SkipInit(out u1);
                    Unsafe.SkipInit(out u2);
                    Unsafe.SkipInit(out u3);
                    Unsafe.As<ulong, Vector256<byte>>(ref u0) = Vector256.Create(bytes);
                }
                else if (AdvSimd.Arm64.IsSupported)
                {
                    Unsafe.SkipInit(out u0);
                    Unsafe.SkipInit(out u1);
                    Unsafe.SkipInit(out u2);
                    Unsafe.SkipInit(out u3);
                    // ARM64 is little-endian: the bytes are already the limbs.
                    ref byte src = ref MemoryMarshal.GetReference(bytes);
                    Unsafe.As<ulong, Vector128<byte>>(ref u0) = Vector128.LoadUnsafe(ref src);
                    Unsafe.As<ulong, Vector128<byte>>(ref u2) = Vector128.LoadUnsafe(ref src, 16);
                }
                else
                {
                    u0 = BinaryPrimitives.ReadUInt64LittleEndian(bytes.Slice(0, 8));
                    u1 = BinaryPrimitives.ReadUInt64LittleEndian(bytes.Slice(8, 8));
                    u2 = BinaryPrimitives.ReadUInt64LittleEndian(bytes.Slice(16, 8));
                    u3 = BinaryPrimitives.ReadUInt64LittleEndian(bytes.Slice(24, 8));
                }
            }
        }
        else
        {
            Create(bytes, out u0, out u1, out u2, out u3);
        }
    }

    private static void Create(in ReadOnlySpan<byte> bytes, out ulong u0, out ulong u1, out ulong u2, out ulong u3)
    {
        int byteCount = bytes.Length;
        int unalignedBytes = byteCount % 8;
        int dwordCount = byteCount / 8 + (unalignedBytes == 0 ? 0 : 1);

        ulong cs0 = 0;
        ulong cs1 = 0;
        ulong cs2 = 0;
        ulong cs3 = 0;

        if (dwordCount == 0)
        {
            u0 = u1 = u2 = u3 = 0;
            return;
        }

        if (dwordCount >= 1)
        {
            for (int j = 8; j > 0; j--)
            {
                cs0 <<= 8;
                if (j <= byteCount)
                {
                    cs0 |= bytes[byteCount - j];
                }
            }
        }

        if (dwordCount >= 2)
        {
            for (int j = 16; j > 8; j--)
            {
                cs1 <<= 8;
                if (j <= byteCount)
                {
                    cs1 |= bytes[byteCount - j];
                }
            }
        }

        if (dwordCount >= 3)
        {
            for (int j = 24; j > 16; j--)
            {
                cs2 <<= 8;
                if (j <= byteCount)
                {
                    cs2 |= bytes[byteCount - j];
                }
            }
        }

        if (dwordCount >= 4)
        {
            for (int j = 32; j > 24; j--)
            {
                cs3 <<= 8;
                if (j <= byteCount)
                {
                    cs3 |= bytes[byteCount - j];
                }
            }
        }

        u0 = cs0;
        u1 = cs1;
        u2 = cs2;
        u3 = cs3;
    }

    public void ToBigEndian(Span<byte> target)
    {
        if (target.Length == 32)
        {
            if (Avx2.IsSupported)
            {
                // Full 32-byte reversal is an involution, so this reuses the shuffle constant of the
                // big-endian read ctor (UInt256.Ctors.cs).
                Vector256<byte> data = Unsafe.As<ulong, Vector256<byte>>(ref Unsafe.AsRef(in u0));
                Vector256<byte> shuffle = Vector256.Create(
                    0x18191a1b1c1d1e1ful,
                    0x1011121314151617ul,
                    0x08090a0b0c0d0e0ful,
                    0x0001020304050607ul).AsByte();
                if (Avx512Vbmi.VL.IsSupported)
                {
                    Vector256<byte> convert = Avx512Vbmi.VL.PermuteVar32x8(data, shuffle);
                    Unsafe.WriteUnaligned(ref MemoryMarshal.GetReference(target), convert);
                }
                else
                {
                    Vector256<byte> convert = Avx2.Shuffle(data, shuffle);
                    Vector256<ulong> permute = Avx2.Permute4x64(convert.AsUInt64(), 0b_01_00_11_10);
                    Unsafe.WriteUnaligned(ref MemoryMarshal.GetReference(target), permute);
                }
            }
            else if (AdvSimd.Arm64.IsSupported)
            {
                // Mirror of the big-endian read ctor: REV64 + EXT #8 per half, halves stored swapped.
                Vector128<ulong> reversedLower = AdvSimd.ReverseElement8(Unsafe.As<ulong, Vector128<ulong>>(ref Unsafe.AsRef(in u0)));
                Vector128<ulong> reversedUpper = AdvSimd.ReverseElement8(Unsafe.As<ulong, Vector128<ulong>>(ref Unsafe.AsRef(in u2)));
                ref byte dst = ref MemoryMarshal.GetReference(target);
                AdvSimd.ExtractVector128(reversedUpper, reversedUpper, 1).AsByte().StoreUnsafe(ref dst);
                AdvSimd.ExtractVector128(reversedLower, reversedLower, 1).AsByte().StoreUnsafe(ref dst, 16);
            }
            else
            {
                BinaryPrimitives.WriteUInt64BigEndian(target.Slice(0, 8), u3);
                BinaryPrimitives.WriteUInt64BigEndian(target.Slice(8, 8), u2);
                BinaryPrimitives.WriteUInt64BigEndian(target.Slice(16, 8), u1);
                BinaryPrimitives.WriteUInt64BigEndian(target.Slice(24, 8), u0);
            }
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
            else if (AdvSimd.Arm64.IsSupported)
            {
                // The limbs are already in byte order.
                ref byte dst = ref MemoryMarshal.GetReference(target);
                Unsafe.As<ulong, Vector128<byte>>(ref Unsafe.AsRef(in u0)).StoreUnsafe(ref dst);
                Unsafe.As<ulong, Vector128<byte>>(ref Unsafe.AsRef(in u2)).StoreUnsafe(ref dst, 16);
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

    [DoesNotReturn, StackTraceHidden]
    private static void ThrowNotSupportedException() => throw new NotSupportedException();
}

[StructLayout(LayoutKind.Sequential)]
internal readonly struct U256Old
{
    public readonly ulong u0;
    public readonly ulong u1;
    public readonly ulong u2;
    public readonly ulong u3;

    public U256Old(in ReadOnlySpan<byte> bytes, bool isBigEndian = false)
    {
        if (bytes.Length == 32)
        {
            if (isBigEndian)
            {
                if (Avx2.IsSupported)
                {
                    Unsafe.SkipInit(out u0);
                    Unsafe.SkipInit(out u1);
                    Unsafe.SkipInit(out u2);
                    Unsafe.SkipInit(out u3);
                    Vector256<byte> data = Unsafe.ReadUnaligned<Vector256<byte>>(ref MemoryMarshal.GetReference(bytes));
                    Vector256<byte> shuffle = Vector256.Create(
                        0x18191a1b1c1d1e1ful,
                        0x1011121314151617ul,
                        0x08090a0b0c0d0e0ful,
                        0x0001020304050607ul).AsByte();
                    if (Avx512Vbmi.VL.IsSupported)
                    {
                        Vector256<byte> convert = Avx512Vbmi.VL.PermuteVar32x8(data, shuffle);
                        Unsafe.As<ulong, Vector256<byte>>(ref u0) = convert;
                    }
                    else
                    {
                        Vector256<byte> convert = Avx2.Shuffle(data, shuffle);
                        Vector256<ulong> permute = Avx2.Permute4x64(Unsafe.As<Vector256<byte>, Vector256<ulong>>(ref convert), 0b_01_00_11_10);
                        Unsafe.As<ulong, Vector256<ulong>>(ref u0) = permute;
                    }
                }
                else
                {
                    u3 = BinaryPrimitives.ReadUInt64BigEndian(bytes.Slice(0, 8));
                    u2 = BinaryPrimitives.ReadUInt64BigEndian(bytes.Slice(8, 8));
                    u1 = BinaryPrimitives.ReadUInt64BigEndian(bytes.Slice(16, 8));
                    u0 = BinaryPrimitives.ReadUInt64BigEndian(bytes.Slice(24, 8));
                }
            }
            else
            {
                if (Vector256.IsHardwareAccelerated)
                {
                    Unsafe.SkipInit(out u0);
                    Unsafe.SkipInit(out u1);
                    Unsafe.SkipInit(out u2);
                    Unsafe.SkipInit(out u3);
                    Unsafe.As<ulong, Vector256<byte>>(ref u0) = Vector256.Create(bytes);
                }
                else
                {
                    u0 = BinaryPrimitives.ReadUInt64LittleEndian(bytes.Slice(0, 8));
                    u1 = BinaryPrimitives.ReadUInt64LittleEndian(bytes.Slice(8, 8));
                    u2 = BinaryPrimitives.ReadUInt64LittleEndian(bytes.Slice(16, 8));
                    u3 = BinaryPrimitives.ReadUInt64LittleEndian(bytes.Slice(24, 8));
                }
            }
        }
        else
        {
            Create(bytes, out u0, out u1, out u2, out u3);
        }
    }

    private static void Create(in ReadOnlySpan<byte> bytes, out ulong u0, out ulong u1, out ulong u2, out ulong u3)
    {
        int byteCount = bytes.Length;
        int unalignedBytes = byteCount % 8;
        int dwordCount = byteCount / 8 + (unalignedBytes == 0 ? 0 : 1);

        ulong cs0 = 0;
        ulong cs1 = 0;
        ulong cs2 = 0;
        ulong cs3 = 0;

        if (dwordCount == 0)
        {
            u0 = u1 = u2 = u3 = 0;
            return;
        }

        if (dwordCount >= 1)
        {
            for (int j = 8; j > 0; j--)
            {
                cs0 <<= 8;
                if (j <= byteCount)
                {
                    cs0 |= bytes[byteCount - j];
                }
            }
        }

        if (dwordCount >= 2)
        {
            for (int j = 16; j > 8; j--)
            {
                cs1 <<= 8;
                if (j <= byteCount)
                {
                    cs1 |= bytes[byteCount - j];
                }
            }
        }

        if (dwordCount >= 3)
        {
            for (int j = 24; j > 16; j--)
            {
                cs2 <<= 8;
                if (j <= byteCount)
                {
                    cs2 |= bytes[byteCount - j];
                }
            }
        }

        if (dwordCount >= 4)
        {
            for (int j = 32; j > 24; j--)
            {
                cs3 <<= 8;
                if (j <= byteCount)
                {
                    cs3 |= bytes[byteCount - j];
                }
            }
        }

        u0 = cs0;
        u1 = cs1;
        u2 = cs2;
        u3 = cs3;
    }

    public void ToBigEndian(Span<byte> target)
    {
        if (target.Length == 32)
        {
            if (Avx2.IsSupported)
            {
                // Full 32-byte reversal is an involution, so this reuses the shuffle constant of the
                // big-endian read ctor (UInt256.Ctors.cs).
                Vector256<byte> data = Unsafe.As<ulong, Vector256<byte>>(ref Unsafe.AsRef(in u0));
                Vector256<byte> shuffle = Vector256.Create(
                    0x18191a1b1c1d1e1ful,
                    0x1011121314151617ul,
                    0x08090a0b0c0d0e0ful,
                    0x0001020304050607ul).AsByte();
                if (Avx512Vbmi.VL.IsSupported)
                {
                    Vector256<byte> convert = Avx512Vbmi.VL.PermuteVar32x8(data, shuffle);
                    Unsafe.WriteUnaligned(ref MemoryMarshal.GetReference(target), convert);
                }
                else
                {
                    Vector256<byte> convert = Avx2.Shuffle(data, shuffle);
                    Vector256<ulong> permute = Avx2.Permute4x64(convert.AsUInt64(), 0b_01_00_11_10);
                    Unsafe.WriteUnaligned(ref MemoryMarshal.GetReference(target), permute);
                }
            }
            else
            {
                BinaryPrimitives.WriteUInt64BigEndian(target.Slice(0, 8), u3);
                BinaryPrimitives.WriteUInt64BigEndian(target.Slice(8, 8), u2);
                BinaryPrimitives.WriteUInt64BigEndian(target.Slice(16, 8), u1);
                BinaryPrimitives.WriteUInt64BigEndian(target.Slice(24, 8), u0);
            }
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

    [DoesNotReturn, StackTraceHidden]
    private static void ThrowNotSupportedException() => throw new NotSupportedException();
}
