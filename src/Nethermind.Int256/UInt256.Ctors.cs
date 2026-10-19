// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Buffers.Binary;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.Arm;
using System.Runtime.Intrinsics.X86;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    public UInt256(uint r0, uint r1, uint r2, uint r3, uint r4, uint r5, uint r6, uint r7)
    {
        if (Vector256.IsHardwareAccelerated)
        {
            Unsafe.SkipInit(out this.u0);
            Unsafe.SkipInit(out this.u1);
            Unsafe.SkipInit(out this.u2);
            Unsafe.SkipInit(out this.u3);
            Unsafe.As<ulong, Vector256<uint>>(ref this.u0) = Vector256.Create(r0, r1, r2, r3, r4, r5, r6, r7);
        }
        else
        {
            u0 = (ulong)r1 << 32 | r0;
            u1 = (ulong)r3 << 32 | r2;
            u2 = (ulong)r5 << 32 | r4;
            u3 = (ulong)r7 << 32 | r6;
        }
    }

    public UInt256(ulong u0 = 0, ulong u1 = 0, ulong u2 = 0, ulong u3 = 0)
    {
        this.u0 = u0;
        this.u1 = u1;
        this.u2 = u2;
        this.u3 = u3;
    }

    /// <summary>Reads a value from its bytes.</summary>
    /// <param name="bytes">
    /// The bytes. Only a 32-byte span is read in the order <paramref name="isBigEndian"/> selects. Any other length
    /// is read big-endian whatever <paramref name="isBigEndian"/> says: a shorter span is zero-extended and a
    /// longer one keeps its last 32 bytes. For a short little-endian span, use
    /// <see cref="IBinaryInteger{TSelf}.ReadLittleEndian(ReadOnlySpan{byte}, bool)"/>.
    /// </param>
    /// <param name="isBigEndian">Whether a 32-byte span is big-endian.</param>
    public UInt256(in ReadOnlySpan<byte> bytes, bool isBigEndian = false)
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
                    ReadBigEndianLimbs(bytes, out u0, out u1, out u2, out u3);
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

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void ReadBigEndianLimbs(ReadOnlySpan<byte> bytes, out ulong u0, out ulong u1, out ulong u2, out ulong u3)
    {
        Debug.Assert(bytes.Length >= 32);
        ref byte source = ref MemoryMarshal.GetReference(bytes);
        u3 = ReadUInt64BigEndian(ref source);
        u2 = ReadUInt64BigEndian(ref Unsafe.Add(ref source, 8));
        u1 = ReadUInt64BigEndian(ref Unsafe.Add(ref source, 16));
        u0 = ReadUInt64BigEndian(ref Unsafe.Add(ref source, 24));
    }

    // Any length other than 32 is read big-endian (see the constructor): the whole words from the end, then the
    // leading partial word byte by byte. A longer span keeps its last 32 bytes.
    private static void Create(ReadOnlySpan<byte> bytes, out ulong u0, out ulong u1, out ulong u2, out ulong u3)
    {
        if (bytes.Length >= 32)
        {
            ReadBigEndianLimbs(bytes[^32..], out u0, out u1, out u2, out u3);
            return;
        }

        ref byte source = ref MemoryMarshal.GetReference(bytes);
        int head = bytes.Length & 7;
        ulong partial = 0;
        for (int i = 0; i < head; i++)
        {
            partial = (partial << 8) | Unsafe.Add(ref source, i);
        }

        // The whole words follow the partial one, most significant first.
        ref byte words = ref Unsafe.Add(ref source, head);
        switch (bytes.Length >> 3)
        {
            case 0:
                (u0, u1, u2, u3) = (partial, 0, 0, 0);
                break;
            case 1:
                (u0, u1, u2, u3) = (ReadUInt64BigEndian(ref words), partial, 0, 0);
                break;
            case 2:
                (u0, u1, u2, u3) = (ReadUInt64BigEndian(ref Unsafe.Add(ref words, 8)), ReadUInt64BigEndian(ref words), partial, 0);
                break;
            default:
                (u0, u1, u2, u3) = (ReadUInt64BigEndian(ref Unsafe.Add(ref words, 16)),
                    ReadUInt64BigEndian(ref Unsafe.Add(ref words, 8)), ReadUInt64BigEndian(ref words), partial);
                break;
        }
    }

    public UInt256(in ReadOnlySpan<ulong> data, bool isBigEndian = false)
    {
        if (isBigEndian)
        {
            u3 = data[0];
            u2 = data[1];
            u1 = data[2];
            u0 = data[3];
        }
        else
        {
            if (Vector256.IsHardwareAccelerated)
            {
                Unsafe.SkipInit(out this.u0);
                Unsafe.SkipInit(out this.u1);
                Unsafe.SkipInit(out this.u2);
                Unsafe.SkipInit(out this.u3);
                Unsafe.As<ulong, Vector256<ulong>>(ref this.u0) = Vector256.Create<ulong>(data);
            }
            else
            {
                u0 = data[0];
                u1 = data[1];
                u2 = data[2];
                u3 = data[3];
            }
        }
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static UInt256 Create(ulong u0, ulong u1, ulong u2, ulong u3)
        => new(u0, u1, u2, u3);
}
