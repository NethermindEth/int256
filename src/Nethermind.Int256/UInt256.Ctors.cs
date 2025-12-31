// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Buffers.Binary;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics;
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
        if (Vector256.IsHardwareAccelerated)
        {
            Unsafe.SkipInit(out this.u0);
            Unsafe.SkipInit(out this.u1);
            Unsafe.SkipInit(out this.u2);
            Unsafe.SkipInit(out this.u3);
            Unsafe.As<ulong, Vector256<ulong>>(ref this.u0) = Vector256.Create(u0, u1, u2, u3);
        }
        else
        {
            this.u0 = u0;
            this.u1 = u1;
            this.u2 = u2;
            this.u3 = u3;
        }
    }

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
    {
        if (Vector256.IsHardwareAccelerated)
        {
            Vector256<ulong> v = Vector256.Create(u0, u1, u2, u3);
            return Unsafe.As<Vector256<ulong>, UInt256>(ref v);
        }
        else
        {
            Unsafe.SkipInit(out UInt256 r);
            ref ulong p = ref Unsafe.As<UInt256, ulong>(ref r);
            p = u0;
            Unsafe.Add(ref p, 1) = u1;
            Unsafe.Add(ref p, 2) = u2;
            Unsafe.Add(ref p, 3) = u3;
            return r;
        }
    }
}
