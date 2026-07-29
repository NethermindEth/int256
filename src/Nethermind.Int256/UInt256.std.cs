// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.X86;
using System.Security.Cryptography;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    // Vary the seed between processes to keep hash distribution independent across nodes and restarts.
    private static readonly uint _hashSeed =
        (uint)RandomNumberGenerator.GetInt32(int.MinValue, int.MaxValue);

    // Vector256 paths live in separate helpers to keep the public bodies small enough to inline.
    public bool IsZero
    {
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        get => Vector256.IsHardwareAccelerated ? IsZeroVector(in this) : (u0 | u1 | u2 | u3) == 0;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool IsZeroVector(in UInt256 a)
        => Unsafe.BitCast<UInt256, Vector256<ulong>>(a) == default;

    public bool IsOne
    {
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        get => Vector256.IsHardwareAccelerated ? IsOneVector(in this) : ((u0 ^ 1UL) | u1 | u2 | u3) == 0;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool IsOneVector(in UInt256 a)
        => Unsafe.BitCast<UInt256, Vector256<ulong>>(a) == Vector256.CreateScalar(1UL);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void Not(in UInt256 a, out UInt256 res)
    {
        if (Vector256.IsHardwareAccelerated)
        {
            NotVector(in a, out res);
            return;
        }
        res = new UInt256(~a.u0, ~a.u1, ~a.u2, ~a.u3);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void NotVector(in UInt256 a, out UInt256 res)
        => res = Unsafe.BitCast<Vector256<ulong>, UInt256>(~Unsafe.BitCast<UInt256, Vector256<ulong>>(a));

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void Or(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        if (Vector256.IsHardwareAccelerated)
        {
            OrVector(in a, in b, out res);
            return;
        }
        res = new UInt256(a.u0 | b.u0, a.u1 | b.u1, a.u2 | b.u2, a.u3 | b.u3);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void OrVector(in UInt256 a, in UInt256 b, out UInt256 res)
        => res = Unsafe.BitCast<Vector256<ulong>, UInt256>(
            Unsafe.BitCast<UInt256, Vector256<ulong>>(a) | Unsafe.BitCast<UInt256, Vector256<ulong>>(b));

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void And(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        if (Vector256.IsHardwareAccelerated)
        {
            AndVector(in a, in b, out res);
            return;
        }
        res = new UInt256(a.u0 & b.u0, a.u1 & b.u1, a.u2 & b.u2, a.u3 & b.u3);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void AndVector(in UInt256 a, in UInt256 b, out UInt256 res)
        => res = Unsafe.BitCast<Vector256<ulong>, UInt256>(
            Unsafe.BitCast<UInt256, Vector256<ulong>>(a) & Unsafe.BitCast<UInt256, Vector256<ulong>>(b));

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void Xor(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        if (Vector256.IsHardwareAccelerated)
        {
            XorVector(in a, in b, out res);
            return;
        }
        res = new UInt256(a.u0 ^ b.u0, a.u1 ^ b.u1, a.u2 ^ b.u2, a.u3 ^ b.u3);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void XorVector(in UInt256 a, in UInt256 b, out UInt256 res)
        => res = Unsafe.BitCast<Vector256<ulong>, UInt256>(
            Unsafe.BitCast<UInt256, Vector256<ulong>>(a) ^ Unsafe.BitCast<UInt256, Vector256<ulong>>(b));

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool LessThan(in UInt256 a, in UInt256 b)
    {
        if (!Avx2.IsSupported && !Vector256.IsHardwareAccelerated)
        {
            return LessThanScalar(in a, in b);
        }

        return Avx2.IsSupported ?
            LessThanAvx2(in a, in b) :
            LessThanVector256(in a, in b);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool LessThanBoth(in UInt256 x, in UInt256 y, in UInt256 m)
    {
        if (!Avx2.IsSupported && !Vector256.IsHardwareAccelerated)
        {
            return LessThanScalar(in x, in m) && LessThanScalar(in y, in m);
        }

        return Avx512F.VL.IsSupported && Avx512DQ.IsSupported ?
            LessThanBothAvx512(in x, in y, in m) :
            Avx2.IsSupported ?
                LessThanBothAvx2(in x, in y, in m) :
                LessThanBothVector256(in x, in y, in m);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public bool Equals(uint other)
        => Vector256.IsHardwareAccelerated ? EqualsVector(in this, other) : u0 == other && IsUint64;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool EqualsVector(in UInt256 a, uint other)
        => Unsafe.BitCast<UInt256, Vector256<uint>>(a) == Vector256.CreateScalar(other);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public bool Equals(ulong other)
        => Vector256.IsHardwareAccelerated ? EqualsVector(in this, other) : u0 == other && IsUint64;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool EqualsVector(in UInt256 a, ulong other)
        => Unsafe.BitCast<UInt256, Vector256<ulong>>(a) == Vector256.CreateScalar(other);

    [OverloadResolutionPriority(1)]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public bool Equals(in UInt256 other)
        => Vector256.IsHardwareAccelerated
            ? EqualsVector(in this, in other)
            : ((u0 ^ other.u0) | (u1 ^ other.u1) | (u2 ^ other.u2) | (u3 ^ other.u3)) == 0;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool EqualsVector(in UInt256 a, in UInt256 b)
        => Unsafe.BitCast<UInt256, Vector256<ulong>>(a) == Unsafe.BitCast<UInt256, Vector256<ulong>>(b);
}
