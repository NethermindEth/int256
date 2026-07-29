// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System.Runtime.CompilerServices;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    // Guest execution requires stable hashes across runs.
    private static readonly uint _hashSeed = 2098026241U;

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

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public bool Equals(uint other)
        => u0 == other && (u1 | u2 | u3) == 0;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public bool Equals(ulong other)
        => u0 == other && (u1 | u2 | u3) == 0;

    [OverloadResolutionPriority(1)]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public bool Equals(in UInt256 other)
        => ((u0 ^ other.u0) | (u1 ^ other.u1) | (u2 ^ other.u2) | (u3 ^ other.u3)) == 0;
}
