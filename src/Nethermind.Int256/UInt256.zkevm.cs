// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;
using Arm = System.Runtime.Intrinsics.Arm;
using x64 = System.Runtime.Intrinsics.X86;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private const uint DefaultSeed = 2098026241U;

    /// <inheritdoc cref="UInt256.SeedHashes(uint)" />
    public static partial void SeedHashes(uint seed)
    {
        ulong aes0 = Spread(seed);

        RunSeed.Crc = unchecked(seed + 32u);
        RunSeed.Aes0 = aes0;
        RunSeed.Aes1 = Spread(aes0);
    }

    /// <summary>The seeds this run hashes with.</summary>
    /// <remarks>
    /// Guest execution has no entropy source, so these start from constants rather than from anything
    /// drawn at start-up, and stay stable across runs until <see cref="SeedHashes(uint)"/> replaces them.
    /// A type of their own so that mutating them leaves <see cref="UInt256"/>'s own statics immutable
    /// after their constructor, which is what lets NativeAOT freeze them. The initializers are constant
    /// expressions for the same reason.
    /// </remarks>
    private static class RunSeed
    {
        // The 32-byte input length rides in the CRC seed, so a UInt256 and a shorter key of the same
        // bytes do not walk the limbs with the same one.
        internal static uint Crc = unchecked(DefaultSeed + 32u);
        internal static ulong Aes0 = 0x1F83D9ABFB41BD6BUL;
        internal static ulong Aes1 = 0x5BE0CD19137E2179UL;
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public readonly override int GetHashCode()
    {
        if (x64.Aes.IsSupported || Arm.Aes.IsSupported)
        {
            Vector128<byte> key = Unsafe.As<ulong, Vector128<byte>>(ref Unsafe.AsRef(in u0));
            Vector128<byte> data = Unsafe.As<ulong, Vector128<byte>>(ref Unsafe.AsRef(in u2));
            key ^= Vector128.Create(RunSeed.Aes0, RunSeed.Aes1).AsByte();
            Vector128<byte> mixed = HashAesRound(data, key);
            mixed = HashAesRound(mixed, key);
            return FoldHash(MumFold(mixed));
        }

        return GetCrcHashCode(RunSeed.Crc);
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
