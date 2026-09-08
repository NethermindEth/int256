// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System.Numerics;
using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;
using Arm = System.Runtime.Intrinsics.Arm;
using x64 = System.Runtime.Intrinsics.X86;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    [SkipLocalsInit]
    private static void ExpOddLong(in UInt256 b, in UInt256 e, out UInt256 result)
    {
        // For odd b, b^2 = 1 mod 8. Each further square adds at least
        // one zero bit to b^(2^k)-1, hence b^(2^62) = 1 mod 2^64.
        // More precisely v2(b^(2^k)-1) = v2(b-1)+v2(b+1)+k-1.
        // The caller handles low limbs +/-1, leaving a cutoff in [1,62].
        // Exactly one of b-1 and b+1 has valuation one. Select the other
        // without a branch, so only one trailing-zero count is needed.
        int squares = 64 - BitOperations.TrailingZeroCount(b.u0 - 1 + (b.u0 & 2));
        // GPU proofs favor truncation when all prefix squares reach 32-bit precision.
        // Ordinary long prefixes retain their established guest schedule.
        if (squares <= 32)
        {
            ExpOddLongNear32(b, e, squares, out result);
            return;
        }
        UInt256 power = b;
        UInt256 value = (e.u0 & 1) != 0 ? b : One;
        ulong bits = e.u0 >> 1;
        for (int i = 1; i < squares; ++i)
        {
            SquareExpLong(power, out power);
            if ((bits & 1) != 0)
            {
                MultiplyExpPower(value, power, out value);
            }
            bits >>= 1;
        }
        SquareExpLong(power, out power);
        int left = 64 - squares;
        UInt256 high = new((e.u0 >> squares) | (e.u1 << left),
            (e.u1 >> squares) | (e.u2 << left), (e.u2 >> squares) | (e.u3 << left), e.u3 >> squares);
        ExpNearOne64(power, high, out power);
        Multiply(value, power, out result);
    }

    private const bool ExpPreferNarrowBinomial = true;

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
