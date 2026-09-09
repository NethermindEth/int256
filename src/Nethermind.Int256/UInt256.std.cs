// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Buffers.Binary;
using System.IO.Hashing;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.X86;
using System.Security.Cryptography;
using Arm = System.Runtime.Intrinsics.Arm;
using x64 = System.Runtime.Intrinsics.X86;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    // Keep the binomial helpers and their spills out of the short-exponent frame.
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void ExpOddLong(in UInt256 b, in UInt256 e, int precision, out UInt256 result)
    {
        if (precision >= ExpFourTermPrecision)
            ExpOddLongPhased(b, e, 64 - precision, out result);
        else if (precision >= 32)
            ExpNearOne32Signed(b, e, precision >= 43, out result);
        else
            ExpOddLong32(b, e, 32 - precision, out result);
    }

    private const int ExpBinomialMinBits = 80;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void SquareExpLong(in UInt256 value, out UInt256 result)
        => value.Squared(out result);

    // Keep established host dispatch; short-path timings depend on ordering.
    private const bool ExpPreferDecimalLookup = false;

    // Native ARM amortizes sixteen entries; software products and x64 favor eight.
    private static int ExpWindowMaxWidth
    {
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        get => Arm.ArmBase.Arm64.IsSupported ? 5 : 4;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void MultiplyExpPower(in UInt256 value, in UInt256 power, out UInt256 result)
    {
        // Avoid repeated general width dispatch in the long-exponent loop.
        if ((power.u1 | power.u2 | power.u3) == 0)
            MultiplyByUInt64(value, power.u0, out result);
        else
            MultiplyLimbs4x4(value, power, out result);
    }

    // Keep wide multiplication spills off trivial host paths.
    private const MethodImplOptions MulModWideInlining = MethodImplOptions.NoInlining;

    // Expose the 128-bit reduction loop to its caller in the host JIT.
    private const MethodImplOptions MulMod128Inlining = MethodImplOptions.AggressiveInlining;

    // Vary the seed between processes to keep hash distribution independent across nodes and restarts.
    private static readonly ulong _aesHashSeed0 = CreateHashSeed();
    private static readonly ulong _aesHashSeed1 = CreateHashSeed();
    private static readonly long _xxHashSeed = unchecked((long)CreateHashSeed());

    [SkipLocalsInit]
    private static ulong CreateHashSeed()
    {
        Span<byte> bytes = stackalloc byte[sizeof(ulong)];
        RandomNumberGenerator.Fill(bytes);
        return BinaryPrimitives.ReadUInt64LittleEndian(bytes);
    }

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

        return GetXxHashCode(_xxHashSeed);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    internal readonly int GetXxHashCode(long seed)
    {
        ref byte start = ref Unsafe.As<ulong, byte>(ref Unsafe.AsRef(in u0));
        ulong hash = XxHash3.HashToUInt64(MemoryMarshal.CreateReadOnlySpan(ref start, 32), seed);
        return FoldHash((long)hash);
    }

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
        // Without AVX-512's native unsigned k-mask compare, the short-circuiting scalar limb compare
        // generally beats the AVX2 sign-flip emulation - see the LessThanPathAB benchmark.
        if (Avx512F.VL.IsSupported && Avx512DQ.IsSupported)
        {
            return LessThanAvx2(in a, in b);
        }

        // Retain the portable fallback for future runtimes: current x64 Vector256 support
        // requires AVX2, and current ARM64 runtimes do not accelerate Vector256.
        if (!Avx2.IsSupported && Vector256.IsHardwareAccelerated)
        {
            return LessThanVector256(in a, in b);
        }

        return LessThanScalar(in a, in b);
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
                // Currently reachable only through direct tests; see the portable fallback above.
                LessThanBothVector256(in x, in y, in m);
    }

    [OverloadResolutionPriority(1)]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public bool Equals(uint other)
        => Vector256.IsHardwareAccelerated
            ? EqualsVector(in this, other)
            : EqualsScalar(new UInt256(other));

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool EqualsVector(in UInt256 a, uint other)
        => (Vector256.CreateScalar(other) ^ Unsafe.BitCast<UInt256, Vector256<uint>>(a)) == Vector256<uint>.Zero;

    [OverloadResolutionPriority(1)]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public bool Equals(ulong other)
        => Vector256.IsHardwareAccelerated
            ? EqualsVector(in this, other)
            : EqualsScalar(new UInt256(other));

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool EqualsVector(in UInt256 a, ulong other)
        => (Vector256.CreateScalar(other) ^ Unsafe.BitCast<UInt256, Vector256<ulong>>(a)) == Vector256<ulong>.Zero;

    // SSE4.1 zero tests won here; the NEON candidate regressed dependent callers.
    [OverloadResolutionPriority(1)]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public bool Equals(in UInt256 other)
        => Vector256.IsHardwareAccelerated
            ? EqualsVector(in this, in other)
            : Sse41.IsSupported
                ? EqualsVector128(in this, in other)
                : EqualsScalar(in other);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool EqualsVector(in UInt256 a, in UInt256 b)
        => Unsafe.BitCast<UInt256, Vector256<ulong>>(a) == Unsafe.BitCast<UInt256, Vector256<ulong>>(b);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool EqualsVector128(in UInt256 a, in UInt256 b)
    {
        ref Vector128<ulong> av = ref Unsafe.As<UInt256, Vector128<ulong>>(ref Unsafe.AsRef(in a));
        ref Vector128<ulong> bv = ref Unsafe.As<UInt256, Vector128<ulong>>(ref Unsafe.AsRef(in b));
        return ((av ^ bv) | (Unsafe.Add(ref av, 1) ^ Unsafe.Add(ref bv, 1))) == Vector128<ulong>.Zero;
    }

    // This shared limb path lets the scalar JIT eliminate primitive-value temporaries.
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private bool EqualsScalar(in UInt256 other)
        => ((u0 ^ other.u0) | (u1 ^ other.u1) | (u2 ^ other.u2) | (u3 ^ other.u3)) == 0;

    // Keep direction-specific bodies: swapping operands changes which load the JIT can fold.
    // The operator wiring keeps its left operand in the second, memory-foldable source.
    // Integer blends for inclusive predicates and float blends for strict predicates were
    // selected together in Windows/Linux caller measurements; preserve these codegen shapes.
    // Pack equality into each low dword and the opposite ordering into each high dword.
    // One MoveMask then yields four base-4 digits: favorable=0, equal=1, opposite=2.
    // All-equal is 0x55; biasing by 0x56 includes equality. The mask is at most 0xAA,
    // so the sign of the biased result determines ordering without overflow ambiguity.
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool LessThanOrEqual(in UInt256 a, in UInt256 b)
    {
        if (Avx512F.VL.IsSupported)
        {
            Vector256<ulong> left = Unsafe.BitCast<UInt256, Vector256<ulong>>(a);
            Vector256<ulong> right = Unsafe.BitCast<UInt256, Vector256<ulong>>(b);
            Vector256<ulong> eq = Avx2.CompareEqual(left, right);
            Vector256<ulong> cmp = Avx512F.VL.CompareGreaterThan(left, right);
            uint mask = (uint)Avx.MoveMask(Avx2.Blend(eq.AsInt32(), cmp.AsInt32(), 0xAA).AsSingle());
            return unchecked((int)(mask - 0x56u)) < 0;
        }
        return !LessThan(in b, in a);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool GreaterThanOrEqual(in UInt256 a, in UInt256 b)
    {
        if (Avx512F.VL.IsSupported)
        {
            Vector256<ulong> left = Unsafe.BitCast<UInt256, Vector256<ulong>>(a);
            Vector256<ulong> right = Unsafe.BitCast<UInt256, Vector256<ulong>>(b);
            Vector256<ulong> eq = Avx2.CompareEqual(left, right);
            Vector256<ulong> cmp = Avx512F.VL.CompareLessThan(left, right);
            uint mask = (uint)Avx.MoveMask(Avx2.Blend(eq.AsInt32(), cmp.AsInt32(), 0xAA).AsSingle());
            return unchecked((int)(mask - 0x56u)) < 0;
        }
        return !LessThan(in a, in b);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool GreaterThan(in UInt256 a, in UInt256 b)
    {
        if (Avx512F.VL.IsSupported)
        {
            Vector256<ulong> left = Unsafe.BitCast<UInt256, Vector256<ulong>>(a);
            Vector256<ulong> right = Unsafe.BitCast<UInt256, Vector256<ulong>>(b);
            Vector256<ulong> eq = Avx2.CompareEqual(left, right);
            Vector256<ulong> cmp = Avx512F.VL.CompareLessThan(left, right);
            uint mask = (uint)Avx.MoveMask(Avx.Blend(eq.AsSingle(), cmp.AsSingle(), 0xAA));
            return unchecked((int)(mask - 0x55u)) < 0;
        }
        return LessThan(in b, in a);
    }

    // Keep the operator reduction separate from the shared Min/Max comparison path.
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool LessThanOperator(in UInt256 a, in UInt256 b)
    {
        if (Avx512F.VL.IsSupported)
        {
            Vector256<ulong> left = Unsafe.BitCast<UInt256, Vector256<ulong>>(a);
            Vector256<ulong> right = Unsafe.BitCast<UInt256, Vector256<ulong>>(b);
            Vector256<ulong> eq = Avx2.CompareEqual(left, right);
            Vector256<ulong> cmp = Avx512F.VL.CompareGreaterThan(left, right);
            uint mask = (uint)Avx.MoveMask(Avx.Blend(eq.AsSingle(), cmp.AsSingle(), 0xAA));
            return unchecked((int)(mask - 0x55u)) < 0;
        }
        return LessThan(in a, in b);
    }
}
