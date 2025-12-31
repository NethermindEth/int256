// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.Arm;
using System.Runtime.Intrinsics.X86;

[assembly: InternalsVisibleTo("Nethermind.Int256.Tests")]

namespace Nethermind.Int256;

[StructLayout(LayoutKind.Explicit)]
public readonly partial struct UInt256 : IEquatable<UInt256>, IComparable, IComparable<UInt256>, IInteger<UInt256>, IConvertible
{
    public const int Len = 4;
    // Ensure that hashes are different for every run of the node and every node, so if are any hash collisions on
    // one node they will not be the same on another node or across a restart so hash collision cannot be used to degrade
    // the performance of the network as a whole.
    private static readonly uint s_instanceRandom = (uint)System.Security.Cryptography.RandomNumberGenerator.GetInt32(int.MinValue, int.MaxValue);

    public static readonly UInt256 Zero = 0ul;
    public static readonly UInt256 One = 1ul;
    public static readonly UInt256 MinValue = Zero;
    public static readonly UInt256 MaxValue = ~Zero;
    public static readonly UInt256 UInt128MaxValue = new(ulong.MaxValue, ulong.MaxValue);

    /* in little endian order so u3 is the most significant ulong */
    [FieldOffset(0)]
    public readonly ulong u0;
    [FieldOffset(8)]
    public readonly ulong u1;
    [FieldOffset(16)]
    public readonly ulong u2;
    [FieldOffset(24)]
    public readonly ulong u3;

    public static UInt256 Negate(in UInt256 a)
    {
        ulong cs0 = 0 - a.u0;
        ulong cs1 = 0 - a.u1;
        ulong cs2 = 0 - a.u2;
        ulong cs3 = 0 - a.u3;
        if (a.u0 > 0)
            cs3--;

        return new UInt256(cs0, cs1, cs2, cs3);
    }

    public (ulong value, bool overflow) UlongWithOverflow => (u0, (u1 | u2 | u3) != 0);

    public bool IsZero
    {
        get
        {
            if (Vector256.IsHardwareAccelerated)
            {
                Vector256<ulong> v = Unsafe.As<ulong, Vector256<ulong>>(ref Unsafe.AsRef(in u0));
                return v == default;
            }
            else
            {
                return (u0 | u1 | u2 | u3) == 0;
            }
        }
    }

    public bool IsOne
    {
        get
        {
            if (Vector256.IsHardwareAccelerated)
            {
                Vector256<ulong> v = Unsafe.As<ulong, Vector256<ulong>>(ref Unsafe.AsRef(in u0));
                return v == Vector256.CreateScalar(1UL);
            }
            else
            {
                return ((u0 ^ 1UL) | u1 | u2 | u3) == 0;
            }
        }
    }

    public bool IsZeroOrOne => ((u0 >> 1) | u1 | u2 | u3) == 0;

    public UInt256 ZeroValue => Zero;

    public UInt256 OneValue => One;

    public UInt256 MaximalValue => MaxValue;

    /// <summary>
    /// Adds two <see cref="UInt256"/> values and returns the wrapped 256-bit result.
    /// </summary>
    /// <remarks>
    /// Stores the low 256 bits of <c>a + b</c> in <paramref name="res"/>.
    /// Overflow (carry out of the most-significant bit) is ignored - the result wraps modulo <c>2^256</c>.
    /// Use <see cref="AddOverflow(in UInt256, in UInt256, out UInt256)"/> to detect overflow.
    /// </remarks>
    /// <param name="a">The first 256-bit addend.</param>
    /// <param name="b">The second 256-bit addend.</param>
    /// <param name="res">On return, contains <c>(a + b) mod 2^256</c>.</param>
    public static void Add(in UInt256 a, in UInt256 b, out UInt256 res)
        => AddOverflow(in a, in b, out res);

    /// <summary>
    /// Adds two <see cref="UInt256"/> values and reports whether the addition overflowed.
    /// </summary>
    /// <remarks>
    /// Computes the full 256-bit sum of <paramref name="a"/> and <paramref name="b"/> and stores the low 256 bits in
    /// <paramref name="res"/>. The return value indicates whether the true mathematical sum exceeded the range
    /// <c>[0, 2^256 - 1]</c>.
    /// </remarks>
    /// <param name="a">The first 256-bit addend.</param>
    /// <param name="b">The second 256-bit addend.</param>
    /// <param name="res">
    /// On return, contains the low 256 bits of <c>a + b</c>.
    /// </param>
    /// <returns>
    /// <see langword="true"/> if <c>a + b</c> overflowed (carry out of the most-significant bit); otherwise <see langword="false"/>.
    /// </returns>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool AddOverflow(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        if (!Avx2.IsSupported && !Vector256.IsHardwareAccelerated)
        {
            return AddScalar(in a, in b, out res);
        }

        return Avx2.IsSupported ?
            AddAvx2(in a, in b, out res) :
            AddVector256(in a, in b, out res);
    }

    private static bool AddScalar(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        ulong a0 = a.u0;
        ulong b0 = b.u0;
        if ((a.u1 | a.u2 | a.u3 | b.u1 | b.u2 | b.u3) == 0)
        {
            // Fast add for numbers less than 2^64 (18,446,744,073,709,551,615)
            ulong u0 = a0 + b0;
            // Assignment to res after in case is used as input for a or b (by ref aliasing)
            res = default;
            Unsafe.AsRef(in res.u0) = u0;
            if (u0 < a0)
            {
                Unsafe.AsRef(in res.u1) = 1;
            }
            // Never overflows UInt256
            return false;
        }

        ulong c = 0;
        AddWithCarry(a0, b0, ref c, out ulong r0);
        AddWithCarry(a.u1, b.u1, ref c, out ulong r1);
        AddWithCarry(a.u2, b.u2, ref c, out ulong r2);
        AddWithCarry(a.u3, b.u3, ref c, out ulong r3);
        res = new UInt256(r0, r1, r2, r3);
        return c != 0;
    }

    private static bool AddAvx2(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        Vector256<ulong> av = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in a));
        Vector256<ulong> bv = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in b));

        Vector256<ulong> result = Avx2.Add(av, bv);
        Vector256<ulong> vCarry;
        if (Avx512F.VL.IsSupported)
        {
            vCarry = Avx512F.VL.CompareLessThan(result, av);
        }
        else
        {
            // Work around for missing Vector256.CompareLessThan
            Vector256<ulong> carryFromBothHighBits = Avx2.And(av, bv);
            Vector256<ulong> eitherHighBit = Avx2.Or(av, bv);
            Vector256<ulong> highBitNotInResult = Avx2.AndNot(result, eitherHighBit);

            // Set high bits where carry occurs
            vCarry = Avx2.Or(carryFromBothHighBits, highBitNotInResult);
        }
        // Move carry from Vector space to uint
        uint carry = (uint)(Avx512DQ.IsSupported ?
            Avx512DQ.MoveMask(vCarry) :
            Avx.MoveMask(vCarry.AsDouble()));

        // All bits set will cascade another carry when carry is added to it
        Vector256<ulong> vCascade = Avx2.CompareEqual(result, Vector256<ulong>.AllBitsSet);
        // Move cascade from Vector space to uint
        uint cascade = (uint)(Avx512DQ.IsSupported ?
            Avx512DQ.MoveMask(vCascade) :
            Avx.MoveMask(Unsafe.As<Vector256<ulong>, Vector256<double>>(ref vCascade)));

        // Use ints to work out the Vector cross lane cascades
        // Move carry to next bit and add cascade
        carry = cascade + 2 * carry; // lea
        // Remove cascades not affected by carry
        cascade ^= carry;
        // Choice of 16 vectors
        cascade &= 0x0f;

        // Lookup the carries to broadcast to the Vectors
        Vector256<ulong> cascadedCarries = Unsafe.Add(ref Unsafe.As<byte, Vector256<ulong>>(ref MemoryMarshal.GetReference(BroadcastLookup)), cascade);

        // Mark res as initialized so we can use it as left side of ref assignment
        Unsafe.SkipInit(out res);
        // Add the cascadedCarries to the result
        Unsafe.As<UInt256, Vector256<ulong>>(ref res) = Avx2.Add(result, cascadedCarries);

        return (carry & 0b1_0000) != 0;
    }

    private static bool AddVector256(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        Vector256<ulong> av = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in a));
        Vector256<ulong> bv = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in b));

        Vector256<ulong> result = Vector256.Add(av, bv);
        Vector256<ulong> vCarry = Vector256.LessThan(result, av);

        uint carry = Vector256.ExtractMostSignificantBits(vCarry);

        // All bits set will cascade another carry when carry is added to it
        Vector256<ulong> vCascade = Vector256.Equals(result, Vector256<ulong>.AllBitsSet);
        // Move cascade from Vector space to uint
        uint cascade = Vector256.ExtractMostSignificantBits(vCascade);

        // Use ints to work out the Vector cross lane cascades
        // Move carry to next bit and add cascade
        carry = cascade + 2 * carry; // lea
        // Remove cascades not affected by carry
        cascade ^= carry;
        // Choice of 16 vectors
        cascade &= 0x0f;

        // Lookup the carries to broadcast to the Vectors
        Vector256<ulong> cascadedCarries = Unsafe.Add(ref Unsafe.As<byte, Vector256<ulong>>(ref MemoryMarshal.GetReference(BroadcastLookup)), cascade);

        // Mark res as initialized so we can use it as left side of ref assignment
        Unsafe.SkipInit(out res);
        // Add the cascadedCarries to the result
        Unsafe.As<UInt256, Vector256<ulong>>(ref res) = Vector256.Add(result, cascadedCarries);

        return (carry & 0b1_0000) != 0;
    }

    /// <summary>
    /// Adds this value and <paramref name="a"/> and returns the wrapped 256-bit result.
    /// </summary>
    /// <remarks>
    /// Stores the low 256 bits of <c>this + a</c> in <paramref name="res"/>.
    /// Overflow is ignored - the result wraps modulo <c>2^256</c>.
    /// Use <see cref="AddOverflow(in UInt256, in UInt256, out UInt256)"/> to detect overflow.
    /// </remarks>
    /// <param name="a">The other 256-bit addend.</param>
    /// <param name="res">On return, contains <c>(this + a) mod 2^256</c>.</param>
    public void Add(in UInt256 a, out UInt256 res) => AddOverflow(this, a, out res);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void AddWithCarry(ulong x, ulong y, ref ulong carry, out ulong sum)
    {
        ulong t = x + y;
        ulong r = t + carry;
        carry = (t < x ? 1UL : 0UL) + (r < t ? 1UL : 0UL);
        sum = r;
    }

    // It avoids c#'s way of shifting a 64-bit number by 64-bit, i.e. in c# a << 64 == a, in our version a << 64 == 0.
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    internal static ulong Lsh(ulong a, int n)
    {
        var n1 = n >> 1;
        var n2 = n - n1;
        return (a << n1) << n2;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    internal static ulong Rsh(ulong a, int n)
    {
        var n1 = n >> 1;
        var n2 = n - n1;
        return (a >> n1) >> n2;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    internal static ulong NativeLsh(ulong a, int n)
    {
        Debug.Assert(n < 64);
        return a << n;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    internal static ulong NativeRsh(ulong a, int n)
    {
        Debug.Assert(n < 64);
        return a >> n;
    }

    // Subtract sets res to the difference a-b
    public static void Subtract(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        SubtractImpl(in a, in b, out res);
    }

    // Subtract sets res to the difference a-b
    private static bool SubtractImpl(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        if (Avx2.IsSupported)
        {
            Vector256<ulong> av = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in a));
            Vector256<ulong> bv = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in b));

            Vector256<ulong> result = Avx2.Subtract(av, bv);
            Vector256<ulong> vBorrow;
            if (Avx512F.VL.IsSupported)
            {
                vBorrow = Avx512F.VL.CompareGreaterThan(result, av);
            }
            else
            {
                // Invert top bits as Avx2.CompareGreaterThan is only available for longs, not unsigned
                Vector256<ulong> signFlip = Vector256.Create(0x8000_0000_0000_0000UL);
                Vector256<ulong> resultSigned = Avx2.Xor(result, signFlip);
                Vector256<ulong> avSigned = Avx2.Xor(av, signFlip);

                // Which vectors need to borrow from the next
                vBorrow = Avx2.CompareGreaterThan(resultSigned.AsInt64(), avSigned.AsInt64()).AsUInt64();
            }
            // Move borrow from Vector space to int
            int borrow = Avx.MoveMask(vBorrow.AsDouble());

            // All zeros will cascade another borrow when borrow is subtracted from it
            Vector256<ulong> vCascade = Avx2.CompareEqual(result, Vector256<ulong>.Zero);
            // Move cascade from Vector space to int
            int cascade = Avx.MoveMask(vCascade.AsDouble());

            // Use ints to work out the Vector cross lane cascades
            // Move borrow to next bit and add cascade
            borrow = cascade + 2 * borrow; // lea
            // Remove cascades not effected by borrow
            cascade ^= borrow;
            // Choice of 16 vectors
            cascade &= 0x0f;

            // Lookup the borrows to broadcast to the Vectors
            Vector256<ulong> cascadedBorrows = Unsafe.Add(ref Unsafe.As<byte, Vector256<ulong>>(ref MemoryMarshal.GetReference(BroadcastLookup)), cascade);

            // Mark res as initialized so we can use it as left said of ref assignment
            Unsafe.SkipInit(out res);
            // Subtract the cascadedBorrows from the result
            Unsafe.As<UInt256, Vector256<ulong>>(ref res) = Avx2.Subtract(result, cascadedBorrows);
            return (borrow & 0b1_0000) != 0;
        }
        else
        {
            ulong borrow = 0ul;
            SubtractWithBorrow(a.u0, b.u0, ref borrow, out ulong res0);
            SubtractWithBorrow(a.u1, b.u1, ref borrow, out ulong res1);
            SubtractWithBorrow(a.u2, b.u2, ref borrow, out ulong res2);
            SubtractWithBorrow(a.u3, b.u3, ref borrow, out ulong res3);
            res = new UInt256(res0, res1, res2, res3);
            return borrow != 0;
        }
    }

    public void Subtract(in UInt256 b, out UInt256 res) => Subtract(this, b, out res);

    public static void SubtractMod(in UInt256 a, in UInt256 b, in UInt256 m, out UInt256 res)
    {
        if (SubtractUnderflow(a, b, out UInt256 intermediate))
        {
            Subtract(b, a, out intermediate);
            Mod(intermediate, m, out intermediate);
            if (!intermediate.IsZero)
            {
                Subtract(m, intermediate, out intermediate);
            }
        }
        else
        {
            Mod(intermediate, m, out intermediate);
        }

        res = intermediate;
    }

    public void SubtractMod(in UInt256 a, in UInt256 m, out UInt256 res) => SubtractMod(this, a, m, out res);

    // SubtractUnderflow sets res to the difference a-b and returns true if the operation underflowed
    public static bool SubtractUnderflow(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        return SubtractImpl(a, b, out res);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void SubtractWithBorrow(ulong a, ulong b, ref ulong borrow, out ulong res)
    {
        ulong result = a - b - borrow;
        borrow = (((~a) & b) | (~(a ^ b)) & result) >> 63;
        res = result;
    }

    /// <summary>
    /// Multiplies two 256‑bit unsigned integers (<paramref name="x"/> and <paramref name="y"/>) and
    /// writes the 256‑bit product to <paramref name="res"/>.
    /// </summary>
    /// <param name="x">The first 256‑bit unsigned integer.</param>
    /// <param name="y">The second 256‑bit unsigned integer.</param>
    /// <param name="res">When this method returns, contains the 256‑bit product of x and y.</param>
    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void Multiply(in UInt256 x, in UInt256 y, out UInt256 res)
    {
        if (y.IsZero || x.IsZero)
        {
            res = default;
            return;
        }
        if (y.IsOne)
        {
            res = x;
            return;
        }
        if (x.IsOne)
        {
            res = y;
            return;
        }

        // If both inputs fit in 64 bits, use a simple multiplication routine.
        if (x.IsUint64 && y.IsUint64)
        {
            // Fast multiply for numbers less than 2^64 (18,446,744,073,709,551,615)
            ulong high = Multiply64(x.u0, y.u0, out ulong low);
            // Assignment to res after multiply in case is used as input for x or y (by ref aliasing)
            res = default;
            Unsafe.AsRef(in res.u0) = low;
            Unsafe.AsRef(in res.u1) = high;
            return;
        }

        // Recent optimizations have made scalar faster
        if (false && Avx512F.IsSupported && Avx512DQ.IsSupported && Avx512DQ.VL.IsSupported)
        {
            MultiplyAvx512F(in x, in y, out res);
        }
        else
        {
            MultiplyScalar(in x, in y, out res);
        }
    }

    [SkipLocalsInit]
    private static void MultiplyScalar(in UInt256 x, in UInt256 y, out UInt256 res)
    {
        ulong x0 = x.u0;
        ulong y0 = y.u0;
        ulong x1 = x.u1;
        ulong y1 = y.u1;
        ulong x2 = x.u2;
        ulong y2 = y.u2;

        Unsafe.SkipInit(out res);
        ref ulong pr = ref Unsafe.As<UInt256, ulong>(ref res);

        ulong a0 = Multiply64(x0, y0, out pr);

        // Column 1
        ulong a1 = 0;
        ulong a2 = 0;
        MultiplyAddCarry(ref a0, ref a1, ref a2, x0, y1);
        MultiplyAddCarry(ref a0, ref a1, ref a2, x1, y0);
        Unsafe.Add(ref pr, 1) = a0;

        // carry into column 2 is (a2:a1) as a 128-bit value, aligned as (lo=a1, hi=a2)

        // Column 2
        a0 = a1;
        a1 = a2;
        a2 = 0;
        MultiplyAddCarry(ref a0, ref a1, ref a2, x0, y2);
        MultiplyAddCarry(ref a0, ref a1, ref a2, x1, y1);
        MultiplyAddCarry(ref a0, ref a1, ref a2, x2, y0);
        ulong s1 = x0 * y.u3 + x.u3 * y0;
        ulong s0 = x1 * y2 + x2 * y1;
        Unsafe.Add(ref pr, 2) = a0;

        // For r3 we only need the low 64 of the incoming carry, which is a1 here.
        Unsafe.Add(ref pr, 3) = a1 + s0 + s1;
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void MultiplyAddCarry(ref ulong a0, ref ulong a1, ref ulong a2, ulong x, ulong y)
    {
        ulong hi = Multiply64(x, y, out ulong lo);

        // a0 += lo; c0 = carry out
        ulong s0 = a0 + lo;
        ulong c0 = s0 < a0 ? 1UL : 0UL;
        a0 = s0;

        // a1 += hi + c0; c1 = carry out (0..2)
        ulong s1 = a1 + hi;
        ulong c1 = s1 < a1 ? 1UL : 0UL;
        s1 += c0;
        c1 += s1 < c0 ? 1UL : 0UL;
        a1 = s1;

        // a2 += c1 (a2 stays small here)
        a2 += c1;
    }

    [SkipLocalsInit]
    private static void MultiplyAvx512F(in UInt256 x, in UInt256 y, out UInt256 res)
    {
        Vector256<ulong> vecX = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in x));
        Vector256<ulong> vecY = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in y));

        // Load the inputs and prepare the mask constant.
        Vector512<ulong> mask32 = Vector512.Create(0xFFFFFFFFUL);

        // Indices that reproduce the layout:
        // xRearranged = [ x0, x0, x1, x0,  x1, x2, x0, x1 ]
        // yRearranged = [ y0, y1, y0, y2,  y1, y0, y3, y2 ]
        Vector512<ulong> idxX = Vector512.Create(0UL, 0UL, 1UL, 0UL, 1UL, 2UL, 0UL, 1UL);
        Vector512<ulong> idxY = Vector512.Create(0UL, 1UL, 0UL, 2UL, 1UL, 0UL, 3UL, 2UL);

        // Lane setup - pure shuffle work.
        // Replace 4x Permute4x64 (ymm) + 4x InsertVector256 (zmm) with:
        // 2x InsertVector256 (just put vecX/vecY in low half) + 2x PermuteVar8x64 (zmm).

        Vector512<ulong> z = Vector512<ulong>.Zero;

        // Put vecX/vecY into the low 256 bits only.
        // Upper 256 bits remain zero, which is fine because we only index 0..3.
        Vector512<ulong> xRearranged = Avx512F.InsertVector256(z, vecX, 0);
        Vector512<ulong> yRearranged = Avx512F.InsertVector256(z, vecY, 0);
        xRearranged = Avx512F.PermuteVar8x64(xRearranged, idxX);
        yRearranged = Avx512F.PermuteVar8x64(yRearranged, idxY);

        // "Side multiplies" - independent of the 32x32 widening multiplies.
        // Low-only products we need for limb3 later: p21_lo and p30_lo.
        Vector128<ulong> xHigh = Avx2.ExtractVector128(vecX, 1);  // [x2, x3]

        // yRearranged elements 4..5 are [y1, y0] -> 128-bit lane index 2
        Vector128<ulong> yLow = Avx512F.ExtractVector128(yRearranged, 2); // [y1, y0]

        Vector128<ulong> finalProdLow = Avx512DQ.VL.MultiplyLow(xHigh, yLow); // [p21_lo, p30_lo]

        // 32x32 widening multiplies. This block is the "main event"
        // everything around it should try to overlap with it.
        Vector512<ulong> xUpperParts = Avx512F.ShiftRightLogical(xRearranged, 32);
        Vector512<ulong> yUpperParts = Avx512F.ShiftRightLogical(yRearranged, 32);

        Vector512<ulong> prodLL = Avx512F.Multiply(xRearranged.AsUInt32(), yRearranged.AsUInt32()); // low(x)  * low(y)
        Vector512<ulong> prodHL = Avx512F.Multiply(xUpperParts.AsUInt32(), yRearranged.AsUInt32()); // high(x) * low(y)
        Vector512<ulong> prodHH = Avx512F.Multiply(xUpperParts.AsUInt32(), yUpperParts.AsUInt32()); // high(x) * high(y)
        Vector512<ulong> prodLH = Avx512F.Multiply(xRearranged.AsUInt32(), yUpperParts.AsUInt32()); // low(x)  * high(y)

        // 64x64 reconstruction.
        // Mostly ALU ops (vpaddq/vpsrlq/vpsllq) - lower pressure than shuffles.
        Vector512<ulong> prodLL_hi = Avx512F.ShiftRightLogical(prodLL, 32);
        Vector512<ulong> prodLH_lo = Avx512F.And(prodLH, mask32);
        Vector512<ulong> prodHL_lo = Avx512F.And(prodHL, mask32);
        Vector512<ulong> termT = Avx512F.Add(prodLL_hi, Avx512F.Add(prodLH_lo, prodHL_lo));

        Vector512<ulong> shiftedT = Avx512F.ShiftLeftLogical(termT, 32);

        // lowerPartial uses vpternlog - typically a throughput win over separate and/or.
        Vector512<ulong> lowerPartial = Avx512F.TernaryLogic(prodLL, mask32, shiftedT, 0xEA);

        // higherPartial is add-heavy - so we can use an add-tree
        Vector512<ulong> hiA = Avx512F.Add(prodHH, Avx512F.ShiftRightLogical(prodLH, 32));
        Vector512<ulong> hiB = Avx512F.Add(Avx512F.ShiftRightLogical(prodHL, 32),
                                           Avx512F.ShiftRightLogical(termT, 32));
        Vector512<ulong> higherPartial = Avx512F.Add(hiA, hiB);

        // Interleave lo/hi into [lo,hi] pairs per product.
        // These unpacks are shuffle-port work; JIT likes to keep them early.

        Vector512<ulong> productLow = Avx512F.UnpackLow(lowerPartial, higherPartial);
        Vector512<ulong> productHi = Avx512F.UnpackHigh(lowerPartial, higherPartial);

        // Hoist common "views" of the product vectors now.
        // This is intentionally earlier than point-of-use - it gives OoO a longer window
        // to overlap shuffle latency with the later ALU+compare chain.
        Vector512<ulong> productLow_r2 = Avx512F.AlignRight64(productLow, productLow, 2);
        Vector512<ulong> product1High = Avx512BW.IsSupported ?
            Avx512BW.ShiftRightLogical128BitLane(productHi.AsByte(), 8).AsUInt64() :
            Avx512F.AlignRight64(productHi, productHi, 1);
        Vector512<ulong> productHi_r2 = Avx512F.AlignRight64(productHi, productHi, 2);

        // Also hoist this extract even though its used late - it is independent work.
        Vector128<ulong> extraLow = Avx512F.ExtractVector128(lowerPartial, 3);

        // Carry-emulated 128-bit adds inside each 128-bit chunk.
        // Cost centres here are:
        // - vpcmpltuq + vpmovm2q (mask materialisation tax)
        // - shuffle ops (valignq/vpslldq) feeding the carry path

        Vector512<ulong> crossAndGroup2Sum = Add128(productHi, productLow_r2);
        Vector512<ulong> crossSumHigh = Avx512BW.IsSupported ?
            Avx512BW.ShiftRightLogical128BitLane(crossAndGroup2Sum.AsByte(), 8).AsUInt64() :
            Avx512F.AlignRight64(crossAndGroup2Sum, crossAndGroup2Sum, 1);

        // Perform the group 1 cross-term addition (in 512-bit form, then extract only the final 128-bit lane).
        Vector512<ulong> crossAddMask = Avx512BW.IsSupported ?
            Avx512BW.ShiftLeftLogical128BitLane(crossAndGroup2Sum.AsByte(), 8).AsUInt64() :
            Avx512F.UnpackLow(Vector512<ulong>.Zero, crossAndGroup2Sum);
        Vector512<ulong> updatedProduct0Vec = Avx512F.Add(productLow, crossAddMask);

        // Carry-out for updatedProduct0Vec = productLow + crossAddMask (0/1 per lane, no k-masks).
        Vector512<ulong> carryMaskVec = Avx512F.ShiftRightLogical(
            Avx512F.TernaryLogic(productLow, crossAddMask, updatedProduct0Vec, 0xD4), 63);

        // Move the carry from each 128-bit chunk’s high lane into its low lane (where crossSumHigh lives).
        Vector512<ulong> carryMaskToHigh = Avx512BW.IsSupported ?
            Avx512BW.ShiftRightLogical128BitLane(carryMaskVec.AsByte(), 8).AsUInt64() :
            Avx512F.AlignRight64(carryMaskVec, carryMaskVec, 1);

        Vector512<ulong> limb2Vec = Avx512F.Add(crossSumHigh, carryMaskToHigh);

        // Carry-out for limb2Vec = crossSumHigh + carryMaskToHigh (0/1 per lane, no k-masks).
        Vector512<ulong> limb2CarryMask = Avx512F.ShiftRightLogical(
            Avx512F.TernaryLogic(carryMaskToHigh, crossSumHigh, limb2Vec, 0xD4), 63);

        // limb3 = (product1High > crossSumHigh) ? 1 : 0
        Vector512<ulong> limb3Mask = Avx512F.CompareGreaterThan(product1High, crossSumHigh);
        Vector512<ulong> limb3Vec = Avx512F.ShiftRightLogical(limb3Mask, 63);

        // propagate overflow from (crossSumHigh + carryFlag) into limb3
        limb3Vec = Avx512F.Add(limb3Vec, limb2CarryMask);

        Vector512<ulong> upperIntermediateVec = Avx512F.UnpackLow(limb2Vec, limb3Vec);

        // Combine group 2 partial results (still in 512-bit form).
        // totalGroup2 = group2Sum + product5
        Vector512<ulong> totalGroup2Vec = Add128(crossAndGroup2Sum, productHi_r2);

        // Move totalGroup2 (lane1) down into lane0, then newHalf = upperIntermediate + totalGroup2.
        Vector512<ulong> totalGroup2ToLow = Avx512F.AlignRight64(totalGroup2Vec, totalGroup2Vec, 2);
        Vector512<ulong> newHalfVec = Add128(upperIntermediateVec, totalGroup2ToLow);

        // Extract the two 128-bit results that form the final 256-bit product.
        Vector128<ulong> updatedProduct0 = Avx512F.ExtractVector128(updatedProduct0Vec, 0);
        Vector128<ulong> newHalf = Avx512F.ExtractVector128(newHalfVec, 0);

        // Process group 3 cross-terms.
        finalProdLow = Sse2.Add(finalProdLow, extraLow);
        // swap qwords via pshufd imm=0x4E
        Vector128<ulong> swapped = Sse2.Shuffle(finalProdLow.AsInt32(), 0x4E).AsUInt64();
        // sum both lanes => [a0+a1, a1+a0]
        Vector128<ulong> sum = Sse2.Add(finalProdLow, swapped);
        // keep only the high-qword in the high lane: shift-left by 8 => [0, a0+a1]
        Vector128<ulong> hiOnly = Sse2.ShiftLeftLogical128BitLane(sum.AsByte(), 8).AsUInt64();
        newHalf = Sse2.Add(newHalf, hiOnly);

        // Combine the results into the final 256-bit value.
        Vector256<ulong> finalResult = Vector256.Create(updatedProduct0, newHalf);
        Unsafe.SkipInit(out res);
        Unsafe.As<UInt256, Vector256<ulong>>(ref res) = finalResult;

        /// <summary>
        /// Adds two 512-bit vectors that conceptually contain four independent 128-bit unsigned integers.
        /// Within each 128-bit chunk, propagates an overflow (carry) from the lower 64-bit lane to the higher lane.
        /// </summary>
        /// <param name="left">The first 512-bit vector operand.</param>
        /// <param name="right">The second 512-bit vector operand.</param>
        /// <returns>
        /// The sum of <paramref name="left"/> and <paramref name="right"/>, with carries propagated within each 128-bit chunk.
        /// </returns>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        static Vector512<ulong> Add128(Vector512<ulong> left, Vector512<ulong> right)
        {
            // Compute the raw lane-wise sum; carries between 64-bit lanes within a 128-bit chunk
            // are not yet propagated and will be handled by the carry logic below.
            Vector512<ulong> sum = Avx512F.Add(left, right);

            if (Avx512BW.IsSupported)
            {
                // carryBits = (left & right) | (~sum & (left | right))  (imm8 = 0xD4)
                Vector512<ulong> carryBits = Avx512F.TernaryLogic(left, right, sum, 0xD4);
                // carryOut (0 or 1 in each 64-bit lane)
                Vector512<ulong> carry01 = Avx512F.ShiftRightLogical(carryBits, 63);
                // Promote carry from lane0->lane1, lane2->lane3, ... within each 128-bit chunk
                Vector512<ulong> promoted = Avx512BW.ShiftLeftLogical128BitLane(carry01.AsByte(), 8).AsUInt64();
                // Finalise
                return Avx512F.Add(sum, promoted);
            }
            else
            {
                Vector512<ulong> overflowMask = Avx512F.CompareLessThan(sum, left);
                // Promote carry from each 128-bit chunk’s low lane into its high lane:
                // lanes: [0, mask0, 0, mask2, 0, mask4, 0, mask6] where mask is 0 or 0xFFFF..FFFF
                Vector512<ulong> promotedCarryAllOnes = Avx512F.UnpackLow(Vector512<ulong>.Zero, overflowMask);
                // Subtracting 0xFFFF..FFFF is identical to adding 1 (mod 2^64)
                return Avx512F.Subtract(sum, promotedCarryAllOnes);
            }
        }
    }

    public void Multiply(in UInt256 a, out UInt256 res) => Multiply(this, a, out res);

    public static bool MultiplyOverflow(in UInt256 x, in UInt256 y, out UInt256 res)
    {
        Multiply256To512Bit(x, y, out res, out UInt256 high);
        return !high.IsZero;
    }

    public int BitLen =>
        u3 != 0
            ? 256 - BitOperations.LeadingZeroCount(u3)
            : u2 != 0
                ? 192 - BitOperations.LeadingZeroCount(u2)
                : u1 != 0
                    ? 128 - BitOperations.LeadingZeroCount(u1)
                    : 64 - BitOperations.LeadingZeroCount(u0);

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private void Squared(out UInt256 result)
    {
        ulong x0 = u0;
        ulong x1 = u1;
        ulong x2 = u2;

        Unsafe.SkipInit(out result);
        ref ulong pr = ref Unsafe.As<UInt256, ulong>(ref result);

        // Column 0
        ulong a0 = Multiply64(x0, x0, out pr);

        // Column 1: 2*x0*x1
        ulong a1 = 0;
        ulong a2 = 0;
        MultiplyAddCarryDouble(ref a0, ref a1, ref a2, x0, x1);
        Unsafe.Add(ref pr, 1) = a0;

        // carry into column 2 is (a2:a1) as a 128-bit value, aligned as (lo=a1, hi=a2)

        // Column 2: 2*x0*x2 + x1*x1
        a0 = a1;
        a1 = a2;
        a2 = 0;
        MultiplyAddCarryDouble(ref a0, ref a1, ref a2, x0, x2);
        MultiplyAddCarry(ref a0, ref a1, ref a2, x1, x1);
        Unsafe.Add(ref pr, 2) = a0;

        // For r3 we only need the low 64 of the incoming carry, which is a1 here.
        ulong x3 = u3;

        // Column 3: 2*x0*x3 + 2*x1*x2 (low 64 only - anything spilling past 64 goes to r4+)
        ulong s0 = (x1 * x2) << 1;
        ulong s1 = (x0 * x3) << 1;
        Unsafe.Add(ref pr, 3) = a1 + s0 + s1;
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void MultiplyAddCarryDouble(ref ulong a0, ref ulong a1, ref ulong a2, ulong x, ulong y)
    {
        // 128-bit product in (hi:lo)
        ulong hi = Multiply64(x, y, out ulong lo);

        // Double it: (hi:lo) <<= 1, producing a 129-bit value.
        ulong extra = hi >> 63;                 // bit 128 (carry out of hi when shifted)
        hi = (hi << 1) | (lo >> 63);            // new high 64
        lo <<= 1;                               // new low 64

        // a0 += lo; c0 = carry out
        ulong s0 = a0 + lo;
        ulong c0 = s0 < a0 ? 1UL : 0UL;
        a0 = s0;

        // a1 += hi + c0; c1 = carry out (0..2)
        ulong s1 = a1 + hi;
        ulong c1 = s1 < a1 ? 1UL : 0UL;
        s1 += c0;
        c1 += s1 < c0 ? 1UL : 0UL;
        a1 = s1;

        // a2 += c1 + extra (a2 stays small here)
        a2 += c1 + extra;
    }

    public static void Exp(in UInt256 b, in UInt256 e, out UInt256 result)
    {
        int bitLen = e.BitLen;
        if (bitLen == 0)
        {
            result = One;
            return;
        }
        if (b.IsUint64)
        {
            if (b.IsZero)
            {
                result = default;
                return;
            }
            if (b.IsOne)
            {
                result = One;
                return;
            }
        }

        // Seed with b so we do not need to "include" the always-set top bit via a multiply.
        UInt256 val = b;
        for (int i = bitLen - 2; i >= 0; --i)
        {
            // val = val * val
            val.Squared(out val);

            if (e.Bit(i))
            {
                MultiplyScalar(in val, in b, out val);
            }
        }

        result = val;
    }

    public void Exp(in UInt256 exp, out UInt256 res) => Exp(this, exp, out res);

    public static void Lsh(in UInt256 x, int n, out UInt256 res)
    {
        if ((n % 64) == 0)
        {
            switch (n)
            {
                case 0:
                    res = x;
                    return;
                case 64:
                    x.Lsh64(out res);
                    return;
                case 128:
                    x.Lsh128(out res);
                    return;
                case 192:
                    x.Lsh192(out res);
                    return;
                default:
                    res = Zero;
                    return;
            }
        }

        ulong z0 = 0, z1 = 0, z2 = 0;
        ulong a = 0, b = 0;
        // Big swaps first
        if (n > 192)
        {
            if (n > 256)
            {
                res = Zero;
                return;
            }

            x.Lsh192(out res);
            n -= 192;
            goto sh192;
        }
        else if (n > 128)
        {
            x.Lsh128(out res);
            n -= 128;
            goto sh128;
        }
        else if (n > 64)
        {
            x.Lsh64(out res);
            n -= 64;
            goto sh64;
        }
        else
        {
            res = x;
        }

        // remaining shifts
        a = NativeRsh(res.u0, 64 - n);
        z0 = NativeLsh(res.u0, n);

    sh64:
        b = NativeRsh(res.u1, 64 - n);
        z1 = NativeLsh(res.u1, n) | a;

    sh128:
        a = NativeRsh(res.u2, 64 - n);
        z2 = NativeLsh(res.u2, n) | b;
        ulong z3;
    sh192:
        z3 = NativeLsh(res.u3, n) | a;

        res = new UInt256(z0, z1, z2, z3);
    }

    public void LeftShift(int n, out UInt256 res)
    {
        Lsh(this, n, out res);
    }

    public bool Bit(int n)
    {
        uint bucket = ((uint)n / 64) % 4;
        int position = n % 64;
        return (Unsafe.Add(ref Unsafe.AsRef(in u0), bucket) & ((ulong)1 << position)) != 0;
    }

    public static void Rsh(in UInt256 x, int n, out UInt256 res)
    {
        // n % 64 == 0
        if ((n & 0x3f) == 0)
        {
            switch (n)
            {
                case 0:
                    res = x;
                    return;
                case 64:
                    x.Rsh64(out res);
                    return;
                case 128:
                    x.Rsh128(out res);
                    return;
                case 192:
                    x.Rsh192(out res);
                    return;
                default:
                    res = Zero;
                    return;
            }
        }

        ulong a = 0, b = 0;
        ulong z3;
        ulong z2;
        ulong z1;

        ulong z0;
        // Big swaps first
        if (n > 192)
        {
            if (n > 256)
            {
                res = Zero;
                return;
            }

            x.Rsh192(out res);
            z1 = res.u1;
            z2 = res.u2;
            z3 = res.u3;
            n -= 192;
            goto sh192;
        }
        else if (n > 128)
        {
            x.Rsh128(out res);
            z2 = res.u2;
            z3 = res.u3;
            n -= 128;
            goto sh128;
        }
        else if (n > 64)
        {
            x.Rsh64(out res);
            z3 = res.u3;
            n -= 64;
            goto sh64;
        }
        else
        {
            res = x;
        }

        // remaining shifts
        a = NativeLsh(res.u3, 64 - n);
        z3 = NativeRsh(res.u3, n);

    sh64:
        b = NativeLsh(res.u2, 64 - n);
        z2 = NativeRsh(res.u2, n) | a;

    sh128:
        a = NativeLsh(res.u1, 64 - n);
        z1 = NativeRsh(res.u1, n) | b;

    sh192:
        z0 = NativeRsh(res.u0, n) | a;

        res = new UInt256(z0, z1, z2, z3);
    }

    public void RightShift(int n, out UInt256 res) => Rsh(this, n, out res);

    internal void Lsh64(out UInt256 res)
    {
        res = new UInt256(0, u0, u1, u2);
    }

    internal void Lsh128(out UInt256 res)
    {
        res = new UInt256(0, 0, u0, u1);
    }

    internal void Lsh192(out UInt256 res)
    {
        res = new UInt256(0, 0, 0, u0);
    }

    internal void Rsh64(out UInt256 res)
    {
        res = new UInt256(u1, u2, u3);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private void Rsh128(out UInt256 res)
    {
        res = new UInt256(u2, u3);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private void Rsh192(out UInt256 res)
    {
        res = new UInt256(u3);
    }

    public static void Not(in UInt256 a, out UInt256 res)
    {
        if (Vector256.IsHardwareAccelerated)
        {
            Vector256<ulong> av = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in a));
            // Mark res as initalized so we can use it as left said of ref assignment
            Unsafe.SkipInit(out res);
            Unsafe.As<UInt256, Vector256<ulong>>(ref res) = Vector256.Xor(av, Vector256<ulong>.AllBitsSet);
        }
        else
        {
            ulong u0 = ~a.u0;
            ulong u1 = ~a.u1;
            ulong u2 = ~a.u2;
            ulong u3 = ~a.u3;
            res = new UInt256(u0, u1, u2, u3);
        }
    }

    public static void Or(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        if (Vector256.IsHardwareAccelerated)
        {
            Vector256<ulong> av = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in a));
            Vector256<ulong> bv = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in b));
            // Mark res as initalized so we can use it as left said of ref assignment
            Unsafe.SkipInit(out res);
            Unsafe.As<UInt256, Vector256<ulong>>(ref res) = Vector256.BitwiseOr(av, bv);
        }
        else
        {
            res = new UInt256(a.u0 | b.u0, a.u1 | b.u1, a.u2 | b.u2, a.u3 | b.u3);
        }
    }

    public static void And(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        if (Vector256.IsHardwareAccelerated)
        {
            Vector256<ulong> av = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in a));
            Vector256<ulong> bv = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in b));
            // Mark res as initalized so we can use it as left said of ref assignment
            Unsafe.SkipInit(out res);
            Unsafe.As<UInt256, Vector256<ulong>>(ref res) = Vector256.BitwiseAnd(av, bv);
        }
        else
        {
            res = new UInt256(a.u0 & b.u0, a.u1 & b.u1, a.u2 & b.u2, a.u3 & b.u3);
        }
    }

    public static void Xor(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        if (Vector256.IsHardwareAccelerated)
        {
            Vector256<ulong> av = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in a));
            Vector256<ulong> bv = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in b));
            // Mark res as initalized so we can use it as left said of ref assignment
            Unsafe.SkipInit(out res);
            Unsafe.As<UInt256, Vector256<ulong>>(ref res) = Vector256.Xor(av, bv);
        }
        else
        {
            res = new UInt256(a.u0 ^ b.u0, a.u1 ^ b.u1, a.u2 ^ b.u2, a.u3 ^ b.u3);
        }
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool LessThan(in UInt256 a, long b) => b >= 0 && a.u3 == 0 && a.u2 == 0 && a.u1 == 0 && a.u0 < (ulong)b;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool LessThan(long a, in UInt256 b) => a < 0 || b.u1 != 0 || b.u2 != 0 || b.u3 != 0 || (ulong)a < b.u0;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool LessThan(in UInt256 a, ulong b) => a.u3 == 0 && a.u2 == 0 && a.u1 == 0 && a.u0 < b;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool LessThan(ulong a, in UInt256 b) => b.u3 != 0 || b.u2 != 0 || b.u1 != 0 || a < b.u0;

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
    private static bool LessThanScalar(in UInt256 a, in UInt256 b)
    {
        if (a.u3 != b.u3)
            return a.u3 < b.u3;
        if (a.u2 != b.u2)
            return a.u2 < b.u2;
        if (a.u1 != b.u1)
            return a.u1 < b.u1;
        return a.u0 < b.u0;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool LessThanAvx2(in UInt256 a, in UInt256 b)
    {
        // Load the four 64-bit words into a 256-bit register.
        Vector256<ulong> vecL = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in a));
        Vector256<ulong> vecR = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in b));

        uint eqMask;
        uint ltMask;
        if (Avx512F.VL.IsSupported && Avx512DQ.IsSupported)
        {
            // Best case: AVX-512 compare produces k-mask; MoveMask uses KMOVB.
            // Avx512DQ.MoveMask is documented as KMOVB r32,k1.
            eqMask = (uint)Avx512DQ.MoveMask(Avx512F.VL.CompareEqual(vecL, vecR));     // VPCMPUQ + KMOVB
            ltMask = (uint)Avx512DQ.MoveMask(Avx512F.VL.CompareLessThan(vecL, vecR));  // VPCMPUQ + KMOVB
        }
        else
        {
            // Equality mask - AVX2 compare -> movmskpd
            eqMask = (uint)Avx.MoveMask(Avx2.CompareEqual(vecL, vecR).AsDouble());
            // AVX2 unsigned-compare trick (flip sign bit, signed compare)
            var signFlip = Vector256.Create(0x8000_0000_0000_0000UL);
            Vector256<long> sL = Avx2.Xor(vecL, signFlip).AsInt64();
            Vector256<long> sR = Avx2.Xor(vecR, signFlip).AsInt64();
            ltMask = (uint)Avx.MoveMask(Avx2.CompareGreaterThan(sR, sL).AsDouble());
        }

        uint diff = eqMask ^ 0xFu;
        if (diff == 0) return false;

        // Slightly nicer than BitOperations.Log2 here:
        // diff != 0 and diff <= 0xF => LZCNT in [28..31] => (31 - lzcnt) == (31 ^ lzcnt)
        int idx = BitOperations.LeadingZeroCount(diff) ^ 31;
        return ((ltMask >> idx) & 1u) != 0;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool LessThanVector256(in UInt256 a, in UInt256 b)
    {
        // Load the four 64-bit words into a 256-bit register.
        Vector256<ulong> vecL = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in a));
        Vector256<ulong> vecR = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in b));

        uint eqMask = Vector256.ExtractMostSignificantBits(Vector256.Equals(vecL, vecR));
        uint ltMask = Vector256.ExtractMostSignificantBits(Vector256.LessThan(vecL, vecR));

        uint diff = eqMask ^ 0xFu;
        if (diff == 0) return false;

        // Slightly nicer than BitOperations.Log2 here:
        // diff != 0 and diff <= 0xF => LZCNT in [28..31] => (31 - lzcnt) == (31 ^ lzcnt)
        int idx = BitOperations.LeadingZeroCount(diff) ^ 31;
        return ((ltMask >> idx) & 1u) != 0;
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
    private static bool LessThanBothAvx512(in UInt256 x, in UInt256 y, in UInt256 m)
    {
        Vector256<ulong> vx = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in x));
        Vector256<ulong> vy = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in y));
        Vector256<ulong> vm = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in m));

        Vector512<ulong> vxy = Vector512.Create(vx, vy);
        Vector512<ulong> vmm = Vector512.Create(vm, vm); // can be improved to vbroadcasti64x4 - see below

        uint eq8 = (uint)Avx512DQ.MoveMask(Avx512F.CompareEqual(vxy, vmm)) & 0xFFu;
        uint lt8 = (uint)Avx512DQ.MoveMask(Avx512F.CompareLessThan(vxy, vmm)) & 0xFFu;

        // d has 1s where lanes differ, in both nibbles
        uint d = (eq8 ^ 0xFFu);

        // saturate within each nibble (no cross-nibble bleed)
        d |= (d >> 1) & 0x77u;
        d |= (d >> 2) & 0x33u;

        // isolate the top mismatch bit in each nibble
        uint msb = d & ~((d >> 1) & 0x77u);

        // pick lt at that mismatch bit (still per nibble)
        uint chosen = lt8 & msb;

        // low nibble -> x, high nibble -> y
        return ((chosen & 0x0Fu) != 0) & ((chosen & 0xF0u) != 0);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool LessThanBothAvx2(in UInt256 x, in UInt256 y, in UInt256 m)
    {
        Vector256<ulong> vecM = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in m));

        var signFlip = Vector256.Create(0x8000_0000_0000_0000UL);
        var low32Mask = Vector256.Create(0x0000_0000_FFFF_FFFFUL);

        Vector256<long> sM = Avx2.Xor(vecM, signFlip).AsInt64();

        Vector256<ulong> vecX2 = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in x));
        Vector256<ulong> vecY2 = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in y));

        // All compares first (lets the core overlap work before any movemask/LZCNT).
        Vector256<ulong> eqXv = Avx2.CompareEqual(vecX2, vecM);
        Vector256<ulong> eqYv = Avx2.CompareEqual(vecY2, vecM);

        Vector256<long> sX = Avx2.Xor(vecX2, signFlip).AsInt64();
        Vector256<long> sY = Avx2.Xor(vecY2, signFlip).AsInt64();

        Vector256<ulong> ltXv = Avx2.CompareGreaterThan(sM, sX).AsUInt64();
        Vector256<ulong> ltYv = Avx2.CompareGreaterThan(sM, sY).AsUInt64();

        // Pack eq(low dword) + lt(high dword) so one movmskps yields both.
        Vector256<ulong> packedX = Avx2.Or(Avx2.And(eqXv, low32Mask), Avx2.AndNot(low32Mask, ltXv));
        Vector256<ulong> packedY = Avx2.Or(Avx2.And(eqYv, low32Mask), Avx2.AndNot(low32Mask, ltYv));

        uint maskX = (uint)Avx.MoveMask(packedX.AsSingle());
        uint maskY = (uint)Avx.MoveMask(packedY.AsSingle());

        return LessThanFromPackedMask8(maskX) & LessThanFromPackedMask8(maskY);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool LessThanBothFromEqLt8(uint eq8, uint lt8)
    {
        // eq8/lt8 are 0..255 (low 8 bits used)
        uint d = (eq8 ^ 0xFFu);           // mismatch bits (1 where not equal), per nibble

        // saturate within each nibble (prevent bit4 spilling into bit3 etc)
        d |= (d >> 1) & 0x77u;
        d |= (d >> 2) & 0x33u;

        // isolate most-significant mismatch bit in each nibble
        uint msb = d & ~((d >> 1) & 0x77u);

        // pick lt bit at that msb position for each nibble
        uint chosen = lt8 & msb;

        // low nibble -> x decision, high nibble -> y decision
        return ((chosen & 0x0Fu) != 0) & ((chosen & 0xF0u) != 0);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool LessThanFromPackedMask8(uint mask8)
    {
        // even bits are eq, odd bits are lt
        uint mismatchEven = (~mask8) & 0x55u;
        if (mismatchEven == 0) return false; // all words equal => not less

        int pos = BitOperations.LeadingZeroCount(mismatchEven) ^ 31; // highest mismatching even bit
        return ((mask8 >> (pos + 1)) & 1u) != 0; // corresponding lt bit
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool LessThanBothVector256(in UInt256 x, in UInt256 y, in UInt256 m)
    {
        Vector256<ulong> vecM = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in m));

        // x < m
        Vector256<ulong> vecX = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in x));
        uint eqMaskX = Vector256.ExtractMostSignificantBits(Vector256.Equals(vecX, vecM));
        uint ltMaskX = Vector256.ExtractMostSignificantBits(Vector256.LessThan(vecX, vecM));
        if (!LessThanBothFromEqLt8(eqMaskX, ltMaskX))
            return false;

        // y < m
        Vector256<ulong> vecY = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in y));
        uint eqMaskY = Vector256.ExtractMostSignificantBits(Vector256.Equals(vecY, vecM));
        uint ltMaskY = Vector256.ExtractMostSignificantBits(Vector256.LessThan(vecY, vecM));
        return LessThanBothFromEqLt8(eqMaskY, ltMaskY);
    }

    public override string ToString() => ((BigInteger)this).ToString();

    public int CompareTo(object? obj) => obj is not UInt256 int256 ? throw new InvalidOperationException() : CompareTo(int256);

    public string ToString(string format)
    {
        return ((BigInteger)this).ToString(format);
    }

    public bool IsUint64 => (u1 | u2 | u3) == 0;

    public bool Equals(int other)
    {
        return other >= 0 && Equals((uint)other);
    }

    public bool Equals(uint other)
    {
        if (Vector256.IsHardwareAccelerated)
        {
            Vector256<uint> v = Unsafe.As<ulong, Vector256<uint>>(ref Unsafe.AsRef(in u0));
            return v == Vector256.CreateScalar(other);
        }
        else
        {
            return u0 == other && IsUint64;
        }
    }

    public bool Equals(long other) => other >= 0 && Equals((ulong)other);

    public bool Equals(ulong other)
    {
        if (Vector256.IsHardwareAccelerated)
        {
            Vector256<ulong> v = Unsafe.As<ulong, Vector256<ulong>>(ref Unsafe.AsRef(in u0));
            return v == Vector256.CreateScalar(other);
        }
        else
        {
            return u0 == other && IsUint64;
        }
    }

    [OverloadResolutionPriority(1)]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public bool Equals(in UInt256 other)
    {
        Vector256<ulong> v1 = Unsafe.As<ulong, Vector256<ulong>>(ref Unsafe.AsRef(in u0));
        Vector256<ulong> v2 = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in other));
        return v1 == v2;
    }

    public bool Equals(UInt256 other)
    {
        Vector256<ulong> v1 = Unsafe.As<ulong, Vector256<ulong>>(ref Unsafe.AsRef(in u0));
        Vector256<ulong> v2 = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in other));
        return v1 == v2;
    }

    public int CompareTo(UInt256 b) => CompareTo(in b);

    [OverloadResolutionPriority(1)]
    public int CompareTo(in UInt256 b) => this < b ? -1 : Equals(b) ? 0 : 1;

    public override bool Equals(object? obj) => obj is UInt256 other && Equals(other);

    [SkipLocalsInit]
    public override int GetHashCode()
    {
        // Very fast hardware accelerated non-cryptographic hash function

        // Start with instance random, length and first ulong as seed
        uint hash = BitOperations.Crc32C(s_instanceRandom, u0);

        // Crc32C is 3 cycle latency, 1 cycle throughput
        // So we use same initial 3 times to not create a dependency chain
        uint hash0 = BitOperations.Crc32C(hash, u1);
        uint hash1 = BitOperations.Crc32C(hash, u2);
        uint hash2 = BitOperations.Crc32C(hash, u3);
        // Combine the 3 hashes; performing the shift on first crc to calculate
        return (int)BitOperations.Crc32C(hash1, ((ulong)hash0 << (sizeof(uint) * 8)) | hash2);
    }

    public ulong this[int index] => index switch
    {
        0 => u0,
        1 => u1,
        2 => u2,
        3 => u3,
        _ => ThrowIndexOutOfRangeException(),
    };

    public static UInt256 Max(in UInt256 a, in UInt256 b) => LessThan(in b, in a) ? a : b;

    public static UInt256 Min(in UInt256 a, in UInt256 b) => LessThan(in b, in a) ? b : a;

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private unsafe static ulong Multiply64(ulong a, ulong b, out ulong low)
    {
        if (Bmi2.X64.IsSupported)
        {
            // Two multiplies ends up being faster as it doesn't force spill to stack.
            ulong lowLocal;
            ulong high = Bmi2.X64.MultiplyNoFlags(a, b, &lowLocal);
            low = lowLocal;
            return high;
        }
        else if (ArmBase.Arm64.IsSupported)
        {
            low = a * b;
            return ArmBase.Arm64.MultiplyHigh(a, b);
        }
        else
        {
            return Math.BigMul(a, b, out low);
        }
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong Sub(ulong x, ulong y, ref ulong borrow)
    {
        ulong t = x - y;
        ulong b1 = (x < y) ? 1UL : 0UL;
        ulong t2 = t - borrow;
        ulong b2 = (t < borrow) ? 1UL : 0UL;
        borrow = b1 | b2;
        return t2;
    }

    [DoesNotReturn, StackTraceHidden]
    private static void ThrowDivideByZeroException() => throw new DivideByZeroException();

    [DoesNotReturn, StackTraceHidden]
    private static void ThrowOverflowException(string message) => throw new OverflowException(message);

    [DoesNotReturn, StackTraceHidden]
    private static void ThrowNotSupportedException() => throw new NotSupportedException();

    [DoesNotReturn, StackTraceHidden]
    private static ulong ThrowIndexOutOfRangeException() => throw new IndexOutOfRangeException();
}
