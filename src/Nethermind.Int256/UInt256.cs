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
using Arm = System.Runtime.Intrinsics.Arm;
using x64 = System.Runtime.Intrinsics.X86;

[assembly: InternalsVisibleTo("Nethermind.Int256.Tests")]
[assembly: InternalsVisibleTo("Nethermind.Int256.Benchmark")]

namespace Nethermind.Int256;

[StructLayout(LayoutKind.Explicit)]
public readonly partial struct UInt256 : IEquatable<UInt256>, IComparable, IComparable<UInt256>, IInteger<UInt256>, IConvertible
{
    public const int Len = 4;

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
        if (Avx2.IsSupported)
        {
            Vector256<ulong> av = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in a));
            Vector256<ulong> bv = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in b));

            Vector256<ulong> result = av + bv;
            // All bits set in lanes that carried out (carry out of each 64-bit limb).
            Vector256<ulong> carryMask;
            Vector256<ulong> carryIn;
            if (Avx512F.VL.IsSupported)
            {
                // Sign bit of (a & b) | (~result & (a | b)) is the carry; one ternary-logic op
                carryMask = Vector256.ShiftRightArithmetic(Avx512F.VL.TernaryLogic(av, bv, result, 0xD4).AsInt64(), 63).AsUInt64();
                carryIn = Avx512F.VL.AlignRight64(carryMask, Vector256<ulong>.Zero, 3);
            }
            else
            {
                carryMask = Vector256.LessThan(result, av);
                carryIn = Avx2.Blend(Avx2.Permute4x64(carryMask, 0b10_01_00_00).AsUInt32(), Vector256<uint>.Zero, 0b0000_0011).AsUInt64();
            }

            // res may alias a or b, so the cascade path below must only use registers already loaded.
            // Storing ahead of the branch measured 25% faster on AVX2-only parts for SubtractImpl.
            Unsafe.SkipInit(out res);
            Unsafe.As<UInt256, Vector256<ulong>>(ref res) = result - carryIn;

            // A full limb that receives a carry must pass it on; rare, so it resolves through the lookup
            Vector256<ulong> fullLanes = Vector256.Equals(result, Vector256<ulong>.AllBitsSet);
            if (!Avx.TestZ(fullLanes, carryIn))
            {
                uint carry = (uint)Avx.MoveMask(carryMask.AsDouble());
                uint cascade = (uint)Avx.MoveMask(fullLanes.AsDouble());
                // Move carry to next bit and add cascade; carries ripple through consecutive full limbs
                carry = cascade + 2 * carry;
                // Keep only the cascades a carry reached
                cascade ^= carry;
                cascade &= 0x0f;

                Vector256<ulong> cascadedCarries = Unsafe.Add(ref Unsafe.As<byte, Vector256<ulong>>(ref MemoryMarshal.GetReference(BroadcastLookup)), (nuint)cascade);
                Unsafe.As<UInt256, Vector256<ulong>>(ref res) = result + cascadedCarries;
                return (carry & 0b1_0000) != 0;
            }

            return (Avx.MoveMask(carryMask.AsDouble()) & 0b1000) != 0;
        }

        return AddScalar(in a, in b, out res);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool AddScalar(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        ulong b0 = b.u0;
        if ((b.u1 | b.u2 | b.u3) == 0)
        {
            return AddScalarUInt64(in a, b0, out res);
        }

        // Addition commutes and the EVM puts the small operand on either side of the stack
        ulong a0 = a.u0;
        if ((a.u1 | a.u2 | a.u3) == 0)
        {
            return AddScalarUInt64(in b, a0, out res);
        }

        if (AdvSimd.IsSupported || Sse42.IsSupported)
        {
            return AddVector128(in a, in b, out res);
        }

        // Loads stay next to their use: the one-limb paths above share this method's prolog
        ulong carry = 0;
        AddWithCarry(a0, b0, ref carry, out ulong r0);
        AddWithCarry(a.u1, b.u1, ref carry, out ulong r1);
        AddWithCarry(a.u2, b.u2, ref carry, out ulong r2);
        AddWithCarry(a.u3, b.u3, ref carry, out ulong r3);
        StoreLimbs(out res, r0, r1, r2, r3);
        return carry != 0;
    }

    // Same speculation as the 256-bit path on two 128-bit halves; 16-byte stores forward to the NEON readers
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool AddVector128(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        ref Vector128<ulong> aRef = ref Unsafe.As<UInt256, Vector128<ulong>>(ref Unsafe.AsRef(in a));
        ref Vector128<ulong> bRef = ref Unsafe.As<UInt256, Vector128<ulong>>(ref Unsafe.AsRef(in b));
        Vector128<ulong> aLo = aRef;
        Vector128<ulong> aHi = Unsafe.Add(ref aRef, 1);
        Vector128<ulong> bLo = bRef;
        Vector128<ulong> bHi = Unsafe.Add(ref bRef, 1);

        Vector128<ulong> resultLo = aLo + bLo;
        Vector128<ulong> resultHi = aHi + bHi;
        Vector128<ulong> carryLo = Vector128.LessThan(resultLo, aLo);
        Vector128<ulong> carryHi = Vector128.LessThan(resultHi, aHi);

        // Lane i receives the carry of lane i-1: [0, lo0] and [lo1, hi0]
        Vector128<ulong> carryInLo;
        Vector128<ulong> carryInHi;
        if (AdvSimd.IsSupported)
        {
            // ext takes its low lanes from the first operand: (second:first) >> 64 bits
            carryInLo = AdvSimd.ExtractVector128(Vector128<ulong>.Zero, carryLo, 1);
            carryInHi = AdvSimd.ExtractVector128(carryLo, carryHi, 1);
        }
        else
        {
            carryInLo = Sse2.ShiftLeftLogical128BitLane(carryLo, 8);
            carryInHi = Ssse3.AlignRight(carryHi.AsByte(), carryLo.AsByte(), 8).AsUInt64();
        }

        // A full limb that receives a carry wraps to zero and must pass it on; testing the sum keeps the
        // all-ones constant out of the register set. The fallback stays inline and call-free: with a call here
        // the JIT parks the vector values in callee-saved registers and the shared prolog pays for it
        Vector128<ulong> sumLo = resultLo - carryInLo;
        Vector128<ulong> sumHi = resultHi - carryInHi;
        Vector128<ulong> propagate = (Vector128.Equals(sumLo, Vector128<ulong>.Zero) & carryInLo)
                                   | (Vector128.Equals(sumHi, Vector128<ulong>.Zero) & carryInHi);
        if (!Vector128.EqualsAll(propagate, Vector128<ulong>.Zero))
        {
            // Nothing has been stored yet, so a and b are intact even when res aliases one of them
            ulong carry = 0;
            AddWithCarry(a.u0, b.u0, ref carry, out ulong r0);
            AddWithCarry(a.u1, b.u1, ref carry, out ulong r1);
            AddWithCarry(a.u2, b.u2, ref carry, out ulong r2);
            AddWithCarry(a.u3, b.u3, ref carry, out ulong r3);
            StoreLimbs(out res, r0, r1, r2, r3);
            return carry != 0;
        }

        Unsafe.SkipInit(out res);
        ref Vector128<ulong> resRef = ref Unsafe.As<UInt256, Vector128<ulong>>(ref res);
        resRef = sumLo;
        Unsafe.Add(ref resRef, 1) = sumHi;
        return carryHi.GetElement(1) != 0;
    }

    // One operand fits in one limb: a carry can only ripple upward through full limbs of the other
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool AddScalarUInt64(in UInt256 a, ulong b0, out UInt256 res)
    {
        ulong a0 = a.u0, a1 = a.u1, a2 = a.u2, a3 = a.u3;
        ulong r0 = a0 + b0;
        if (r0 >= a0)
        {
            StoreLimbs(out res, r0, a1, a2, a3);
            return false;
        }
        if (++a1 != 0)
        {
            StoreLimbs(out res, r0, a1, a2, a3);
            return false;
        }
        if (++a2 != 0)
        {
            StoreLimbs(out res, r0, 0, a2, a3);
            return false;
        }
        if (++a3 != 0)
        {
            StoreLimbs(out res, r0, 0, 0, a3);
            return false;
        }

        StoreLimbs(out res, r0, 0, 0, 0);
        return true;
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

    // Subtract sets res to the difference a-b
    public static void Subtract(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        SubtractImpl(in a, in b, out res);
    }

    // Subtract sets res to the difference a-b and returns true if the operation underflowed
    private static bool SubtractImpl(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        if (Avx2.IsSupported)
        {
            Vector256<ulong> av = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in a));
            Vector256<ulong> bv = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in b));

            Vector256<ulong> result = av - bv;
            // All bits set in lanes where a < b, and in lanes whose lower neighbour borrowed
            Vector256<ulong> borrowMask;
            Vector256<ulong> borrowIn;
            if (Avx512F.VL.IsSupported)
            {
                // Sign bit of (~a & b) | (~(a ^ b) & result) is the borrow; one ternary-logic op
                borrowMask = Vector256.ShiftRightArithmetic(Avx512F.VL.TernaryLogic(av, bv, result, 0x8E).AsInt64(), 63).AsUInt64();
                borrowIn = Avx512F.VL.AlignRight64(borrowMask, Vector256<ulong>.Zero, 3);
            }
            else
            {
                borrowMask = Vector256.GreaterThan(result, av);
                borrowIn = Avx2.Blend(Avx2.Permute4x64(borrowMask, 0b10_01_00_00).AsUInt32(), Vector256<uint>.Zero, 0b0000_0011).AsUInt64();
            }

            // res may alias a or b, so the cascade path below must only use registers already loaded.
            // Storing ahead of the branch measured 25% faster on AVX2-only parts.
            Unsafe.SkipInit(out res);
            Unsafe.As<UInt256, Vector256<ulong>>(ref res) = result + borrowIn;

            // A zero limb that receives a borrow must pass it on; rare, so it resolves through the lookup
            Vector256<ulong> zeroLanes = Vector256.Equals(result, Vector256<ulong>.Zero);
            if (!Avx.TestZ(zeroLanes, borrowIn))
            {
                uint borrow = (uint)Avx.MoveMask(borrowMask.AsDouble());
                uint cascade = (uint)Avx.MoveMask(zeroLanes.AsDouble());
                // Move borrow to next bit and add cascade; carries ripple through consecutive zero limbs
                borrow = cascade + 2 * borrow;
                // Keep only the cascades a borrow reached
                cascade ^= borrow;
                cascade &= 0x0f;

                Vector256<ulong> cascadedBorrows = Unsafe.Add(ref Unsafe.As<byte, Vector256<ulong>>(ref MemoryMarshal.GetReference(BroadcastLookup)), (nuint)cascade);
                Unsafe.As<UInt256, Vector256<ulong>>(ref res) = result - cascadedBorrows;
                return (borrow & 0b1_0000) != 0;
            }

            return (Avx.MoveMask(borrowMask.AsDouble()) & 0b1000) != 0;
        }

        return SubtractScalar(in a, in b, out res);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool SubtractScalar(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        ulong b0 = b.u0;
        if ((b.u1 | b.u2 | b.u3) == 0)
        {
            return SubtractScalarUInt64(in a, b0, out res);
        }

        if (AdvSimd.IsSupported || Sse42.IsSupported)
        {
            return SubtractVector128(in a, in b, out res);
        }

        // Loads stay next to their use: the one-limb path above shares this method's prolog
        ulong borrow = 0;
        SubtractWithBorrow(a.u0, b0, ref borrow, out ulong r0);
        SubtractWithBorrow(a.u1, b.u1, ref borrow, out ulong r1);
        SubtractWithBorrow(a.u2, b.u2, ref borrow, out ulong r2);
        SubtractWithBorrow(a.u3, b.u3, ref borrow, out ulong r3);
        StoreLimbs(out res, r0, r1, r2, r3);
        return borrow != 0;
    }

    // Same speculation as the 256-bit path on two 128-bit halves; 16-byte stores forward to the NEON readers
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool SubtractVector128(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        ref Vector128<ulong> aRef = ref Unsafe.As<UInt256, Vector128<ulong>>(ref Unsafe.AsRef(in a));
        ref Vector128<ulong> bRef = ref Unsafe.As<UInt256, Vector128<ulong>>(ref Unsafe.AsRef(in b));
        Vector128<ulong> aLo = aRef;
        Vector128<ulong> aHi = Unsafe.Add(ref aRef, 1);
        Vector128<ulong> bLo = bRef;
        Vector128<ulong> bHi = Unsafe.Add(ref bRef, 1);

        Vector128<ulong> resultLo = aLo - bLo;
        Vector128<ulong> resultHi = aHi - bHi;
        Vector128<ulong> borrowLo = Vector128.LessThan(aLo, bLo);
        Vector128<ulong> borrowHi = Vector128.LessThan(aHi, bHi);

        // Lane i receives the borrow of lane i-1: [0, lo0] and [lo1, hi0]
        Vector128<ulong> borrowInLo;
        Vector128<ulong> borrowInHi;
        if (AdvSimd.IsSupported)
        {
            // ext takes its low lanes from the first operand: (second:first) >> 64 bits
            borrowInLo = AdvSimd.ExtractVector128(Vector128<ulong>.Zero, borrowLo, 1);
            borrowInHi = AdvSimd.ExtractVector128(borrowLo, borrowHi, 1);
        }
        else
        {
            borrowInLo = Sse2.ShiftLeftLogical128BitLane(borrowLo, 8);
            borrowInHi = Ssse3.AlignRight(borrowHi.AsByte(), borrowLo.AsByte(), 8).AsUInt64();
        }

        // A zero limb that receives a borrow must pass it on. The fallback stays inline and call-free: with a
        // call here the JIT parks the vector values in callee-saved registers and the shared prolog pays for it
        Vector128<ulong> propagate = (Vector128.Equals(resultLo, Vector128<ulong>.Zero) & borrowInLo)
                                   | (Vector128.Equals(resultHi, Vector128<ulong>.Zero) & borrowInHi);
        if (!Vector128.EqualsAll(propagate, Vector128<ulong>.Zero))
        {
            // Nothing has been stored yet, so a and b are intact even when res aliases one of them
            ulong borrow = 0;
            SubtractWithBorrow(a.u0, b.u0, ref borrow, out ulong r0);
            SubtractWithBorrow(a.u1, b.u1, ref borrow, out ulong r1);
            SubtractWithBorrow(a.u2, b.u2, ref borrow, out ulong r2);
            SubtractWithBorrow(a.u3, b.u3, ref borrow, out ulong r3);
            StoreLimbs(out res, r0, r1, r2, r3);
            return borrow != 0;
        }

        Unsafe.SkipInit(out res);
        ref Vector128<ulong> resRef = ref Unsafe.As<UInt256, Vector128<ulong>>(ref res);
        resRef = resultLo + borrowInLo;
        Unsafe.Add(ref resRef, 1) = resultHi + borrowInHi;
        return borrowHi.GetElement(1) != 0;
    }

    // Right operand fits in one limb: a borrow can only ripple upward through zero limbs
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool SubtractScalarUInt64(in UInt256 a, ulong b0, out UInt256 res)
    {
        ulong a0 = a.u0, a1 = a.u1, a2 = a.u2, a3 = a.u3;
        ulong r0 = a0 - b0;
        if (a0 >= b0)
        {
            StoreLimbs(out res, r0, a1, a2, a3);
            return false;
        }
        if (a1 != 0)
        {
            StoreLimbs(out res, r0, a1 - 1, a2, a3);
            return false;
        }
        if (a2 != 0)
        {
            StoreLimbs(out res, r0, ulong.MaxValue, a2 - 1, a3);
            return false;
        }
        if (a3 != 0)
        {
            StoreLimbs(out res, r0, ulong.MaxValue, ulong.MaxValue, a3 - 1);
            return false;
        }

        StoreLimbs(out res, r0, ulong.MaxValue, ulong.MaxValue, ulong.MaxValue);
        return true;
    }

    // Inputs are read into locals before this runs, so res may alias either operand
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void StoreLimbs(out UInt256 res, ulong r0, ulong r1, ulong r2, ulong r3)
    {
        Unsafe.SkipInit(out res);
        Unsafe.AsRef(in res.u0) = r0;
        Unsafe.AsRef(in res.u1) = r1;
        Unsafe.AsRef(in res.u2) = r2;
        Unsafe.AsRef(in res.u3) = r3;
    }

    // Borrow out is (a < b) | ((a == b) & borrowIn); both compares are off the carry chain
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void SubtractWithBorrow(ulong a, ulong b, ref ulong borrow, out ulong res)
    {
        res = a - b - borrow;
        borrow = (a < b ? 1UL : 0UL) | (borrow & (a == b ? 1UL : 0UL));
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
        ulong x3 = x.u3;
        ulong y3 = y.u3;

        if (Bmi2.X64.IsSupported && (x2 | x3 | y2 | y3) == 0)
        {
            if (x1 == 0)
            {
                MultiplyByUInt64Width2(in y, x0, out res);
                return;
            }
            if (y1 == 0)
            {
                MultiplyByUInt64Width2(in x, y0, out res);
                return;
            }

            MultiplyWidth2(in x, in y, out res);
            return;
        }
        if (!ArmBase.Arm64.IsSupported && (x2 | x3 | y2 | y3) == 0)
        {
            if (x1 == 0)
            {
                MultiplyByUInt64Width2(in y, x0, out res);
                return;
            }
            if (y1 == 0)
            {
                MultiplyByUInt64Width2(in x, y0, out res);
                return;
            }

            MultiplyWidth2(in x, in y, out res);
            return;
        }

        if ((y1 | y2 | y3) == 0)
        {
            MultiplyByUInt64(in x, y0, out res);
            return;
        }
        if ((x1 | x2 | x3) == 0)
        {
            MultiplyByUInt64(in y, x0, out res);
            return;
        }

        ulong h00 = Multiply64(x0, y0, out ulong r0);
        ulong h01 = Multiply64(x0, y1, out ulong l01);
        ulong h10 = Multiply64(x1, y0, out ulong l10);
        ulong h02 = Multiply64(x0, y2, out ulong l02);
        ulong h11 = Multiply64(x1, y1, out ulong l11);
        ulong h20 = Multiply64(x2, y0, out ulong l20);

        ulong carry = 0;
        ulong r1 = AddAndCountCarry(h00, l01, ref carry);
        r1 = AddAndCountCarry(r1, l10, ref carry);

        ulong r2 = carry;
        carry = 0;
        r2 = AddAndCountCarry(r2, h01, ref carry);
        r2 = AddAndCountCarry(r2, h10, ref carry);
        r2 = AddAndCountCarry(r2, l02, ref carry);
        r2 = AddAndCountCarry(r2, l11, ref carry);
        r2 = AddAndCountCarry(r2, l20, ref carry);

        ulong r3 = carry + h02 + h11 + h20
            + x0 * y3 + x1 * y2 + x2 * y1 + x3 * y0;
        Unsafe.SkipInit(out res);
        ref ulong pr = ref Unsafe.As<UInt256, ulong>(ref res);
        pr = r0;
        Unsafe.Add(ref pr, 1) = r1;
        Unsafe.Add(ref pr, 2) = r2;
        Unsafe.Add(ref pr, 3) = r3;
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void MultiplyByUInt64Width2(in UInt256 x, ulong y, out UInt256 res)
    {
        ulong carry = Multiply64(x.u0, y, out ulong r0);
        ulong high = Multiply64(x.u1, y, out ulong low);
        ulong r1 = low + carry;
        ulong r2 = high + (r1 < low ? 1UL : 0UL);
        res = new UInt256(r0, r1, r2);
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void MultiplyWidth2(in UInt256 x, in UInt256 y, out UInt256 res)
    {
        ulong h00 = Multiply64(x.u0, y.u0, out ulong r0);
        ulong h01 = Multiply64(x.u0, y.u1, out ulong l01);
        ulong h10 = Multiply64(x.u1, y.u0, out ulong l10);
        ulong h11 = Multiply64(x.u1, y.u1, out ulong l11);

        ulong carry = 0;
        ulong r1 = AddAndCountCarry(h00, l01, ref carry);
        r1 = AddAndCountCarry(r1, l10, ref carry);

        ulong r2 = carry;
        carry = 0;
        r2 = AddAndCountCarry(r2, h01, ref carry);
        r2 = AddAndCountCarry(r2, h10, ref carry);
        r2 = AddAndCountCarry(r2, l11, ref carry);

        res = new UInt256(r0, r1, r2, h11 + carry);
    }

    private static void MultiplyByUInt64(in UInt256 x, ulong y, out UInt256 res)
    {
        ulong x0 = x.u0;
        ulong x1 = x.u1;
        ulong x2 = x.u2;
        ulong x3 = x.u3;

        ulong carry = Multiply64(x0, y, out ulong r0);
        ulong high = Multiply64(x1, y, out ulong low);
        ulong r1 = low + carry;
        carry = high + (r1 < low ? 1UL : 0UL);

        high = Multiply64(x2, y, out low);
        ulong r2 = low + carry;
        carry = high + (r2 < low ? 1UL : 0UL);

        ulong r3 = x3 * y + carry;
        Unsafe.SkipInit(out res);
        ref ulong pr = ref Unsafe.As<UInt256, ulong>(ref res);
        pr = r0;
        Unsafe.Add(ref pr, 1) = r1;
        Unsafe.Add(ref pr, 2) = r2;
        Unsafe.Add(ref pr, 3) = r3;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong AddAndCountCarry(ulong x, ulong y, ref ulong carry)
    {
        ulong sum = x + y;
        carry += sum < x ? 1UL : 0UL;
        return sum;
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

    [SkipLocalsInit]
    public static bool MultiplyOverflow(in UInt256 x, in UInt256 y, out UInt256 res)
    {
        Multiply256To512Bit(x, y, out res, out UInt256 high);
        // Scalar test: a vector IsZero load here would span the four scalar limb stores
        // the multiply just made and defeat store forwarding.
        return (high.u0 | high.u1 | high.u2 | high.u3) != 0;
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

    /// <summary>
    /// Shifts <paramref name="x"/> left by <paramref name="n"/> bits, discarding bits shifted out of bit 255.
    /// </summary>
    /// <remarks>
    /// Counts of 256 or more produce zero. Negative counts keep the historic behaviour: a negative
    /// multiple of 64 produces zero, any other negative count shifts by <c>n &amp; 63</c> with no word shift.
    /// <paramref name="res"/> may alias <paramref name="x"/>.
    /// </remarks>
    public static void Lsh(in UInt256 x, int n, out UInt256 res)
    {
        int wordShift = n >> 6;
        if ((uint)wordShift >= (uint)Len)
        {
            if (wordShift >= 0 || (n & 63) == 0)
            {
                res = default;
                return;
            }

            wordShift = 0;
        }

        int bitShift = n & 63;
        int carryShift = 63 - bitShift;
        // Read every limb up front: res is allowed to alias x.
        ulong x0 = x.u0, x1 = x.u1, x2 = x.u2, x3 = x.u3;

        // (lo >> 1) >> (63 - bitShift) equals lo >> (64 - bitShift) but also yields 0 when
        // bitShift is 0, so whole-word counts need no separate path.
        if (wordShift == 0)
        {
            SetLimbs(out res,
                x0 << bitShift,
                (x1 << bitShift) | ((x0 >> 1) >> carryShift),
                (x2 << bitShift) | ((x1 >> 1) >> carryShift),
                (x3 << bitShift) | ((x2 >> 1) >> carryShift));
        }
        else if (wordShift == 1)
        {
            SetLimbs(out res,
                0,
                x0 << bitShift,
                (x1 << bitShift) | ((x0 >> 1) >> carryShift),
                (x2 << bitShift) | ((x1 >> 1) >> carryShift));
        }
        else if (wordShift == 2)
        {
            SetLimbs(out res,
                0,
                0,
                x0 << bitShift,
                (x1 << bitShift) | ((x0 >> 1) >> carryShift));
        }
        else
        {
            SetLimbs(out res, 0, 0, 0, x0 << bitShift);
        }
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

    /// <summary>
    /// Shifts <paramref name="x"/> right by <paramref name="n"/> bits, discarding bits shifted out of bit 0.
    /// </summary>
    /// <remarks>
    /// Counts of 256 or more produce zero. Negative counts keep the historic behaviour: a negative
    /// multiple of 64 produces zero, any other negative count shifts by <c>n &amp; 63</c> with no word shift.
    /// <paramref name="res"/> may alias <paramref name="x"/>.
    /// </remarks>
    public static void Rsh(in UInt256 x, int n, out UInt256 res)
    {
        int wordShift = n >> 6;
        if ((uint)wordShift >= (uint)Len)
        {
            if (wordShift >= 0 || (n & 63) == 0)
            {
                res = default;
                return;
            }

            wordShift = 0;
        }

        int bitShift = n & 63;
        int carryShift = 63 - bitShift;
        // Read every limb up front: res is allowed to alias x.
        ulong x0 = x.u0, x1 = x.u1, x2 = x.u2, x3 = x.u3;

        // (hi << 1) << (63 - bitShift) equals hi << (64 - bitShift) but also yields 0 when
        // bitShift is 0, so whole-word counts need no separate path.
        if (wordShift == 0)
        {
            SetLimbs(out res,
                (x0 >> bitShift) | ((x1 << 1) << carryShift),
                (x1 >> bitShift) | ((x2 << 1) << carryShift),
                (x2 >> bitShift) | ((x3 << 1) << carryShift),
                x3 >> bitShift);
        }
        else if (wordShift == 1)
        {
            SetLimbs(out res,
                (x1 >> bitShift) | ((x2 << 1) << carryShift),
                (x2 >> bitShift) | ((x3 << 1) << carryShift),
                x3 >> bitShift,
                0);
        }
        else if (wordShift == 2)
        {
            SetLimbs(out res,
                (x2 >> bitShift) | ((x3 << 1) << carryShift),
                x3 >> bitShift,
                0,
                0);
        }
        else
        {
            SetLimbs(out res, x3 >> bitShift, 0, 0, 0);
        }
    }

    public void RightShift(int n, out UInt256 res) => Rsh(this, n, out res);

    /// <summary>
    /// Writes a result built from four separate limbs, in one store of the full width.
    /// </summary>
    /// <remarks>
    /// The store width has to match how callers read the value back. Most of this type reads a
    /// <see cref="UInt256"/> as a single <see cref="Vector256{T}"/> (see <c>AddOverflow</c>,
    /// <c>LessThanAvx2</c>, <c>ToBigEndian</c>), and a 32-byte load cannot be store-forwarded from
    /// four 8-byte stores - it waits on L1, costing roughly ten cycles. Assigning through
    /// <see cref="Unsafe.As{TFrom, TTo}"/> keeps this a single <c>vmovdqu</c>; going via the
    /// <see cref="UInt256"/> constructor instead lets struct promotion split it back into limb stores.
    /// Without hardware acceleration the callers read limbs too, so store limbs: the software
    /// <see cref="Vector256.Create(ulong, ulong, ulong, ulong)"/> fallback is out-of-line calls.
    /// </remarks>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void SetLimbs(out UInt256 res, ulong z0, ulong z1, ulong z2, ulong z3)
    {
        Unsafe.SkipInit(out res);
        if (Vector256.IsHardwareAccelerated)
        {
            Unsafe.As<UInt256, Vector256<ulong>>(ref res) = Vector256.Create(z0, z1, z2, z3);
        }
        else
        {
            ref ulong p = ref Unsafe.As<UInt256, ulong>(ref res);
            p = z0;
            Unsafe.Add(ref p, 1) = z1;
            Unsafe.Add(ref p, 2) = z2;
            Unsafe.Add(ref p, 3) = z3;
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
    internal static bool LessThanScalar(in UInt256 a, in UInt256 b)
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
    internal static bool LessThanAvx2(in UInt256 a, in UInt256 b)
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

    public bool Equals(long other) => other >= 0 && Equals((ulong)other);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public bool Equals(UInt256 other) => Equals(in other);

    public int CompareTo(UInt256 b) => CompareTo(in b);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    [OverloadResolutionPriority(1)]
    public int CompareTo(in UInt256 b)
    {
        if (u3 != b.u3) return u3 < b.u3 ? -1 : 1;
        if (u2 != b.u2) return u2 < b.u2 ? -1 : 1;
        if (u1 != b.u1) return u1 < b.u1 ? -1 : 1;
        return u0 == b.u0 ? 0 : u0 < b.u0 ? -1 : 1;
    }

    public override bool Equals(object? obj) => obj is UInt256 other && Equals(other);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    internal readonly int GetCrcHashCode(uint seed)
    {
        ulong hash0 = BitOperations.Crc32C(seed, u0);
        ulong hash1 = BitOperations.Crc32C(seed ^ 0x9E3779B9u, u1);
        ulong hash2 = BitOperations.Crc32C(seed ^ 0x85EBCA6Bu, u2);
        ulong hash3 = BitOperations.Crc32C(seed ^ 0xC2B2AE35u, u3);
        return FoldHash(MumFold(hash0 | (hash1 << 32), hash2 | (hash3 << 32)));
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static Vector128<byte> HashAesRound(Vector128<byte> state, Vector128<byte> roundKey)
        => x64.Aes.IsSupported
            ? x64.Aes.Encrypt(state, roundKey)
            // Keep the round key outside AESE so state and roundKey have distinct roles in the mixer.
            : Arm.Aes.MixColumns(Arm.Aes.Encrypt(state, Vector128<byte>.Zero)) ^ roundKey;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static long MumFold(ulong a, ulong b)
    {
        ulong low = Math.BigMul(a ^ 0x9E3779B97F4A7C15UL, b ^ 0xBF58476D1CE4E5B9UL, out ulong high);
        return (long)(low ^ high);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static long MumFold(Vector128<byte> mixed)
        => MumFold(mixed.AsUInt64().GetElement(0), mixed.AsUInt64().GetElement(1));

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static int FoldHash(long hash)
    {
        ulong value = (ulong)hash;
        return (int)(value ^ (value >> 32));
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
    private static ulong Multiply64(ulong a, ulong b, out ulong low)
    {
        if (Bmi2.X64.IsSupported)
        {
            // Two multiplies are faster here because the high-only overload
            // lets the JIT keep both results in registers.
            low = a * b;
            return Bmi2.X64.MultiplyNoFlags(a, b);
        }
        else if (ArmBase.Arm64.IsSupported)
        {
            low = a * b;
            return ArmBase.Arm64.MultiplyHigh(a, b);
        }
        else
        {
            // No widening multiply instruction on this target (e.g. riscv64). Spelled out rather than
            // deferred to Math.BigMul, which repeats the same ISA checks and then calls an
            // out-of-line software fallback that cannot inline into the 256-bit limb loops.
            uint al = (uint)a, ah = (uint)(a >> 32);
            uint bl = (uint)b, bh = (uint)(b >> 32);

            ulong mull = (ulong)al * bl;
            ulong t = (ulong)ah * bl + (mull >> 32);
            ulong tl = (ulong)al * bh + (uint)t;

            low = (tl << 32) | (uint)mull;
            return (ulong)ah * bh + (t >> 32) + (tl >> 32);
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
