// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
// Versioned production-shaped Add/Subtract algorithms. Runtime fixture runners never mutate these sources.
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.Arm;
using System.Runtime.Intrinsics.X86;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    /// <summary>Adds the two fixture operands modulo 2^256.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void Add(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        #if FEATURE_EXPRESSIONS
        if (Avx2.IsSupported & Avx2.IsSupported)
#else
        if (Avx2.IsSupported)
#endif
        {
#if RENAMED
            LoadSum256(in a, in b, out res, out Vector256<ulong> result, out Vector256<ulong> carryMask,
#else
            PrepareAdd(in a, in b, out res, out Vector256<ulong> result, out Vector256<ulong> carryMask,
#endif
                out Vector256<ulong> carryIn, out Vector256<ulong> fullLanes);
            // Lane 3 has already wrapped in the speculative store; its carry out is discarded.
            // Only cascades from lanes 1-2 can still change the wrapped result (unlike AddOverflow).
            if ((Avx.MoveMask((fullLanes & carryIn).AsDouble()) & 0b0110) != 0)
#if RENAMED
                RepairSum256(result, carryMask, fullLanes, out res);
#else
                FinishAdd(result, carryMask, fullLanes, out res);
#endif
            return;
        }
        AddScalar(in a, in b, out res, false);
    }

    /// <summary>Adds fixture operands and returns the overflow flag.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
#if REPORTING_FIXTURE
    private static bool AddOverflowCore(in UInt256 a, in UInt256 b, out UInt256 res)
#else
    public static bool AddOverflow(in UInt256 a, in UInt256 b, out UInt256 res)
#endif
    {
        #if FEATURE_EXPRESSIONS
        if (Avx2.IsSupported & Avx2.IsSupported)
#else
        if (Avx2.IsSupported)
#endif
        {
#if RENAMED
            LoadSum256(in a, in b, out res, out Vector256<ulong> result, out Vector256<ulong> carryMask,
#else
            PrepareAdd(in a, in b, out res, out Vector256<ulong> result, out Vector256<ulong> carryMask,
#endif
                out Vector256<ulong> carryIn, out Vector256<ulong> fullLanes);
            if (!Avx.TestZ(fullLanes, carryIn))
#if RENAMED
                return RepairSum256(result, carryMask, fullLanes, out res);
#else
                return FinishAdd(result, carryMask, fullLanes, out res);
#endif
            return (Avx.MoveMask(carryMask.AsDouble()) & 0b1000) != 0;
        }
        return AddScalar(in a, in b, out res, true);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
#if RENAMED
    private static void LoadSum256(in UInt256 a, in UInt256 b, out UInt256 res,
#else
    private static void PrepareAdd(in UInt256 a, in UInt256 b, out UInt256 res,
#endif
        out Vector256<ulong> result, out Vector256<ulong> carryMask,
        out Vector256<ulong> carryIn, out Vector256<ulong> fullLanes)
    {
        Vector256<ulong> av = Unsafe.BitCast<UInt256, Vector256<ulong>>(a);
        Vector256<ulong> bv = Unsafe.BitCast<UInt256, Vector256<ulong>>(b);

        result = av + bv;
        // All bits set in lanes that carried out (carry out of each 64-bit limb).
        #if FEATURE_EXPRESSIONS
        if (Avx512F.VL.IsSupported & Avx.IsSupported)
#else
        if (Avx512F.VL.IsSupported)
#endif
        {
            // Sign bit of (a & b) | (~result & (a | b)) is the carry; one ternary-logic op
            #if WRONG_TERNARY
carryMask = Vector256.ShiftRightArithmetic(Avx512F.VL.TernaryLogic(av, bv, result, 0x00).AsInt64(), 63).AsUInt64();
#else
carryMask = Vector256.ShiftRightArithmetic(Avx512F.VL.TernaryLogic(av, bv, result, 0xD4).AsInt64(), 63).AsUInt64();
#endif
#if WRONG_AVX_ALIGNMENT
            carryIn = Avx512F.VL.AlignRight64(carryMask, Vector256<ulong>.Zero, 2);
#else
            carryIn = Avx512F.VL.AlignRight64(carryMask, Vector256<ulong>.Zero, 3);
#endif
        }
        else
        {
            carryMask = Vector256.LessThan(result, av);
#if EQUIVALENT_MASK
            carryIn = Avx2.Permute4x64(carryMask, 0b10_01_00_00) & Vector256.Create(0UL, ulong.MaxValue, ulong.MaxValue, ulong.MaxValue);
#else
#if WRONG_BLEND
            carryIn = Avx2.Blend(Avx2.Permute4x64(carryMask, 0b10_01_00_00).AsUInt32(), Vector256<uint>.Zero, 0b0000_1111).AsUInt64();
#else
            carryIn = Avx2.Blend(Avx2.Permute4x64(carryMask, 0b10_01_00_00).AsUInt32(), Vector256<uint>.Zero, 0b0000_0011).AsUInt64();
#endif
#endif
        }

        // res may alias a or b, so the cascade path below must only use registers already loaded.
#if RENAMED
        // Storing ahead of the branch measured 25% faster on AVX2-only parts for DifferenceDispatcher.
#else
        // Storing ahead of the branch measured 25% faster on AVX2-only parts for SubtractImpl.
#endif
        Unsafe.SkipInit(out res);
        Unsafe.As<UInt256, Vector256<ulong>>(ref res) = result - carryIn;

        // A full limb that receives a carry must pass it on; rare, so it resolves through the lookup
        #if WRONG_PREDICATE
fullLanes = Vector256.Equals(result, Vector256<ulong>.Zero);
#else
#if EARLY_REREAD
fullLanes = Vector256.Equals(Unsafe.BitCast<UInt256, Vector256<ulong>>(a) + bv, Vector256<ulong>.AllBitsSet);
#else
fullLanes = Vector256.Equals(result, Vector256<ulong>.AllBitsSet);
#endif
#endif
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
#if RENAMED
    private static bool RepairSum256(Vector256<ulong> result, Vector256<ulong> carryMask,
#else
    private static bool FinishAdd(Vector256<ulong> result, Vector256<ulong> carryMask,
#endif
        Vector256<ulong> fullLanes, out UInt256 res)
    {
        Unsafe.SkipInit(out res);
        uint carry = (uint)Avx.MoveMask(carryMask.AsDouble());
        uint cascade = (uint)Avx.MoveMask(fullLanes.AsDouble());
        // Move carry to next bit and add cascade; carries ripple through consecutive full limbs
        #if EXTRACTED_HELPER
carry = AccumulateCascade(cascade, carry);
#else
carry = cascade + 2 * carry;
#endif
        // Keep only the cascades a carry reached
        cascade ^= carry;
        cascade &= 0x0f;

        #if WRONG_SCALE
Vector256<ulong> cascadedCarries = Unsafe.Add(ref Unsafe.As<byte, Vector256<ulong>>(ref MemoryMarshal.GetReference(BroadcastLookup)), (nuint)(cascade << 1));
#else
Vector256<ulong> cascadedCarries = Unsafe.Add(ref Unsafe.As<byte, Vector256<ulong>>(ref MemoryMarshal.GetReference(BroadcastLookup)), (nuint)cascade);
#endif
        Unsafe.As<UInt256, Vector256<ulong>>(ref res) = result + cascadedCarries;
        return (carry & 0b1_0000) != 0;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool AddScalar(in UInt256 a, in UInt256 b, out UInt256 res, bool detectOverflow)
    {
        #if FEATURE_EXPRESSIONS
        if (AdvSimd.IsSupported & AdvSimd.IsSupported)
#else
        if (AdvSimd.IsSupported)
#endif
        {
            ref readonly UInt256 large = ref a;
            ulong small = b.u0;
            if ((b.u1 | b.u2 | b.u3) != 0)
            {
#if RENAMED
                if ((a.u1 | a.u2 | a.u3) != 0) return PairSum128(in a, in b, out res, detectOverflow);
#else
                if ((a.u1 | a.u2 | a.u3) != 0) return AddVector128(in a, in b, out res, detectOverflow);
#endif
                large = ref b;
                small = a.u0;
            }
#if RENAMED
            return SumWord(in large, small, out res);
#else
            return AddScalarUInt64(in large, small, out res);
#endif
        }
        ulong b0 = b.u0;
        if ((b.u1 | b.u2 | b.u3) == 0)
        {
#if RENAMED
            return SumWord(in a, b0, out res);
#else
            return AddScalarUInt64(in a, b0, out res);
#endif
        }

        // Addition commutes and the EVM puts the small operand on either side of the stack
        ulong a0 = a.u0;
        if ((a.u1 | a.u2 | a.u3) == 0)
        {
#if RENAMED
            return SumWord(in b, a0, out res);
#else
            return AddScalarUInt64(in b, a0, out res);
#endif
        }

        if (Sse42.IsSupported)
        {
#if RENAMED
            return PairSum128(in a, in b, out res, detectOverflow);
#else
            return AddVector128(in a, in b, out res, detectOverflow);
#endif
        }

        // Loads stay next to their use: the one-limb paths above share this method's prolog
        ulong carry = 0;
#if INLINE_CARRY
        ulong tempr0 = a0 + b0;
        ulong r0 = tempr0 + carry;
        carry = (tempr0 < a0 ? 1UL : 0UL) + (r0 < tempr0 ? 1UL : 0UL);
#else
        AddWithCarry(a0, b0, ref carry, out ulong r0);
#endif
#if INLINE_CARRY
        ulong tempr1 = a.u1 + b.u1;
        ulong r1 = tempr1 + carry;
        carry = (tempr1 < a.u1 ? 1UL : 0UL) + (r1 < tempr1 ? 1UL : 0UL);
#else
        AddWithCarry(a.u1, b.u1, ref carry, out ulong r1);
#endif
#if INLINE_CARRY
        ulong tempr2 = a.u2 + b.u2;
        ulong r2 = tempr2 + carry;
        carry = (tempr2 < a.u2 ? 1UL : 0UL) + (r2 < tempr2 ? 1UL : 0UL);
#else
        AddWithCarry(a.u2, b.u2, ref carry, out ulong r2);
#endif
#if INLINE_CARRY
        ulong tempr3 = a.u3 + b.u3;
        ulong r3 = tempr3 + carry;
        carry = (tempr3 < a.u3 ? 1UL : 0UL) + (r3 < tempr3 ? 1UL : 0UL);
#else
        AddWithCarry(a.u3, b.u3, ref carry, out ulong r3);
#endif
#if REVERSED_STORE
        StoreLimbs(out res, r3, r2, r1, r0);
#else
        StoreLimbs(out res, r0, r1, r2, r3);
#endif
        return carry != 0;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
#if RENAMED
    private static bool PairSum128(in UInt256 a, in UInt256 b, out UInt256 res, bool detectOverflow)
#else
    private static bool AddVector128(in UInt256 a, in UInt256 b, out UInt256 res, bool detectOverflow)
#endif
    {
        ref Vector128<ulong> aRef = ref Unsafe.As<UInt256, Vector128<ulong>>(ref Unsafe.AsRef(in a));
        ref Vector128<ulong> bRef = ref Unsafe.As<UInt256, Vector128<ulong>>(ref Unsafe.AsRef(in b));
#if LANE_LOCALS
        Vector128<ulong> bHi = Unsafe.Add(ref bRef, 1);
        Vector128<ulong> aLo = aRef;
        Vector128<ulong> bLo = bRef;
        Vector128<ulong> aHi = Unsafe.Add(ref aRef, 1);
#else
        Vector128<ulong> aLo = aRef;
        Vector128<ulong> aHi = Unsafe.Add(ref aRef, 1);
        Vector128<ulong> bLo = bRef;
        Vector128<ulong> bHi = Unsafe.Add(ref bRef, 1);
#endif

        Vector128<ulong> resultLo = aLo + bLo;
        Vector128<ulong> resultHi = aHi + bHi;
        Vector128<ulong> carryLo = Vector128.LessThan(resultLo, aLo);
        Vector128<ulong> carryHi = Vector128.LessThan(resultHi, aHi);

        // Lane i receives the carry of lane i-1: [0, lo0] and [lo1, hi0]
        Vector128<ulong> carryInLo;
        Vector128<ulong> carryInHi;
        #if FEATURE_EXPRESSIONS
        if (AdvSimd.IsSupported & AdvSimd.IsSupported)
#else
        if (AdvSimd.IsSupported)
#endif
        {
            // ext takes its low lanes from the first operand: (second:first) >> 64 bits
            carryInLo = AdvSimd.ExtractVector128(Vector128<ulong>.Zero, carryLo, 1);
            #if WRONG_ALIGNMENT
carryInHi = AdvSimd.ExtractVector128(carryLo, carryHi, 0);
#else
#if EXTRACTED_HELPER
carryInHi = ExtractPair(carryLo, carryHi);
#else
carryInHi = AdvSimd.ExtractVector128(carryLo, carryHi, 1);
#endif
#endif
        }
        else
        {
            carryInLo = Sse2.ShiftLeftLogical128BitLane(carryLo, 8);
            #if WRONG_ALIGNMENT
carryInHi = Ssse3.AlignRight(carryHi.AsByte(), carryLo.AsByte(), 0).AsUInt64();
#else
carryInHi = Ssse3.AlignRight(carryHi.AsByte(), carryLo.AsByte(), 8).AsUInt64();
#endif
        }

        // A full limb that receives a carry wraps to zero and must pass it on; testing the sum keeps the
        // all-ones constant out of the register set. The fallback stays inline and call-free: with a call here
        // the JIT parks the vector values in callee-saved registers and the shared prolog pays for it
        Vector128<ulong> sumLo = resultLo - carryInLo;
        Vector128<ulong> sumHi = resultHi - carryInHi;
        Unsafe.SkipInit(out res);
        // ARM repairs carries using the loaded vectors, so early stores are safe even with aliased inputs.
        #if FEATURE_EXPRESSIONS
        if (AdvSimd.IsSupported & AdvSimd.IsSupported)
#else
        if (AdvSimd.IsSupported)
#endif
        {
            ref Vector128<ulong> earlyResult = ref Unsafe.As<UInt256, Vector128<ulong>>(ref res);
            earlyResult = sumLo;
            Unsafe.Add(ref earlyResult, 1) = sumHi;
        }

        Vector128<ulong> propagatedLo = Vector128.Equals(sumLo, Vector128<ulong>.Zero) & carryInLo;
        Vector128<ulong> propagatedHi = Vector128.Equals(sumHi, Vector128<ulong>.Zero) & carryInHi;
        // Void ARM Add drops propagatedHi[1]: the early store already wrapped limb 3,
        // and its carry out is discarded. This is the same restriction as the AVX 0b0110 mask.
        Vector128<ulong> propagate = AdvSimd.IsSupported && !detectOverflow
            ? AdvSimd.ExtractVector128(propagatedLo, propagatedHi, 1)
            #if EXTRACTED_HELPER
: MergePropagation(propagatedLo, propagatedHi);
#else
: propagatedLo | propagatedHi;
#endif
        if (!Vector128.EqualsAll(propagate, Vector128<ulong>.Zero))
        {
            #if FEATURE_EXPRESSIONS
        if (AdvSimd.IsSupported & AdvSimd.IsSupported)
#else
        if (AdvSimd.IsSupported)
#endif
            {
                // The low half is complete. Repair the remaining two carry hops in the high half.
                Vector128<ulong> secondHi = detectOverflow
                    ? AdvSimd.ExtractVector128(propagatedLo, propagatedHi, 1)
                    : propagate;
                Vector128<ulong> fullHi = Vector128.Equals(sumHi, Vector128<ulong>.AllBitsSet);
                Vector128<ulong> thirdHi = AdvSimd.ExtractVector128(Vector128<ulong>.Zero, fullHi & secondHi, 1);
                Vector128<ulong> extra = secondHi | thirdHi;
                carryHi |= propagatedHi | (fullHi & extra);
                #if WRONG_TOP
sumHi -= Vector128.Create(extra.GetElement(0), 0UL);
#else
sumHi -= extra;
#endif
                ref Vector128<ulong> resultRef = ref Unsafe.As<UInt256, Vector128<ulong>>(ref res);
                Unsafe.Add(ref resultRef, 1) = sumHi;
                return carryHi.GetElement(1) != 0;
            }

            // Only the non-ARM path reaches this fallback: the early store is guarded by AdvSimd.
            // No non-ARM store has occurred, so a and b remain intact when res aliases either input.
            ulong carry = 0;
#if INLINE_CARRY
            ulong tempr0 = a.u0 + b.u0;
            ulong r0 = tempr0 + carry;
            carry = (tempr0 < a.u0 ? 1UL : 0UL) + (r0 < tempr0 ? 1UL : 0UL);
#else
            AddWithCarry(a.u0, b.u0, ref carry, out ulong r0);
#endif
#if INLINE_CARRY
            ulong tempr1 = a.u1 + b.u1;
            ulong r1 = tempr1 + carry;
            carry = (tempr1 < a.u1 ? 1UL : 0UL) + (r1 < tempr1 ? 1UL : 0UL);
#else
            AddWithCarry(a.u1, b.u1, ref carry, out ulong r1);
#endif
#if INLINE_CARRY
            ulong tempr2 = a.u2 + b.u2;
            ulong r2 = tempr2 + carry;
            carry = (tempr2 < a.u2 ? 1UL : 0UL) + (r2 < tempr2 ? 1UL : 0UL);
#else
            AddWithCarry(a.u2, b.u2, ref carry, out ulong r2);
#endif
#if INLINE_CARRY
            ulong tempr3 = a.u3 + b.u3;
            ulong r3 = tempr3 + carry;
            carry = (tempr3 < a.u3 ? 1UL : 0UL) + (r3 < tempr3 ? 1UL : 0UL);
#else
            AddWithCarry(a.u3, b.u3, ref carry, out ulong r3);
#endif
#if REVERSED_STORE
            StoreLimbs(out res, r3, r2, r1, r0);
#else
            StoreLimbs(out res, r0, r1, r2, r3);
#endif
            return carry != 0;
        }

        if (!AdvSimd.IsSupported)
        {
            ref Vector128<ulong> resRef = ref Unsafe.As<UInt256, Vector128<ulong>>(ref res);
            resRef = sumLo;
            Unsafe.Add(ref resRef, 1) = sumHi;
        }
        return carryHi.GetElement(1) != 0;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
#if RENAMED
    private static bool SumWord(in UInt256 a, ulong b0, out UInt256 res)
#else
    private static bool AddScalarUInt64(in UInt256 a, ulong b0, out UInt256 res)
#endif
    {
        ulong a0 = a.u0, a1 = a.u1, a2 = a.u2, a3 = a.u3;
        #if FEATURE_EXPRESSIONS
        if (AdvSimd.IsSupported & AdvSimd.IsSupported)
#else
        if (AdvSimd.IsSupported)
#endif
        {
            ulong low = a0 + b0;
            bool overflow = false;
            // Short-circuit each increment: higher limbs change only while the carry keeps rippling.
            if (low < a0 && ++a1 == 0 && ++a2 == 0) overflow = ++a3 == 0;
#if REVERSED_STORE
            StoreLimbs(out res, a3, a2, a1, low);
#else
            StoreLimbs(out res, low, a1, a2, a3);
#endif
            return overflow;
        }
        ulong r0 = a0 + b0;
        if (r0 >= a0)
        {
#if REVERSED_STORE
            StoreLimbs(out res, a3, a2, a1, r0);
#else
            StoreLimbs(out res, r0, a1, a2, a3);
#endif
            return false;
        }
        if (++a1 != 0)
        {
#if REVERSED_STORE
            StoreLimbs(out res, a3, a2, a1, r0);
#else
            StoreLimbs(out res, r0, a1, a2, a3);
#endif
            return false;
        }
        if (++a2 != 0)
        {
#if REVERSED_STORE
            StoreLimbs(out res, a3, a2, 0, r0);
#else
            StoreLimbs(out res, r0, 0, a2, a3);
#endif
            return false;
        }
        if (++a3 != 0)
        {
#if REVERSED_STORE
            StoreLimbs(out res, a3, 0, 0, r0);
#else
            StoreLimbs(out res, r0, 0, 0, a3);
#endif
            return false;
        }
#if REVERSED_STORE

        StoreLimbs(out res, 0, 0, 0, r0);
#else

        StoreLimbs(out res, r0, 0, 0, 0);
#endif
        return true;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void AddWithCarry(ulong x, ulong y, ref ulong carry, out ulong sum)
    {
        ulong t = x + y;
        ulong r = t + carry;
        carry = (t < x ? 1UL : 0UL) + (r < t ? 1UL : 0UL);
        sum = r;
    }

    /// <summary>Subtracts the fixture operands modulo 2^256.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void Subtract(in UInt256 a, in UInt256 b, out UInt256 res)
    {
#if RENAMED
        DifferenceDispatcher(in a, in b, out res);
#else
        SubtractImpl(in a, in b, out res);
#endif
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
#if RENAMED
    private static bool DifferenceDispatcher(in UInt256 a, in UInt256 b, out UInt256 res)
#else
    private static bool SubtractImpl(in UInt256 a, in UInt256 b, out UInt256 res)
#endif
    {
        #if FEATURE_EXPRESSIONS
        if (Avx2.IsSupported & Avx2.IsSupported)
#else
        if (Avx2.IsSupported)
#endif
        {
            Vector256<ulong> av = Unsafe.BitCast<UInt256, Vector256<ulong>>(a);
            Vector256<ulong> bv = Unsafe.BitCast<UInt256, Vector256<ulong>>(b);

            Vector256<ulong> result = av - bv;
            // All bits set in lanes where a < b, and in lanes whose lower neighbour borrowed
            Vector256<ulong> borrowMask;
            Vector256<ulong> borrowIn;
            #if FEATURE_EXPRESSIONS
        if (Avx512F.VL.IsSupported & Avx.IsSupported)
#else
        if (Avx512F.VL.IsSupported)
#endif
            {
                // Sign bit of (~a & b) | (~(a ^ b) & result) is the borrow; one ternary-logic op
                #if WRONG_TERNARY
borrowMask = Vector256.ShiftRightArithmetic(Avx512F.VL.TernaryLogic(av, bv, result, 0x00).AsInt64(), 63).AsUInt64();
#else
borrowMask = Vector256.ShiftRightArithmetic(Avx512F.VL.TernaryLogic(av, bv, result, 0x8E).AsInt64(), 63).AsUInt64();
#endif
#if WRONG_AVX_ALIGNMENT
                borrowIn = Avx512F.VL.AlignRight64(borrowMask, Vector256<ulong>.Zero, 2);
#else
                borrowIn = Avx512F.VL.AlignRight64(borrowMask, Vector256<ulong>.Zero, 3);
#endif
            }
            else
            {
                // Form borrows independently of result to shorten the dependency chain.
                borrowMask = Vector256.LessThan(av, bv);
#if EQUIVALENT_MASK
#if WRONG_BLEND
                borrowIn = Avx2.Blend(Avx2.Permute4x64(borrowMask, 0b10_01_00_00).AsUInt32(), Vector256<uint>.Zero, 0b0000_1111).AsUInt64();
#else
                borrowIn = Avx2.Blend(Avx2.Permute4x64(borrowMask, 0b10_01_00_00).AsUInt32(), Vector256<uint>.Zero, 0b0000_0011).AsUInt64();
#endif
#else
                #if WRONG_BLEND
borrowIn = Avx2.Permute4x64(borrowMask, 0b10_01_00_00) & Vector256.Create(0UL, 0UL, ulong.MaxValue, ulong.MaxValue);
#else
borrowIn = Avx2.Permute4x64(borrowMask, 0b10_01_00_00) & Vector256.Create(0UL, ulong.MaxValue, ulong.MaxValue, ulong.MaxValue);
#endif
#endif
            }

            // res may alias a or b, so the cascade path below must only use registers already loaded.
            // Storing ahead of the branch measured 25% faster on AVX2-only parts.
            Unsafe.SkipInit(out res);
            Unsafe.As<UInt256, Vector256<ulong>>(ref res) = result + borrowIn;

            // A zero limb that receives a borrow must pass it on; rare, so it resolves through the lookup
            #if WRONG_PREDICATE
Vector256<ulong> zeroLanes = Vector256.Equals(result, Vector256<ulong>.AllBitsSet);
#else
#if EARLY_REREAD
Vector256<ulong> zeroLanes = Vector256.Equals(Unsafe.BitCast<UInt256, Vector256<ulong>>(a), bv);
#else
Vector256<ulong> zeroLanes = Vector256.Equals(av, bv);
#endif
#endif
            if (!Avx.TestZ(zeroLanes, borrowIn))
            {
                uint borrow = (uint)Avx.MoveMask(borrowMask.AsDouble());
                uint cascade = (uint)Avx.MoveMask(zeroLanes.AsDouble());
                // Move borrow to next bit and add cascade; carries ripple through consecutive zero limbs
                #if EXTRACTED_HELPER
borrow = AccumulateCascade(cascade, borrow);
#else
borrow = cascade + 2 * borrow;
#endif
                // Keep only the cascades a borrow reached
                cascade ^= borrow;
                cascade &= 0x0f;

                #if WRONG_SCALE
Vector256<ulong> cascadedBorrows = Unsafe.Add(ref Unsafe.As<byte, Vector256<ulong>>(ref MemoryMarshal.GetReference(BroadcastLookup)), (nuint)(cascade << 1));
#else
Vector256<ulong> cascadedBorrows = Unsafe.Add(ref Unsafe.As<byte, Vector256<ulong>>(ref MemoryMarshal.GetReference(BroadcastLookup)), (nuint)cascade);
#endif
                Unsafe.As<UInt256, Vector256<ulong>>(ref res) = result - cascadedBorrows;
                return Bmi1.IsSupported
                    ? Unsafe.BitCast<byte, bool>((byte)Bmi1.BitFieldExtract(borrow, 4, 1))
                    : (borrow & 0b1_0000) != 0;
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
#if RENAMED
            return DifferenceWord(in a, b0, out res);
#else
            return SubtractScalarUInt64(in a, b0, out res);
#endif
        }

        if (AdvSimd.IsSupported || Sse42.IsSupported)
        {
#if RENAMED
            return PairDifference128(in a, in b, out res);
#else
            return SubtractVector128(in a, in b, out res);
#endif
        }

        // Loads stay next to their use: the one-limb path above shares this method's prolog
        ulong borrow = 0;
#if INLINE_CARRY
        ulong tempr0 = a.u0 - b0;
        ulong r0 = tempr0 - borrow;
        borrow = (a.u0 < b0 ? 1UL : 0UL) | (tempr0 < borrow ? 1UL : 0UL);
#else
        SubtractWithBorrow(a.u0, b0, ref borrow, out ulong r0);
#endif
#if INLINE_CARRY
        ulong tempr1 = a.u1 - b.u1;
        ulong r1 = tempr1 - borrow;
        borrow = (a.u1 < b.u1 ? 1UL : 0UL) | (tempr1 < borrow ? 1UL : 0UL);
#else
        SubtractWithBorrow(a.u1, b.u1, ref borrow, out ulong r1);
#endif
#if INLINE_CARRY
        ulong tempr2 = a.u2 - b.u2;
        ulong r2 = tempr2 - borrow;
        borrow = (a.u2 < b.u2 ? 1UL : 0UL) | (tempr2 < borrow ? 1UL : 0UL);
#else
        SubtractWithBorrow(a.u2, b.u2, ref borrow, out ulong r2);
#endif
#if INLINE_CARRY
        ulong tempr3 = a.u3 - b.u3;
        ulong r3 = tempr3 - borrow;
        borrow = (a.u3 < b.u3 ? 1UL : 0UL) | (tempr3 < borrow ? 1UL : 0UL);
#else
        #if WRONG_TOP
ulong r3 = a.u3 - b.u3;
            borrow = 0;
#else
SubtractWithBorrow(a.u3, b.u3, ref borrow, out ulong r3);
#endif
#endif
#if REVERSED_STORE
        StoreLimbs(out res, r3, r2, r1, r0);
#else
        StoreLimbs(out res, r0, r1, r2, r3);
#endif
        return borrow != 0;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
#if RENAMED
    private static bool PairDifference128(in UInt256 a, in UInt256 b, out UInt256 res)
#else
    private static bool SubtractVector128(in UInt256 a, in UInt256 b, out UInt256 res)
#endif
    {
        ref Vector128<ulong> aRef = ref Unsafe.As<UInt256, Vector128<ulong>>(ref Unsafe.AsRef(in a));
        ref Vector128<ulong> bRef = ref Unsafe.As<UInt256, Vector128<ulong>>(ref Unsafe.AsRef(in b));
#if LANE_LOCALS
        Vector128<ulong> bHi = Unsafe.Add(ref bRef, 1);
        Vector128<ulong> aLo = aRef;
        Vector128<ulong> bLo = bRef;
        Vector128<ulong> aHi = Unsafe.Add(ref aRef, 1);
#else
        Vector128<ulong> aLo = aRef;
        Vector128<ulong> aHi = Unsafe.Add(ref aRef, 1);
        Vector128<ulong> bLo = bRef;
        Vector128<ulong> bHi = Unsafe.Add(ref bRef, 1);
#endif

        Vector128<ulong> resultLo = aLo - bLo;
        Vector128<ulong> resultHi = aHi - bHi;
        Vector128<ulong> borrowLo = Vector128.LessThan(aLo, bLo);
        Vector128<ulong> borrowHi = Vector128.LessThan(aHi, bHi);

        // Lane i receives the borrow of lane i-1: [0, lo0] and [lo1, hi0]
        Vector128<ulong> borrowInLo;
        Vector128<ulong> borrowInHi;
        #if FEATURE_EXPRESSIONS
        if (AdvSimd.IsSupported & AdvSimd.IsSupported)
#else
        if (AdvSimd.IsSupported)
#endif
        {
            // ext takes its low lanes from the first operand: (second:first) >> 64 bits
            borrowInLo = AdvSimd.ExtractVector128(Vector128<ulong>.Zero, borrowLo, 1);
            #if WRONG_ALIGNMENT
borrowInHi = AdvSimd.ExtractVector128(borrowLo, borrowHi, 0);
#else
#if EXTRACTED_HELPER
borrowInHi = ExtractPair(borrowLo, borrowHi);
#else
borrowInHi = AdvSimd.ExtractVector128(borrowLo, borrowHi, 1);
#endif
#endif
        }
        else
        {
            borrowInLo = Sse2.ShiftLeftLogical128BitLane(borrowLo, 8);
            #if WRONG_ALIGNMENT
borrowInHi = Ssse3.AlignRight(borrowHi.AsByte(), borrowLo.AsByte(), 0).AsUInt64();
#else
borrowInHi = Ssse3.AlignRight(borrowHi.AsByte(), borrowLo.AsByte(), 8).AsUInt64();
#endif
        }

        // A zero limb that receives a borrow must pass it on. The fallback stays inline and call-free: with a
        // call here the JIT parks the vector values in callee-saved registers and the shared prolog pays for it
        #if EXTRACTED_HELPER
Vector128<ulong> propagate = MergePropagation(
            Vector128.Equals(resultLo, Vector128<ulong>.Zero) & borrowInLo,
            Vector128.Equals(resultHi, Vector128<ulong>.Zero) & borrowInHi);
#else
Vector128<ulong> propagate = (Vector128.Equals(resultLo, Vector128<ulong>.Zero) & borrowInLo)
                                   | (Vector128.Equals(resultHi, Vector128<ulong>.Zero) & borrowInHi);
#endif
        if (!Vector128.EqualsAll(propagate, Vector128<ulong>.Zero))
        {
            // Nothing has been stored yet, so a and b are intact even when res aliases one of them
            ulong borrow = 0;
#if INLINE_CARRY
            ulong tempr0 = a.u0 - b.u0;
            ulong r0 = tempr0 - borrow;
            borrow = (a.u0 < b.u0 ? 1UL : 0UL) | (tempr0 < borrow ? 1UL : 0UL);
#else
            SubtractWithBorrow(a.u0, b.u0, ref borrow, out ulong r0);
#endif
#if INLINE_CARRY
            ulong tempr1 = a.u1 - b.u1;
            ulong r1 = tempr1 - borrow;
            borrow = (a.u1 < b.u1 ? 1UL : 0UL) | (tempr1 < borrow ? 1UL : 0UL);
#else
            SubtractWithBorrow(a.u1, b.u1, ref borrow, out ulong r1);
#endif
#if INLINE_CARRY
            ulong tempr2 = a.u2 - b.u2;
            ulong r2 = tempr2 - borrow;
            borrow = (a.u2 < b.u2 ? 1UL : 0UL) | (tempr2 < borrow ? 1UL : 0UL);
#else
            SubtractWithBorrow(a.u2, b.u2, ref borrow, out ulong r2);
#endif
#if INLINE_CARRY
            ulong tempr3 = a.u3 - b.u3;
            ulong r3 = tempr3 - borrow;
            borrow = (a.u3 < b.u3 ? 1UL : 0UL) | (tempr3 < borrow ? 1UL : 0UL);
#else
            #if WRONG_TOP
ulong r3 = a.u3 - b.u3;
            borrow = 0;
#else
SubtractWithBorrow(a.u3, b.u3, ref borrow, out ulong r3);
#endif
#endif
#if REVERSED_STORE
            StoreLimbs(out res, r3, r2, r1, r0);
#else
            StoreLimbs(out res, r0, r1, r2, r3);
#endif
            return borrow != 0;
        }

        Unsafe.SkipInit(out res);
        ref Vector128<ulong> resRef = ref Unsafe.As<UInt256, Vector128<ulong>>(ref res);
        resRef = resultLo + borrowInLo;
        Unsafe.Add(ref resRef, 1) = resultHi + borrowInHi;
        return borrowHi.GetElement(1) != 0;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
#if RENAMED
    private static bool DifferenceWord(in UInt256 a, ulong b0, out UInt256 res)
#else
    private static bool SubtractScalarUInt64(in UInt256 a, ulong b0, out UInt256 res)
#endif
    {
        ulong a0 = a.u0, a1 = a.u1, a2 = a.u2, a3 = a.u3;
        ulong r0 = a0 - b0;
        if (a0 >= b0)
        {
#if REVERSED_STORE
            StoreLimbs(out res, a3, a2, a1, r0);
#else
            StoreLimbs(out res, r0, a1, a2, a3);
#endif
            return false;
        }
        if (a1 != 0)
        {
#if REVERSED_STORE
            StoreLimbs(out res, a3, a2, a1 - 1, r0);
#else
            StoreLimbs(out res, r0, a1 - 1, a2, a3);
#endif
            return false;
        }
        if (a2 != 0)
        {
#if REVERSED_STORE
            StoreLimbs(out res, a3, a2 - 1, ulong.MaxValue, r0);
#else
            StoreLimbs(out res, r0, ulong.MaxValue, a2 - 1, a3);
#endif
            return false;
        }
        if (a3 != 0)
        {
#if REVERSED_STORE
            StoreLimbs(out res, a3 - 1, ulong.MaxValue, ulong.MaxValue, r0);
#else
            StoreLimbs(out res, r0, ulong.MaxValue, ulong.MaxValue, a3 - 1);
#endif
            return false;
        }
#if REVERSED_STORE

        StoreLimbs(out res, ulong.MaxValue, ulong.MaxValue, ulong.MaxValue, r0);
#else

        StoreLimbs(out res, r0, ulong.MaxValue, ulong.MaxValue, ulong.MaxValue);
#endif
        return true;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void StoreLimbs(out UInt256 res, ulong r0, ulong r1, ulong r2, ulong r3)
    {
        Unsafe.SkipInit(out res);
#if REVERSED_STORE
        Unsafe.AsRef(in res.u0) = r3;
#else
        Unsafe.AsRef(in res.u0) = r0;
#endif
#if REVERSED_STORE
        Unsafe.AsRef(in res.u1) = r2;
#else
        Unsafe.AsRef(in res.u1) = r1;
#endif
#if REVERSED_STORE
        Unsafe.AsRef(in res.u2) = r1;
#else
        Unsafe.AsRef(in res.u2) = r2;
#endif
#if REVERSED_STORE
        Unsafe.AsRef(in res.u3) = r0;
#else
        Unsafe.AsRef(in res.u3) = r3;
#endif
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void SubtractWithBorrow(ulong a, ulong b, ref ulong borrow, out ulong res)
    {
        res = a - b - borrow;
        borrow = (a < b ? 1UL : 0UL) | (borrow & (a == b ? 1UL : 0UL));
    }
}
