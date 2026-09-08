// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics.Arm;
using System.Runtime.Intrinsics.X86;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    // Hardware x64 reaches the crossover sooner; ARM and software products
    // amortize the six-term polynomial over a shorter remaining prefix.
    private static int ExpFourTermPrecision
    {
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        get => Bmi2.X64.IsSupported ? 52 : 56;
    }

    [SkipLocalsInit]
    private static void ExpOddLongPhased(in UInt256 b, in UInt256 e, int squares, out UInt256 result)
    {
        // For odd b, b^2 = 1 mod 8. Each further square adds at least
        // one zero bit to b^(2^k)-1, hence b^(2^62) = 1 mod 2^64.
        // More precisely v2(b^(2^k)-1) = v2(b-1)+v2(b+1)+k-1.
        // The caller handles low limbs +/-1, leaving a cutoff in [1,62].
        // Exactly one of b-1 and b+1 has valuation one. Select the other
        // without a branch, so only one trailing-zero count is needed.
        UInt256 power = b;
        UInt256 value = (e.u0 & 1) != 0 ? b : One;
        ulong bits = e.u0 >> 1;
        int i = 1;
        if (!(Bmi2.X64.IsSupported || ArmBase.Arm64.IsSupported))
        {
            // After j >= 1 squares the precision is t+j, where t=64-squares.
            // Split at 32 bits so the second phase needs no precision test.
            int stop = Math.Min(squares, Math.Max(2, squares - 31));
            for (; i < stop; ++i)
            {
                SquareExpLong(power, out power);
                if ((bits & 1) != 0) MultiplyExpPower(value, power, out value);
                bits >>= 1;
            }
            for (; i < squares; ++i)
            {
                SquareExpLowOne32(power, out power);
                if ((bits & 1) != 0) MultiplyExpLowOne32(value, power, out value);
                bits >>= 1;
            }
        }
        else
        {
            for (; i < squares; ++i)
            {
                SquareExpLong(power, out power);
                if ((bits & 1) != 0) MultiplyExpPower(value, power, out value);
                bits >>= 1;
            }
        }
        SquareExpPrefix(power, out power);
        int left = 64 - squares;
        UInt256 high = new((e.u0 >> squares) | (e.u1 << left),
            (e.u1 >> squares) | (e.u2 << left), (e.u2 >> squares) | (e.u3 << left), e.u3 >> squares);
        ExpNearOne64(power, high, out power);
        // NEON's existing final product avoids a sparse-power scheduling regression.
        if (ArmBase.Arm64.IsSupported)
            Multiply(value, power, out result);
        else
            MultiplyExpNearOne(value, power, out result);
    }

    [SkipLocalsInit]
    private static void ExpOddLong32(in UInt256 b, in UInt256 e, int squares, out UInt256 result)
    {
        UInt256 power = b;
        UInt256 value = (e.u0 & 1) != 0 ? b : One;
        ulong bits = e.u0 >> 1;
        for (int i = 1; i < squares; ++i)
        {
            SquareExpLong(power, out power);
            if ((bits & 1) != 0) MultiplyExpPower(value, power, out value);
            bits >>= 1;
        }
        SquareExpLong(power, out power);
        int left = 64 - squares;
        UInt256 high = new((e.u0 >> squares) | (e.u1 << left), (e.u1 >> squares) | (e.u2 << left), (e.u2 >> squares) | (e.u3 << left), e.u3 >> squares);
        ExpNearOne32(power, high, out power);
        Multiply(value, power, out result);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void ExpNearOne32Signed(in UInt256 b, in UInt256 e, bool sixTerms, out UInt256 result)
    {
        // No squaring prefix is needed when the base already has 32-bit precision.
        // For negative bases, only the bits above bit 31 enter the polynomial.
        ulong sign = 0UL - ((b.u0 >> 1) & 1);
        UInt256 positive = CreateExpLimbs(b.u0 ^ sign, b.u1 ^ sign, b.u2 ^ sign, b.u3 ^ sign);
        UInt256 value;
        if (sixTerms) ExpNearOne43(positive, e, out value);
        else ExpNearOne32(positive, e, out value);
        sign &= 0UL - (e.u0 & 1);
        result = CreateExpLimbs((value.u0 ^ sign) + (sign & 1), value.u1 ^ sign, value.u2 ^ sign, value.u3 ^ sign);
    }

    private static void ExpNearOne43(in UInt256 b, in UInt256 e, out UInt256 result)
    {
        // Existing 43-bit precision leaves only six terms. Use the same
        // guarded recurrence, retaining 256-43*k bits in term k.
        UInt256 x = CreateExpLimbs((b.u0 >> 43) | (b.u1 << 21), (b.u1 >> 43) | (b.u2 << 21), (b.u2 >> 43) | (b.u3 << 21), b.u3 >> 43);
        UInt256 factor = e;
        Multiply(x, factor, out UInt256 term);
        UInt256 sum = One + CreateExpLimbs((term.u0 << 43), (term.u1 << 43) | (term.u0 >> 21), (term.u2 << 43) | (term.u1 >> 21), (term.u3 << 43) | (term.u2 >> 21));
        factor = CreateExpLimbs(e.u0 - 1UL, e.u1 - (e.u0 < 1 ? 1UL : 0UL), e.u2 - (e.u0 < 1 && e.u1 == 0 ? 1UL : 0UL), e.u3 - (e.u0 < 1 && e.u1 == 0 && e.u2 == 0 ? 1UL : 0UL));
        MultiplyExpTruncated(term, factor, 3, out term);
        term = CreateExpLimbs((term.u0 >> 1) | (term.u1 << 63), (term.u1 >> 1) | (term.u2 << 63), (term.u2 >> 1) | (term.u3 << 63), term.u3 >> 1);
        MultiplyExpTruncated(term, x, 3, out term);
        sum += CreateExpLimbs(0, (term.u0 << 22), (term.u1 << 22) | (term.u0 >> 42), (term.u2 << 22) | (term.u1 >> 42));
        factor = CreateExpLimbs(e.u0 - 2UL, e.u1 - (e.u0 < 2 ? 1UL : 0UL), e.u2 - (e.u0 < 2 && e.u1 == 0 ? 1UL : 0UL), e.u3 - (e.u0 < 2 && e.u1 == 0 && e.u2 == 0 ? 1UL : 0UL));
        MultiplyExpTruncated(term, factor, 2, out term);
        MultiplyExpTruncated(term, CreateExpLimbs(0xAAAAAAAAAAAAAAABUL, 0xAAAAAAAAAAAAAAAAUL, 0xAAAAAAAAAAAAAAAAUL, 0xAAAAAAAAAAAAAAAAUL), 2, out term);
        MultiplyExpTruncated(term, x, 2, out term);
        sum += CreateExpLimbs(0, 0, (term.u0 << 1), (term.u1 << 1) | (term.u0 >> 63));
        factor = CreateExpLimbs(e.u0 - 3UL, e.u1 - (e.u0 < 3 ? 1UL : 0UL), e.u2 - (e.u0 < 3 && e.u1 == 0 ? 1UL : 0UL), e.u3 - (e.u0 < 3 && e.u1 == 0 && e.u2 == 0 ? 1UL : 0UL));
        MultiplyExpTruncated(term, factor, 2, out term);
        term = CreateExpLimbs((term.u0 >> 2) | (term.u1 << 62), (term.u1 >> 2) | (term.u2 << 62), (term.u2 >> 2) | (term.u3 << 62), term.u3 >> 2);
        MultiplyExpTruncated(term, x, 2, out term);
        sum += CreateExpLimbs(0, 0, (term.u0 << 44), (term.u1 << 44) | (term.u0 >> 20));
        factor = CreateExpLimbs(e.u0 - 4UL, e.u1 - (e.u0 < 4 ? 1UL : 0UL), e.u2 - (e.u0 < 4 && e.u1 == 0 ? 1UL : 0UL), e.u3 - (e.u0 < 4 && e.u1 == 0 && e.u2 == 0 ? 1UL : 0UL));
        MultiplyExpTruncated(term, factor, 1, out term);
        MultiplyExpTruncated(term, CreateExpLimbs(0xCCCCCCCCCCCCCCCDUL, 0xCCCCCCCCCCCCCCCCUL, 0xCCCCCCCCCCCCCCCCUL, 0xCCCCCCCCCCCCCCCCUL), 1, out term);
        MultiplyExpTruncated(term, x, 1, out term);
        sum += CreateExpLimbs(0, 0, 0, (term.u0 << 23));
        result = sum;
    }

    private static void ExpNearOne32(in UInt256 b, in UInt256 e, out UInt256 result)
    {
        // b = 1 + x*2^32. Terms k >= 8 vanish modulo 2^256.
        // Keep S_k = C(e,k)*x^k and add S_k << (32*k). The recurrence
        // S_k = S_(k-1)*(e-k+1)/k*x uses exact division by powers of two
        // and modular inverses for odd divisors. Before each right shift,
        // retain its guard bits; each preceding term has 32 extra bits,
        // more than the at-most-two bits consumed by these divisions.
        // The caller guarantees e >= 7 and supplies the upper bits of
        // a base normalized to +1 mod 2^32; the low 32 bits are discarded.
        // Fixed limb stores avoid constructor/shift calls in this large body.
        UInt256 x = CreateExpLimbs((b.u0 >> 32) | (b.u1 << 32), (b.u1 >> 32) | (b.u2 << 32), (b.u2 >> 32) | (b.u3 << 32), b.u3 >> 32);
        UInt256 factor = e;
        Multiply(x, factor, out UInt256 term);
        UInt256 sum = One + CreateExpLimbs((term.u0 << 32), (term.u1 << 32) | (term.u0 >> 32), (term.u2 << 32) | (term.u1 >> 32), (term.u3 << 32) | (term.u2 >> 32));
        factor = CreateExpLimbs(e.u0 - 1UL, e.u1 - (e.u0 < 1 ? 1UL : 0UL), e.u2 - (e.u0 < 1 && e.u1 == 0 ? 1UL : 0UL), e.u3 - (e.u0 < 1 && e.u1 == 0 && e.u2 == 0 ? 1UL : 0UL));
        MultiplyExpTruncated(term, factor, 4, out term);
        term = CreateExpLimbs((term.u0 >> 1) | (term.u1 << 63), (term.u1 >> 1) | (term.u2 << 63), (term.u2 >> 1) | (term.u3 << 63), term.u3 >> 1);
        MultiplyExpTruncated(term, x, 3, out term);
        sum += CreateExpLimbs(0, term.u0, term.u1, term.u2);
        factor = CreateExpLimbs(e.u0 - 2UL, e.u1 - (e.u0 < 2 ? 1UL : 0UL), e.u2 - (e.u0 < 2 && e.u1 == 0 ? 1UL : 0UL), e.u3 - (e.u0 < 2 && e.u1 == 0 && e.u2 == 0 ? 1UL : 0UL));
        MultiplyExpTruncated(term, factor, 3, out term);
        MultiplyExpTruncated(term, CreateExpLimbs(0xAAAAAAAAAAAAAAABUL, 0xAAAAAAAAAAAAAAAAUL, 0xAAAAAAAAAAAAAAAAUL, 0xAAAAAAAAAAAAAAAAUL), 3, out term);
        MultiplyExpTruncated(term, x, 3, out term);
        sum += CreateExpLimbs(0, (term.u0 << 32), (term.u1 << 32) | (term.u0 >> 32), (term.u2 << 32) | (term.u1 >> 32));
        factor = CreateExpLimbs(e.u0 - 3UL, e.u1 - (e.u0 < 3 ? 1UL : 0UL), e.u2 - (e.u0 < 3 && e.u1 == 0 ? 1UL : 0UL), e.u3 - (e.u0 < 3 && e.u1 == 0 && e.u2 == 0 ? 1UL : 0UL));
        MultiplyExpTruncated(term, factor, 3, out term);
        term = CreateExpLimbs((term.u0 >> 2) | (term.u1 << 62), (term.u1 >> 2) | (term.u2 << 62), (term.u2 >> 2) | (term.u3 << 62), term.u3 >> 2);
        MultiplyExpTruncated(term, x, 2, out term);
        sum += CreateExpLimbs(0, 0, term.u0, term.u1);
        factor = CreateExpLimbs(e.u0 - 4UL, e.u1 - (e.u0 < 4 ? 1UL : 0UL), e.u2 - (e.u0 < 4 && e.u1 == 0 ? 1UL : 0UL), e.u3 - (e.u0 < 4 && e.u1 == 0 && e.u2 == 0 ? 1UL : 0UL));
        MultiplyExpTruncated(term, factor, 2, out term);
        MultiplyExpTruncated(term, CreateExpLimbs(0xCCCCCCCCCCCCCCCDUL, 0xCCCCCCCCCCCCCCCCUL, 0xCCCCCCCCCCCCCCCCUL, 0xCCCCCCCCCCCCCCCCUL), 2, out term);
        MultiplyExpTruncated(term, x, 2, out term);
        sum += CreateExpLimbs(0, 0, (term.u0 << 32), (term.u1 << 32) | (term.u0 >> 32));
        factor = CreateExpLimbs(e.u0 - 5UL, e.u1 - (e.u0 < 5 ? 1UL : 0UL), e.u2 - (e.u0 < 5 && e.u1 == 0 ? 1UL : 0UL), e.u3 - (e.u0 < 5 && e.u1 == 0 && e.u2 == 0 ? 1UL : 0UL));
        MultiplyExpTruncated(term, factor, 2, out term);
        term = CreateExpLimbs((term.u0 >> 1) | (term.u1 << 63), (term.u1 >> 1) | (term.u2 << 63), (term.u2 >> 1) | (term.u3 << 63), term.u3 >> 1);
        MultiplyExpTruncated(term, CreateExpLimbs(0xAAAAAAAAAAAAAAABUL, 0xAAAAAAAAAAAAAAAAUL, 0xAAAAAAAAAAAAAAAAUL, 0xAAAAAAAAAAAAAAAAUL), 1, out term);
        MultiplyExpTruncated(term, x, 1, out term);
        sum += CreateExpLimbs(0, 0, 0, term.u0);
        factor = CreateExpLimbs(e.u0 - 6UL, e.u1 - (e.u0 < 6 ? 1UL : 0UL), e.u2 - (e.u0 < 6 && e.u1 == 0 ? 1UL : 0UL), e.u3 - (e.u0 < 6 && e.u1 == 0 && e.u2 == 0 ? 1UL : 0UL));
        MultiplyExpTruncated(term, factor, 1, out term);
        MultiplyExpTruncated(term, CreateExpLimbs(0x6DB6DB6DB6DB6DB7UL, 0xB6DB6DB6DB6DB6DBUL, 0xDB6DB6DB6DB6DB6DUL, 0x6DB6DB6DB6DB6DB6UL), 1, out term);
        MultiplyExpTruncated(term, x, 1, out term);
        sum += CreateExpLimbs(0, 0, 0, (term.u0 << 32));
        result = sum;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void MultiplyExpTruncated(in UInt256 x, in UInt256 y, int limbs, out UInt256 result)
    {
        if (limbs == 4) { Multiply(x, y, out result); return; }
        if (limbs == 1) { result = CreateExpLimbs(x.u0 * y.u0); return; }
        ulong h00 = Multiply64(x.u0, y.u0, out ulong r0);
        if (limbs == 2)
        {
            result = CreateExpLimbs(r0, h00 + x.u0 * y.u1 + x.u1 * y.u0);
            return;
        }
        ulong h01 = Multiply64(x.u0, y.u1, out ulong l01);
        ulong h10 = Multiply64(x.u1, y.u0, out ulong l10);
        ulong carry = 0;
        ulong r1 = AddAndCountCarry(h00, l01, ref carry);
        r1 = AddAndCountCarry(r1, l10, ref carry);
        result = CreateExpLimbs(r0, r1, h01 + h10 + carry + x.u0 * y.u2 + x.u1 * y.u1 + x.u2 * y.u0);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static UInt256 CreateExpLimbs(ulong a, ulong b = 0, ulong c = 0, ulong d = 0)
    {
        StoreLimbs(out UInt256 result, a, b, c, d);
        return result;
    }

    [SkipLocalsInit]
    private static void ExpOddLongNear32(in UInt256 b, in UInt256 e, int squares, out UInt256 result)
    {
        // Guest-only path: the prefix reaches 32-bit precision immediately.
        UInt256 power = b;
        UInt256 value = (e.u0 & 1) != 0 ? b : One;
        ulong bits = e.u0 >> 1;
        for (int i = 1; i < squares; ++i)
        {
            SquareExpPrefix(power, out power);
            if ((bits & 1) != 0)
            {
                MultiplyExpPrefix(value, power, out value);
            }
            bits >>= 1;
        }
        SquareExpPrefix(power, out power);
        int left = 64 - squares;
        UInt256 high = new((e.u0 >> squares) | (e.u1 << left),
            (e.u1 >> squares) | (e.u2 << left), (e.u2 >> squares) | (e.u3 << left), e.u3 >> squares);
        ExpNearOne64(power, high, out power);
        MultiplyExpNearOne(value, power, out result);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void MultiplyExpPrefix(in UInt256 value, in UInt256 power, out UInt256 result)
    {
        if ((uint)power.u0 == 1)
            MultiplyExpLowOne32(value, power, out result);
        else
            MultiplyExpPower(value, power, out result);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void MultiplyExpLowOne32(in UInt256 x, in UInt256 y, out UInt256 res)
    {
        // Repeated odd squares eventually make y = 1 + q*2^32 (mod 2^64).
        // Software products by that limb need two 32x32 products instead of four.
        // Hardware widening multiplication keeps the established kernel.
        ulong q = y.u0 >> 32;
        ulong x0 = x.u0, x1 = x.u1, x2 = x.u2;
        ulong y1 = y.u1, y2 = y.u2;
        ulong r3 = x0 * y.u3 + x1 * y2 + x2 * y1 + x.u3 + ((q * (uint)x.u3) << 32);
        ulong h00 = MultiplyLowOne32(q, x0, out ulong r0);
        ulong h01 = Multiply64(x0, y1, out ulong l01);
        ulong h10 = MultiplyLowOne32(q, x1, out ulong l10);
        ulong carry = 0;
        ulong r1 = AddAndCountCarry(h00, l01, ref carry);
        r1 = AddAndCountCarry(r1, l10, ref carry);
        ulong r2 = carry;
        carry = 0;
        r2 = AddAndCountCarry(r2, h01, ref carry);
        r2 = AddAndCountCarry(r2, h10, ref carry);
        ulong h02 = Multiply64(x0, y2, out ulong l02);
        r2 = AddAndCountCarry(r2, l02, ref carry);
        r3 += h02;
        ulong h11 = Multiply64(x1, y1, out ulong l11);
        r2 = AddAndCountCarry(r2, l11, ref carry);
        r3 += h11;
        ulong h20 = MultiplyLowOne32(q, x2, out ulong l20);
        r2 = AddAndCountCarry(r2, l20, ref carry);
        r3 += h20 + carry;
        StoreProduct(out res, r0, r1, r2, r3);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void MultiplyExpNearOne(in UInt256 value, in UInt256 power, out UInt256 result)
    {
        if (value.IsUint64)
        {
            MultiplyByUInt64(power, value.u0, out result);
            return;
        }
        // power.u0 is one. Products by that limb are just additions.
        ulong h01 = Multiply64(value.u0, power.u1, out ulong l01);
        ulong h02 = Multiply64(value.u0, power.u2, out ulong l02);
        ulong h11 = Multiply64(value.u1, power.u1, out ulong l11);
        ulong r1 = value.u1 + l01;
        ulong carry = 0;
        ulong r2 = AddAndCountCarry(value.u2, h01, ref carry);
        r2 = AddAndCountCarry(r2, l02, ref carry);
        r2 = AddAndCountCarry(r2, l11, ref carry);
        r2 = AddAndCountCarry(r2, r1 < value.u1 ? 1UL : 0UL, ref carry);
        ulong r3 = value.u3 + h02 + h11 + carry
            + value.u0 * power.u3 + value.u1 * power.u2 + value.u2 * power.u1;
        StoreProduct(out result, value.u0, r1, r2, r3);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void SquareExpPrefix(in UInt256 value, out UInt256 result)
    {
        if (Bmi2.X64.IsSupported || ArmBase.Arm64.IsSupported || (uint)value.u0 != 1)
        {
            SquareExpLong(value, out result);
            return;
        }
        SquareExpLowOne32(value, out result);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void SquareExpLowOne32(in UInt256 value, out UInt256 result)
    {
        ulong q = value.u0 >> 32;
        // (1 + q*2^32)^2 has low limb 1 + q*2^33 and high limb
        // q^2 + (q >> 31). No general low-limb square is needed.
        ulong r0 = 1 | (q << 33);
        ulong h00 = q * q + (q >> 31);
        ulong h11 = Square64(value.u1, out ulong l11);
        ulong h01 = MultiplyLowOne32(q, value.u1, out ulong l01);
        ulong h02 = MultiplyLowOne32(q, value.u2, out ulong l02);
        ulong cross = h01 + l02;
        ulong upper = h02 + (cross < h01 ? 1UL : 0UL)
            + value.u3 + ((q * (uint)value.u3) << 32) + value.u1 * value.u2;
        ulong r1 = h00 + (l01 << 1);
        ulong carry = 0;
        ulong r2 = AddAndCountCarry(l11, (cross << 1) | (l01 >> 63), ref carry);
        r2 = AddAndCountCarry(r2, r1 < h00 ? 1UL : 0UL, ref carry);
        result = new UInt256(r0, r1, r2, h11 + (upper << 1) + (cross >> 63) + carry);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong MultiplyLowOne32(ulong q, ulong value, out ulong low)
    {
        // Multiply value by 1 + q*2^32; callers bound q to 32 bits.
        ulong p0 = q * (uint)value;
        low = value + (p0 << 32);
        return (p0 >> 32) + q * (value >> 32) + (low < value ? 1UL : 0UL);
    }

    private static void ExpNearOne64(in UInt256 b, in UInt256 e, out UInt256 result)
    {
        // b = +/- (1+x*2^64). Only four binomial terms survive modulo 2^256.
        ulong sign = b.u0 == 1 ? 0 : ulong.MaxValue;
        ulong x0 = b.u1 ^ sign, x1 = b.u2 ^ sign, x2 = b.u3 ^ sign;
        ulong e0 = e.u0, e1 = e.u1, e2 = e.u2;

        // e*x modulo 2^192, shifted up one limb in the result.
        ulong h00 = Multiply64(e0, x0, out ulong r1);
        ulong h01 = Multiply64(e0, x1, out ulong l01);
        ulong h10 = Multiply64(e1, x0, out ulong l10);
        ulong carry = 0;
        ulong r2 = AddAndCountCarry(h00, l01, ref carry);
        r2 = AddAndCountCarry(r2, l10, ref carry);
        ulong r3 = h01 + h10 + carry + e0 * x2 + e1 * x1 + e2 * x0;

        // C(e,2) modulo 2^128. Divide the even factor before multiplying;
        // its shifted high limb includes bit 128 of e.
        ulong a0 = (e0 >> 1) | (e1 << 63);
        ulong a1 = (e1 >> 1) | (e2 << 63);
        ulong c0 = e0 - ((~e0) & 1);
        ulong c1 = e1 - (e0 == 0 ? 1UL : 0UL);
        ulong coefficientHigh = Multiply64(a0, c0, out ulong coefficientLow) + a0 * c1 + a1 * c0;
        ulong squareHigh = Square64(x0, out ulong squareLow) + ((x0 * x1) << 1);
        ulong quadraticHigh = Multiply64(coefficientLow, squareLow, out ulong quadraticLow)
            + coefficientLow * squareHigh + coefficientHigh * squareLow;
        carry = 0;
        r2 = AddAndCountCarry(r2, quadraticLow, ref carry);
        r3 += quadraticHigh + carry;

        // C(e,3) modulo 2^64: after exact division by two, divide by three
        // using its inverse modulo 2^64. Terms beyond x^3 are discarded.
        ulong cubic = a0 * c0 * (e0 - 2) * 0xAAAAAAAAAAAAAAABUL;
        r3 += cubic * squareLow * x0;
        sign &= 0UL - (e0 & 1);
        result = new UInt256(1 | sign, r1 ^ sign, r2 ^ sign, r3 ^ sign);
    }

    private static void ExpLimbAligned(in UInt256 b, in UInt256 e, int bitLen, out UInt256 result)
    {
        // b = x*2^64 and e >= 2. Only e=2 or e=3 can survive modulo 2^256.
        if (bitLen > 2 || b.u1 == 0)
        {
            result = default;
        }
        else if (e.u0 == 2)
        {
            ulong high = Square64(b.u1, out ulong low);
            result = new UInt256(0, 0, low, high + ((b.u1 * b.u2) << 1));
        }
        else
        {
            result = new UInt256(0, 0, 0, b.u1 * b.u1 * b.u1);
        }
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong Square64(ulong x, out ulong low)
    {
        if (Bmi2.X64.IsSupported || ArmBase.Arm64.IsSupported)
            return Multiply64(x, x, out low);
        // Squaring needs only one 32x32 cross product; a generic multiply
        // computes it twice. Preserve the carry from the low 64-bit sum.
        ulong lo = (uint)x;
        ulong hi = x >> 32;
        ulong diagonal = lo * lo;
        ulong cross = lo * hi;
        low = diagonal + (cross << 33);
        return hi * hi + (cross >> 31) + (low < diagonal ? 1UL : 0UL);
    }

    private static void ExpNearOne(in UInt256 b, in UInt256 e, out UInt256 result)
    {
        // b = +/- (1 + x*2^128). Every term after the linear term in the
        // binomial expansion vanishes modulo 2^256, so only e's low 128 bits
        // matter: b^e = (+/-1)^e * (1 + e*x*2^128).
        ulong sign = b.u0 == 1 ? 0 : ulong.MaxValue;
        ulong x0 = b.u2 ^ sign;
        ulong x1 = b.u3 ^ sign;
        ulong high = Multiply64(e.u0, x0, out ulong low);
        high += e.u0 * x1 + e.u1 * x0;
        sign &= 0UL - (e.u0 & 1);
        result = new UInt256(1 | sign, sign, low ^ sign, high ^ sign);
    }

    [SkipLocalsInit]
    private static void ExpWindow(in UInt256 b, in UInt256 e, int bitLen, out UInt256 result)
    {
        // The caller routes long and suitable structured powers through binomial reduction.
        // Host code favors eight entries; the guest amortizes sixteen better.
        int width = bitLen <= 64 ? 4 : ExpWindowMaxWidth;
        Span<UInt256> powers = stackalloc UInt256[1 << (ExpWindowMaxWidth - 1)];
        powers[0] = b;
        SquareExpLong(b, out UInt256 square);
        for (int j = 1; j < (1 << (width - 1)); ++j)
            Multiply(powers[j - 1], square, out powers[j]);

        UInt256 val = One;
        for (int i = bitLen - 1; i >= 0;)
        {
            if ((Unsafe.Add(ref Unsafe.AsRef(in e.u0), i >> 6) & (1UL << i)) == 0)
            {
                SquareExpLong(val, out val);
                --i;
                continue;
            }
            int low = Math.Max(i - width + 1, 0);
            int shift = low & 63;
            // low <= bitLen - width (unless clamped to zero), so a window
            // crossing a limb boundary always has a next limb within e.
            ulong word = Unsafe.Add(ref Unsafe.AsRef(in e.u0), low >> 6) >> shift;
            if (shift > 64 - width)
                word |= Unsafe.Add(ref Unsafe.AsRef(in e.u0), (low >> 6) + 1) << (64 - shift);
            uint window = (uint)word & ((1u << (i - low + 1)) - 1);
            int trailing = BitOperations.TrailingZeroCount(window);
            low += trailing;
            window >>= trailing;
            if (i == bitLen - 1)
            {
                // Seed from the leading window: no squaring or multiplying one.
                val = powers[(int)(window >> 1)];
                i = low - 1;
                continue;
            }
            for (int j = i; j >= low; --j)
            {
                SquareExpLong(val, out val);
            }
            // Preserve cheap narrow table factors (e.g. base 3), but avoid the
            // general product's remaining width dispatch inside the hot loop.
            ref readonly UInt256 factor = ref powers[(int)(window >> 1)];
            if ((factor.u1 | factor.u2 | factor.u3) == 0)
                MultiplyByUInt64(val, factor.u0, out val);
            else
                MultiplyLimbs4x4(val, factor, out val);
            i = low - 1;
        }
        result = val;
    }

    // Little-endian limbs of every power of ten that fits in 256 bits.
    // A constant span is embedded data, with no array allocation or static constructor.
    private static ReadOnlySpan<ulong> PowersOfTen =>
    [
        0x0000000000000001UL, 0x0000000000000000UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^0
        0x000000000000000AUL, 0x0000000000000000UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^1
        0x0000000000000064UL, 0x0000000000000000UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^2
        0x00000000000003E8UL, 0x0000000000000000UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^3
        0x0000000000002710UL, 0x0000000000000000UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^4
        0x00000000000186A0UL, 0x0000000000000000UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^5
        0x00000000000F4240UL, 0x0000000000000000UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^6
        0x0000000000989680UL, 0x0000000000000000UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^7
        0x0000000005F5E100UL, 0x0000000000000000UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^8
        0x000000003B9ACA00UL, 0x0000000000000000UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^9
        0x00000002540BE400UL, 0x0000000000000000UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^10
        0x000000174876E800UL, 0x0000000000000000UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^11
        0x000000E8D4A51000UL, 0x0000000000000000UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^12
        0x000009184E72A000UL, 0x0000000000000000UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^13
        0x00005AF3107A4000UL, 0x0000000000000000UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^14
        0x00038D7EA4C68000UL, 0x0000000000000000UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^15
        0x002386F26FC10000UL, 0x0000000000000000UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^16
        0x016345785D8A0000UL, 0x0000000000000000UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^17
        0x0DE0B6B3A7640000UL, 0x0000000000000000UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^18
        0x8AC7230489E80000UL, 0x0000000000000000UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^19
        0x6BC75E2D63100000UL, 0x0000000000000005UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^20
        0x35C9ADC5DEA00000UL, 0x0000000000000036UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^21
        0x19E0C9BAB2400000UL, 0x000000000000021EUL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^22
        0x02C7E14AF6800000UL, 0x000000000000152DUL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^23
        0x1BCECCEDA1000000UL, 0x000000000000D3C2UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^24
        0x161401484A000000UL, 0x0000000000084595UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^25
        0xDCC80CD2E4000000UL, 0x000000000052B7D2UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^26
        0x9FD0803CE8000000UL, 0x00000000033B2E3CUL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^27
        0x3E25026110000000UL, 0x00000000204FCE5EUL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^28
        0x6D7217CAA0000000UL, 0x00000001431E0FAEUL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^29
        0x4674EDEA40000000UL, 0x0000000C9F2C9CD0UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^30
        0xC0914B2680000000UL, 0x0000007E37BE2022UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^31
        0x85ACEF8100000000UL, 0x000004EE2D6D415BUL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^32
        0x38C15B0A00000000UL, 0x0000314DC6448D93UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^33
        0x378D8E6400000000UL, 0x0001ED09BEAD87C0UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^34
        0x2B878FE800000000UL, 0x0013426172C74D82UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^35
        0xB34B9F1000000000UL, 0x00C097CE7BC90715UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^36
        0x00F436A000000000UL, 0x0785EE10D5DA46D9UL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^37
        0x098A224000000000UL, 0x4B3B4CA85A86C47AUL, 0x0000000000000000UL, 0x0000000000000000UL, // 10^38
        0x5F65568000000000UL, 0xF050FE938943ACC4UL, 0x0000000000000002UL, 0x0000000000000000UL, // 10^39
        0xB9F5610000000000UL, 0x6329F1C35CA4BFABUL, 0x000000000000001DUL, 0x0000000000000000UL, // 10^40
        0x4395CA0000000000UL, 0xDFA371A19E6F7CB5UL, 0x0000000000000125UL, 0x0000000000000000UL, // 10^41
        0xA3D9E40000000000UL, 0xBC627050305ADF14UL, 0x0000000000000B7AUL, 0x0000000000000000UL, // 10^42
        0x6682E80000000000UL, 0x5BD86321E38CB6CEUL, 0x00000000000072CBUL, 0x0000000000000000UL, // 10^43
        0x011D100000000000UL, 0x9673DF52E37F2410UL, 0x0000000000047BF1UL, 0x0000000000000000UL, // 10^44
        0x0B22A00000000000UL, 0xE086B93CE2F768A0UL, 0x00000000002CD76FUL, 0x0000000000000000UL, // 10^45
        0x6F5A400000000000UL, 0xC5433C60DDAA1640UL, 0x0000000001C06A5EUL, 0x0000000000000000UL, // 10^46
        0x5986800000000000UL, 0xB4A05BC8A8A4DE84UL, 0x00000000118427B3UL, 0x0000000000000000UL, // 10^47
        0x7F41000000000000UL, 0x0E4395D69670B12BUL, 0x00000000AF298D05UL, 0x0000000000000000UL, // 10^48
        0xF88A000000000000UL, 0x8EA3DA61E066EBB2UL, 0x00000006D79F8232UL, 0x0000000000000000UL, // 10^49
        0xB564000000000000UL, 0x926687D2C40534FDUL, 0x000000446C3B15F9UL, 0x0000000000000000UL, // 10^50
        0x15E8000000000000UL, 0xB8014E3BA83411E9UL, 0x000002AC3A4EDBBFUL, 0x0000000000000000UL, // 10^51
        0xDB10000000000000UL, 0x300D0E549208B31AUL, 0x00001ABA4714957DUL, 0x0000000000000000UL, // 10^52
        0x8EA0000000000000UL, 0xE0828F4DB456FF0CUL, 0x00010B46C6CDD6E3UL, 0x0000000000000000UL, // 10^53
        0x9240000000000000UL, 0xC51999090B65F67DUL, 0x000A70C3C40A64E6UL, 0x0000000000000000UL, // 10^54
        0xB680000000000000UL, 0xB2FFFA5A71FBA0E7UL, 0x006867A5A867F103UL, 0x0000000000000000UL, // 10^55
        0x2100000000000000UL, 0xFDFFC78873D4490DUL, 0x04140C78940F6A24UL, 0x0000000000000000UL, // 10^56
        0x4A00000000000000UL, 0xEBFDCB54864ADA83UL, 0x28C87CB5C89A2571UL, 0x0000000000000000UL, // 10^57
        0xE400000000000000UL, 0x37E9F14D3EEC8920UL, 0x97D4DF19D6057673UL, 0x0000000000000001UL, // 10^58
        0xE800000000000000UL, 0x2F236D04753D5B48UL, 0xEE50B7025C36A080UL, 0x000000000000000FUL, // 10^59
        0x1000000000000000UL, 0xD762422C946590D9UL, 0x4F2726179A224501UL, 0x000000000000009FUL, // 10^60
        0xA000000000000000UL, 0x69D695BDCBF7A87AUL, 0x17877CEC0556B212UL, 0x0000000000000639UL, // 10^61
        0x4000000000000000UL, 0x2261D969F7AC94CAUL, 0xEB4AE1383562F4B8UL, 0x0000000000003E3AUL, // 10^62
        0x8000000000000000UL, 0x57D27E23ACBDCFE6UL, 0x30ECCC3215DD8F31UL, 0x0000000000026E4DUL, // 10^63
        0x0000000000000000UL, 0x6E38ED64BF6A1F01UL, 0xE93FF9F4DAA797EDUL, 0x0000000000184F03UL, // 10^64
        0x0000000000000000UL, 0x4E3945EF7A25360AUL, 0x1C7FC3908A8BEF46UL, 0x0000000000F31627UL, // 10^65
        0x0000000000000000UL, 0x0E3CBB5AC5741C64UL, 0x1CFDA3A5697758BFUL, 0x00000000097EDD87UL, // 10^66
        0x0000000000000000UL, 0x8E5F518BB6891BE8UL, 0x21E864761EA97776UL, 0x000000005EF4A747UL, // 10^67
        0x0000000000000000UL, 0x8FB92F75215B1710UL, 0x5313EC9D329EAAA1UL, 0x00000003B58E88C7UL, // 10^68
        0x0000000000000000UL, 0x9D3BDA934D8EE6A0UL, 0x3EC73E23FA32AA4FUL, 0x00000025179157C9UL, // 10^69
        0x0000000000000000UL, 0x245689C107950240UL, 0x73C86D67C5FAA71CUL, 0x00000172EBAD6DDCUL, // 10^70
        0x0000000000000000UL, 0x6B61618A4BD21680UL, 0x85D4460DBBCA8719UL, 0x00000E7D34C64A9CUL, // 10^71
        0x0000000000000000UL, 0x31CDCF66F634E100UL, 0x3A4ABC8955E946FEUL, 0x000090E40FBEEA1DUL, // 10^72
        0x0000000000000000UL, 0xF20A1A059E10CA00UL, 0x46EB5D5D5B1CC5EDUL, 0x0005A8E89D752524UL, // 10^73
        0x0000000000000000UL, 0x746504382CA7E400UL, 0xC531A5A58F1FBB4BUL, 0x003899162693736AUL, // 10^74
        0x0000000000000000UL, 0x8BF22A31BE8EE800UL, 0xB3F07877973D50F2UL, 0x0235FADD81C2822BUL, // 10^75
        0x0000000000000000UL, 0x7775A5F171951000UL, 0x0764B4ABE8652979UL, 0x161BCCA7119915B5UL, // 10^76
        0x0000000000000000UL, 0xAA987B6E6FD2A000UL, 0x49EF0EB713F39EBEUL, 0xDD15FE86AFFAD912UL, // 10^77
    ];
}
