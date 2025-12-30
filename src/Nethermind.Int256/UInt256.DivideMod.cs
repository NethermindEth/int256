// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

#pragma warning disable SYSLIB5004 // DivRem is [Experimental] as of net10

using System;
using System.Diagnostics;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.Arm;
using System.Runtime.Intrinsics.X86;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    /// <summary>
    /// Sets <paramref name="res"/> to the integer quotient of <paramref name="x"/> divided by <paramref name="y"/>.
    /// </summary>
    /// <remarks>
    /// This performs an unsigned integer division with truncation toward zero (floor for unsigned values).
    /// <para>
    /// Special cases:
    /// <list type="bullet">
    ///   <item><description>If <paramref name="y"/> is zero, <paramref name="res"/> is set to zero.</description></item>
    ///   <item><description>If <paramref name="x"/> is less than <paramref name="y"/>, <paramref name="res"/> is set to zero.</description></item>
    ///   <item><description>If <paramref name="x"/> equals <paramref name="y"/>, <paramref name="res"/> is set to one.</description></item>
    /// </list>
    /// </para>
    /// <para>
    /// This method does not throw on divide-by-zero. If a <see cref="DivideByZeroException"/> (or equivalent)
    /// is required, it must be enforced by the caller before invoking this method.
    /// </para>
    /// </remarks>
    /// <param name="x">The dividend.</param>
    /// <param name="y">The divisor.</param>
    /// <param name="res">On return, contains the quotient <c>x / y</c>.</param>
    [SkipLocalsInit]
    public static void Divide(in UInt256 x, in UInt256 y, out UInt256 res)
    {
        // Handle y == 0 and y == 1 cheaply
        //
        // y0 is the low limb.
        // We structure this to keep y1/y2/y3 lifetimes short - do not load them unless y0 is 0 or 1.
        //
        // (y0 & ~1) == 0 is equivalent to (y0 == 0 || y0 == 1) but compiles well and keeps the branch compact.
        ulong y0 = y.u0;
        if ((y0 & ~1UL) == 0)
        {
            // yHi is the OR of the upper limbs.
            // - y == 0  iff y0 == 0 and yHi == 0
            // - y == 1  iff y0 == 1 and yHi == 0
            //
            // Computing yHi here (and only here) avoids keeping y1/y2/y3 live across the entire function,
            // which would force the JIT to use callee-saved regs (rbx/rsi/rdi/rbp/r14/r15) and emit pushes.
            ulong yHi = y.u1 | y.u2 | y.u3;
            if (yHi == 0)
            {
                // Exact: if y == 0 -> quotient is 0 (we return default)
                //        if y == 1 -> quotient is x (copy x)
                //
                // Note: written as a conditional expression for brevity.
                res = (y0 == 0) ? default : x;
                return;
            }
            // else y is 2^64 or larger - not a special-case, continue.
        }

        // Decide "u64 fast path" vs "wide path" with minimal register pressure
        //
        // Key idea: do not read x1 unless we already know x3|x2 == 0.
        // If we pull x1/x2/x3 all live at once and then also pull y2/y3 for the wide compare, we run out of
        // volatile regs (Windows x64 has rcx/rdx/r8 pinned for args; leaves rax/r9/r10/r11 as the main free ones).
        // That is exactly how you get extra pushes.
        ulong x3 = x.u3;
        ulong x2 = x.u2;

        // x fits in 64 bits iff x1==x2==x3==0.
        // We stage it:
        // - first check x3|x2 (cheap and already needed for wide compare)
        // - only then touch x1, so x1 does not become live on the wide path.
        if ((x3 | x2) == 0 && x.u1 == 0)
        {
            // u64 path
            //
            // Here x < 2^64. If y has any high limbs set, then y >= 2^64 > x, so quotient is 0.
            // This avoids any 256-bit division work and avoids the "unsafe" x.u0/y.u0 divide when y doesn't fit.
            if ((y.u1 | y.u2 | y.u3) != 0)
            {
                res = default;
                return;
            }

            // Now both x and y fit in 64 bits, and y != 0 (we already handled y==0 earlier).
            ulong x0 = x.u0;
            ulong yy0 = y.u0; // reload y0 in this scope so we do not keep the earlier y0 live unnecessarily

            // If y > x then quotient is 0.
            if (yy0 > x0) { res = default; return; }

            // If x == y then quotient is 1.
            if (yy0 == x0) { res = Create(1, 0, 0, 0); return; }

            // Normal 64-bit division.
            res = Create(x0 / yy0, 0, 0, 0);
            return;
        }

        // Wide compare gate - decide between {0, 1} and "real division"
        //
        // We only call DivideFull when x > y.
        // When x < y, quotient is 0.
        // When x == y, quotient is 1.
        //
        // Implemented as lexicographic compare from MS limb to LS limb:
        // (x3,x2,x1,x0) vs (y3,y2,y1,y0).
        //
        // Staged preloads:
        // - stage A loads y3 and y2 only (paired with x3/x2 already loaded)
        // - stage B loads x1/y1 and x0/y0 only if stage A says they are equal
        //
        // This keeps at most ~4 scalar values live at any time, helping the JIT stay in volatile regs and
        // avoid callee-saved spills - while still giving the CPU some independent loads to overlap.
        ulong y3 = y.u3;
        if (x3 < y3) { res = default; return; }                 // x < y
        if (x3 > y3) { DivideFull(in x, in y, out res); return; } // x > y -> real division

        ulong y2 = y.u2;
        if (x2 < y2) { res = default; return; }                 // x < y
        if (x2 > y2) { DivideFull(in x, in y, out res); return; } // x > y -> real division

        // Stage B (only reached when x3==y3 and x2==y2)
        ulong x1 = x.u1;
        ulong y1 = y.u1;
        if (x1 < y1) { res = default; return; }                 // x < y
        if (x1 > y1) { DivideFull(in x, in y, out res); return; } // x > y -> real division

        ulong x0b = x.u0;
        ulong y0b = y.u0;
        if (x0b < y0b) { res = default; return; }               // x < y
        if (x0b == y0b) { res = Create(1, 0, 0, 0); return; }   // x == y -> quotient 1

        // Remaining case: x > y.
        DivideFull(in x, in y, out res);
    }

    [SkipLocalsInit]
    // Slow path is isolated so the wrapper can tailcall it and avoid stack temps like "out _ remainder".
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void DivideFull(in UInt256 x, in UInt256 y, out UInt256 res)
    {
        // Full 256-bit division. We discard the remainder via out _.
        // Keeping this in a separate method prevents the wrapper from needing
        // a 32-byte stack slot for the remainder, which would otherwise force
        // a larger frame and extra stores even on fast exits.
        DivideImpl(x, y, out res, out _);
    }

    /// <summary>
    /// Divides this value by <paramref name="a"/> and returns the integer quotient.
    /// </summary>
    /// <remarks>
    /// Sets <paramref name="res"/> to <c>this / a</c> using unsigned integer division.
    /// If <paramref name="a"/> is zero, the result depends on the semantics of the underlying static
    /// <see cref="Divide(in UInt256, in UInt256, out UInt256)"/> implementation.
    /// If a <see cref="System.DivideByZeroException"/> is required for a zero divisor, the caller must pre-check
    /// <paramref name="a"/> and throw before calling this method.
    /// </remarks>
    /// <param name="a">The divisor.</param>
    /// <param name="res">On return, contains the quotient <c>this / a</c>.</param>
    public void Divide(in UInt256 a, out UInt256 res) => Divide(this, a, out res);

    

    /// <summary>
    /// Computes the modular sum of two 256-bit unsigned integers.
    /// </summary>
    /// <remarks>
    /// Sets <paramref name="res"/> to <c>(x + y) mod m</c>.
    /// <para>
    /// <strong>Warning:</strong> if <paramref name="m"/> is zero, <paramref name="res"/> is set to zero and
    /// no <see cref="System.DivideByZeroException"/> (or any other exception) is thrown. This behaviour
    /// intentionally differs from <see cref="System.Numerics.BigInteger"/>-style APIs and from standard
    /// modulo semantics, and can mask bugs in calling code that accidentally passes a zero modulus.
    /// Callers that require an exception for a zero modulus must validate <paramref name="m"/> and throw
    /// (for example, <see cref="System.DivideByZeroException"/>) before calling this method.
    /// </para>
    /// <para>Example (zero modulus):</para>
    /// <code>
    /// UInt256 x = 10;
    /// UInt256 y = 20;
    /// UInt256 m = UInt256.Zero;
    /// UInt256 res;
    ///
    /// // res will be 0 here; no exception is thrown:
    /// UInt256.AddMod(in x, in y, in m, out res);
    /// </code>
    /// </remarks>
    /// <param name="x">The first 256-bit addend.</param>
    /// <param name="y">The second 256-bit addend.</param>
    /// <param name="m">The modulus. If zero, the result is defined to be zero and no exception is thrown.</param>
    /// <param name="res">On return, contains the value of <c>(x + y) mod m</c>, or zero when <paramref name="m"/> is zero.</param>
    [SkipLocalsInit]
    public static void AddMod(in UInt256 x, in UInt256 y, in UInt256 m, out UInt256 res)
    {
        if (m.IsZero || m.IsOne)
        {
            // Any value mod 0 is defined here to be 0, and any value mod 1 is mathematically 0.
            res = default;
            return;
        }

        // Compute 257-bit sum S = x + y as 5 limbs (s0..s3, s4=carry)
        bool overflow = AddOverflow(in x, in y, out UInt256 sum);
        ulong s4 = !overflow ? 0UL : 1UL;

        if (m.IsUint64)
        {
            if (X86Base.X64.IsSupported)
            {
                Remainder257By64BitsX86Base(in sum, s4, m.u0, out res);
            }
            else
            {
                Remainder257By64Bits(in sum, s4, m.u0, out res);
            }
        }
        else if (LessThanBoth(in x, in y, in m))
        {
            // Fast path: if x < m and y < m then S < 2m, so one subtract is enough (carry-aware).
            // (Branchy compare is fine - the fallback is much more expensive anyway.)
            ReduceSumAssumingLT2m(in sum, s4, in m, out res);
        }
        else if (!overflow)
        {
            // No overflow - sum is the exact x+y, so normal mod is correct.
            Mod(in sum, in m, out res);
        }
        else if (m.u3 != 0)
        {
            Remainder257By256Bits(in sum, in m, out res);
        }
        else if (m.u2 != 0)
        {
            Remainder257By192Bits(in sum, in m, out res);
        }
        else
        {
            Remainder257By128Bits(in sum, in m, out res);
        }
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void ReduceSumAssumingLT2m(in UInt256 sum, ulong carry, in UInt256 m, out UInt256 res)
    {
        // Fast reduction when S < 2m (eg x<m,y<m).
        // Uses carry-aware single subtract.

        // diff = sum - m
        ulong borrow = !SubtractUnderflow(in sum, in m, out UInt256 d) ? 0UL : 1UL;

        // Need subtract if (carry == 1) || (sum >= m)
        // sum >= m <=> borrow == 0
        ulong needSub = carry | (borrow ^ 1UL);
        ulong mask = 0UL - needSub;

        if (mask == 0)
        {
            res = sum;
        }
        else if (mask == ulong.MaxValue)
        {
            res = d;
        }
        else if (Vector256.IsHardwareAccelerated)
        {
            Vector256<ulong> dV = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in d));
            Vector256<ulong> sumV = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in sum));
            Vector256<ulong> maskV = Vector256.Create(mask);

            Vector256<ulong> resultV = Vector256.ConditionalSelect(dV, sumV, maskV);

            Unsafe.SkipInit(out res);
            Unsafe.As<UInt256, Vector256<ulong>>(ref res) = resultV;
        }
        else
        {
            UInt256 mask256 = Create(mask, mask, mask, mask);
            res = (d & mask256) | (sum & ~mask256);
        }
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void Remainder257By64Bits(in UInt256 a, ulong a4, ulong d, out UInt256 rem)
    {
        // Remainder of 5-limb value by 64-bit modulus.
        // Computes ((a4..a0 base 2^64) % d).
        Debug.Assert(d != 0);
        Debug.Assert(a4 <= 1);

        int s = BitOperations.LeadingZeroCount(d);
        ulong dn = (s != 0) ? (d << s) : d;       // normalised (msb set) if s>0
        ulong recip = Reciprocal2By1(dn);

        // Normalise dividend (we treat it as 6 limbs with top limb 0)
        ulong u0, u1, u2, u3, u4, u5;
        if (s == 0)
        {
            u0 = a.u0;
            u1 = a.u1;
            u2 = a.u2;
            u3 = a.u3;
            u4 = a4;
            u5 = 0;
        }
        else
        {
            int rs = 64 - s;
            u0 = a.u0 << s;
            u1 = (a.u1 << s) | (a.u0 >> rs);
            u2 = (a.u2 << s) | (a.u1 >> rs);
            u3 = (a.u3 << s) | (a.u2 >> rs);
            u4 = (a4 << s) | (a.u3 >> rs);
            u5 = (a4 >> rs); // top limb (a5=0)
        }

        // Horner-like remainder using exact 2-by-1 divisions:
        // r = (((((u5*b + u4)*b + u3)*b + u2)*b + u1)*b + u0) % dn
        ulong r = 0;
        _ = UDivRem2By1(r, recip, dn, u5, out r);
        _ = UDivRem2By1(r, recip, dn, u4, out r);
        _ = UDivRem2By1(r, recip, dn, u3, out r);
        _ = UDivRem2By1(r, recip, dn, u2, out r);
        _ = UDivRem2By1(r, recip, dn, u1, out r);
        _ = UDivRem2By1(r, recip, dn, u0, out r);

        rem = default;
        Unsafe.AsRef(in rem.u0) = (s == 0) ? r : (r >> s);
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void Remainder257By64BitsX86Base(in UInt256 a, ulong a4, ulong d, out UInt256 rem)
    {
        Debug.Assert(d != 0);
        Debug.Assert(a4 <= 1);
        // Pull limbs up-front to encourage register residency and avoid repeated loads.
        // (Does not change semantics - just helps the JIT and OoO core.)
        ulong u0 = a.u0;
        ulong u1 = a.u1;
        ulong u2 = a.u2;
        ulong u3 = a.u3;

        // Treat the top as a single 128-bit chunk (a4:u3) and take its remainder in ONE DivRem.
        // This is valid as long as a4 < d. For a carry limb (0/1) and d>1, that's guaranteed.
        ulong r = X86Base.X64.DivRem(u3, a4, d).Remainder;
        r = X86Base.X64.DivRem(u2, r, d).Remainder;
        r = X86Base.X64.DivRem(u1, r, d).Remainder;
        r = X86Base.X64.DivRem(u0, r, d).Remainder;

        rem = default;
        Unsafe.AsRef(in rem.u0) = r;
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void Remainder257By128Bits(in UInt256 dividendLo256, in UInt256 mod128, out UInt256 remainder)
    {
        // (257-bit sum) % mod, where dividend is 5 limbs (implicit top limb) and mod is 2 limbs (<= 128-bit)
        // We run Knuth D (base 2^64) specialised to a 2-limb divisor, using a 3-limb rolling window.
        // Dividend is treated as n[0..5] with n5 == 0 (extra top limb), and here n4 == 1 from the 257th bit.
        // Result is a 2-limb remainder in remainder.u0..remainder.u1
        const ulong topLimb = 1;
        Debug.Assert(mod128.u3 == 0 && mod128.u2 == 0 && mod128.u1 != 0);

        // D1 - Normalise divisor: shift so vHi has its MSB set.
        // mod128 is 128-bit: v = (vHi:vLo). normShift in [0..63].
        ulong vLo = mod128.u0;
        ulong vHi = mod128.u1;
        int normShift = BitOperations.LeadingZeroCount(vHi);

        if (normShift > 0)
        {
            int invShift = 64 - normShift;
            vHi = (vHi << normShift) | (vLo >> invShift);
            vLo <<= normShift;
        }

        // Precompute reciprocal for 2-by-1 division when we do not have fast hardware div.
        ulong recipVHi = X86Base.X64.IsSupported ? 0UL : Reciprocal2By1(vHi);

        // D1 - Normalise dividend into 5 limbs n0..n4, plus implicit n5 == 0.
        // n4 is the top (257th) limb and is always 1 before normalisation.
        ulong n0, n1, n2, n3, n4;
        if (normShift == 0)
        {
            n0 = dividendLo256.u0;
            n1 = dividendLo256.u1;
            n2 = dividendLo256.u2;
            n3 = dividendLo256.u3;
            n4 = topLimb; // top limb
        }
        else
        {
            UInt256 shifted = ShiftLeftSmall(in dividendLo256, normShift);
            n0 = shifted.u0;
            n1 = shifted.u1;
            n2 = shifted.u2;
            n3 = shifted.u3;

            // n4 = (topLimb:dividendLo256.u3) << normShift, but topLimb == 1 so we fold
            // the carry from dividendLo256.u3
            n4 = (topLimb << normShift) | (dividendLo256.u3 >> (64 - normShift));
        }

        // Top-step shortcut: only possible quotient from the topmost pair (n4:n3) is q3 in {0,1}.
        // For normShift <= 62, n4 < 2^63 <= vHi, so (n4:n3) < (vHi:vLo) => q3 == 0.
        // Only when normShift == 63 can q3 be 1; if so, subtract v once to pre-reduce.
        if (normShift == 63 && (n4 > vHi || (n4 == vHi && n3 >= vLo)))
        {
            ulong t = n3 - vLo;
            ulong b = (n3 < vLo) ? 1UL : 0UL;
            n3 = t;
            n4 = n4 - vHi - b;
        }

        // D2-D7 over remaining positions digit = 2..0.
        // Rolling window invariant: we divide the 3-limb chunk (n4:n3:n2) by 2-limb v.
        // After each step we slide down one limb: (n4,n3,n2,n1,n0) <- (n3,n2,n1,n0,discard).
        int digit = 2;
        while (true)
        {
            // D3 - Estimate qhat from (n4:n3) / vHi, with rhat remainder of that 2-by-1 divide.
            // Special-case n4 == vHi to avoid overflow and match Knuth's qhat = base-1 path.
            // rhatCarry tracks rhat overflow when we do rhat = n3 + vHi in that special-case.
            ulong qhat, rhat;
            bool rhatCarry;

            if (n4 == vHi)
            {
                qhat = ulong.MaxValue;
                rhat = n3 + vHi;
                rhatCarry = rhat < n3;
            }
            else
            {
                if (X86Base.X64.IsSupported)
                {
                    (qhat, rhat) = X86Base.X64.DivRem(n3, n4, vHi); // (n4:n3) / vHi
                }
                else
                {
                    qhat = UDivRem2By1(n4, recipVHi, vHi, n3, out rhat);
                }

                rhatCarry = false;
            }

            // qv0 = qhat * vLo (128-bit)
            ulong qv0Hi = Multiply64(qhat, vLo, out ulong qv0Lo);

            // D3 correction: ensure qhat is not too large.
            // Compare (qv0Hi:qv0Lo) vs (rhat:n2). If too big, decrement qhat and adjust rhat.
            // At most two corrections are needed.
            if (!rhatCarry && (qv0Hi > rhat || (qv0Hi == rhat && qv0Lo > n2)))
            {
                qhat--;

                // (qv0Hi:qv0Lo) -= vLo
                qv0Hi -= (qv0Lo < vLo) ? 1UL : 0UL;
                qv0Lo -= vLo;

                ulong sum = rhat + vHi;
                rhatCarry = sum < rhat;
                rhat = sum;

                if (!rhatCarry && (qv0Hi > rhat || (qv0Hi == rhat && qv0Lo > n2)))
                {
                    qhat--;

                    qv0Hi -= (qv0Lo < vLo) ? 1UL : 0UL;
                    qv0Lo -= vLo;
                }
            }

            // D4 - Subtract qhat * v from the 3-limb chunk (n4:n3:n2).
            // We compute:
            //   (n2,n3,n4) -= qhat*(vLo,vHi) with full carry/borrow propagation.
            // Keep n2,n3 as the updated chunk for next iteration/slide (n4 is discarded after this digit).
            ulong borrowLo = (n2 < qv0Lo) ? 1UL : 0UL;
            n2 -= qv0Lo;

            ulong qv1Hi = Multiply64(qhat, vHi, out ulong qv1Lo);

            // Combine cross terms: q * vLo contributes qv0Hi into the next limb.
            ulong midLo = qv1Lo + qv0Hi;
            ulong midHi = qv1Hi + ((midLo < qv1Lo) ? 1UL : 0UL);

            ulong tmpN3 = n3 - midLo;
            ulong borrowMid = (n3 < midLo) ? 1UL : 0UL;
            n3 = tmpN3 - borrowLo;
            ulong borrowOut = borrowMid | ((tmpN3 < borrowLo) ? 1UL : 0UL);

            // Top limb (n4) only used to detect underflow; it is discarded after this digit.
            ulong tmpN4 = n4 - midHi;
            ulong borrowHi = (n4 < midHi) ? 1UL : 0UL;
            borrowOut = borrowHi | ((tmpN4 < borrowOut) ? 1UL : 0UL);

            // D6 - If subtraction underflowed, add v back once (and implicitly qhat--, but we only need the remainder).
            // Add-back is only on the lower 2 limbs of the chunk (n3:n2) since v is 2 limbs.
            if (borrowOut != 0)
            {
                ulong s0 = n2 + vLo;
                ulong c0 = (s0 < n2) ? 1UL : 0UL;

                ulong s1 = n3 + vHi;
                n3 = s1 + c0;
                n2 = s0;
            }

            if (digit == 0)
                break;

            // Slide window down by one limb for next quotient digit.
            n4 = n3;
            n3 = n2;
            n2 = n1;
            n1 = n0;

            digit--;
        }

        // D8 - De-normalise remainder: undo the initial left shift.
        // The remainder is in (n3:n2) in normalised space; shift right by normShift to restore.
        ulong remLo = n2;
        ulong remHi = n3;

        if (normShift != 0)
        {
            int invShift = 64 - normShift;
            remLo = (remLo >> normShift) | (remHi << invShift);
            remHi >>= normShift;
        }

        remainder = Create(remLo, remHi, 0, 0);
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void Remainder257By192Bits(in UInt256 valueLo256, in UInt256 modulus192, out UInt256 remainder)
    {
        // Computes: ( (1 << 256) + valueLo256 ) % modulus192
        // - Dividend is 257-bit: 4 explicit limbs plus an implicit top limb == 1.
        // - Modulus is 192-bit: 3 limbs (mod2:mod1:mod0), with mod2 != 0 and mod3 == 0.
        // Uses Knuth D in base 2^64, specialised to a 3-limb divisor.
        // We operate on a 5-limb dividend window (u0..u4); the implicit u5 is provably 0 here.
        const ulong implicitTopLimb = 1;
        Debug.Assert(modulus192.u3 == 0 && modulus192.u2 != 0);

        // D1 - Normalise modulus so its top limb has the MSB set.
        ulong modTop = modulus192.u2;
        int normShiftBits = BitOperations.LeadingZeroCount(modTop);

        UInt256 normMod = ShiftLeftSmall(in modulus192, normShiftBits);
        ulong mod0 = normMod.u0;
        ulong mod1 = normMod.u1;
        ulong mod2 = normMod.u2;

        ulong recipMod2 = X86Base.X64.IsSupported ? 0UL : Reciprocal2By1(mod2);

        // D1 - Normalise the 257-bit dividend into limbs u0..u4 (u5 is implicitly 0).
        // Using explicit shifts avoids building a full UInt256 temporary on the hot path.
        ulong u0, u1, u2, u3, u4;
        if (normShiftBits == 0)
        {
            u0 = valueLo256.u0;
            u1 = valueLo256.u1;
            u2 = valueLo256.u2;
            u3 = valueLo256.u3;
            u4 = implicitTopLimb;
        }
        else
        {
            int inv = 64 - normShiftBits;
            u0 = valueLo256.u0 << normShiftBits;
            u1 = (valueLo256.u1 << normShiftBits) | (valueLo256.u0 >> inv);
            u2 = (valueLo256.u2 << normShiftBits) | (valueLo256.u1 >> inv);
            u3 = (valueLo256.u3 << normShiftBits) | (valueLo256.u2 >> inv);
            u4 = (implicitTopLimb << normShiftBits) | (valueLo256.u3 >> inv);
            // u5 would be (implicitTopLimb >> inv) which is always 0 for inv in 1..63.
        }

        // j = 2 (top digit) specialisation:
        // With u5 == 0 and mod2 normalised, the top quotient digit is in {0,1}.
        // Compute it exactly by comparing (u4:u3:u2) against (mod2:mod1:mod0).
        if (u4 > mod2 || (u4 == mod2 && (u3 > mod1 || (u3 == mod1 && u2 >= mod0))))
        {
            ulong borrow = 0;
            u2 = Sub(u2, mod0, ref borrow);
            u3 = Sub(u3, mod1, ref borrow);
            u4 = Sub(u4, mod2, ref borrow);
            Debug.Assert(borrow == 0);
        }

        // j = 1
        {
            // Estimate q from (u4:u3) / mod2, tracking r (the remainder of that divide).
            ulong qEst, rEst;
            ulong rCarry;

            if (u4 == mod2)
            {
                qEst = ulong.MaxValue;
                ulong sum = u3 + mod2;
                rCarry = (sum < u3) ? 1UL : 0UL;
                rEst = sum;
            }
            else
            {
                if (X86Base.X64.IsSupported)
                {
                    (qEst, rEst) = X86Base.X64.DivRem(u3, u4, mod2);
                }
                else
                {
                    qEst = UDivRem2By1(u4, recipMod2, mod2, u3, out rEst);
                }
                rCarry = 0;
            }

            // Precompute q*mod1 once - used in correction and in the mul-sub.
            ulong qMod1Hi = Multiply64(qEst, mod1, out ulong qMod1Lo);

            // Knuth correction: compare (q*mod1) against (r:u2). At most two decrements.
            if (rCarry == 0 && (qMod1Hi > rEst || (qMod1Hi == rEst && qMod1Lo > u2)))
            {
                qEst--;

                // (q*mod1) -= mod1 (128-bit)
                ulong t = qMod1Lo - mod1;
                qMod1Hi -= (t > qMod1Lo) ? 1UL : 0UL;
                qMod1Lo = t;

                ulong sum = rEst + mod2;
                rCarry = (sum < rEst) ? 1UL : 0UL;
                rEst = sum;
            }

            if (rCarry == 0 && (qMod1Hi > rEst || (qMod1Hi == rEst && qMod1Lo > u2)))
            {
                qEst--;

                ulong t = qMod1Lo - mod1;
                qMod1Hi -= (t > qMod1Lo) ? 1UL : 0UL;
                qMod1Lo = t;
                // rEst not needed after this point for j=1.
            }

            // Mul-sub q*mod from the 4-limb window u1..u4 (producing updated u1..u4).
            ulong borrow = 0;

            ulong qMod0Hi = Multiply64(qEst, mod0, out ulong qMod0Lo);
            u1 = Sub(u1, qMod0Lo, ref borrow);
            ulong carry = qMod0Hi;

            ulong sum1 = qMod1Lo + carry;
            ulong c1 = (sum1 < qMod1Lo) ? 1UL : 0UL;
            carry = qMod1Hi + c1;
            u2 = Sub(u2, sum1, ref borrow);

            ulong qMod2Hi = Multiply64(qEst, mod2, out ulong qMod2Lo);
            ulong sum2 = qMod2Lo + carry;
            ulong c2 = (sum2 < qMod2Lo) ? 1UL : 0UL;
            carry = qMod2Hi + c2;
            u3 = Sub(u3, sum2, ref borrow);

            u4 = Sub(u4, carry, ref borrow);

            if (borrow != 0)
            {
                AddBack3(ref u1, ref u2, ref u3, ref u4, mod0, mod1, mod2);
            }
        }

        // j = 0
        {
            // Estimate q from (u3:u2) / mod2.
            ulong qEst, rEst;
            ulong rCarry;

            if (u3 == mod2)
            {
                qEst = ulong.MaxValue;
                ulong sum = u2 + mod2;
                rCarry = (sum < u2) ? 1UL : 0UL;
                rEst = sum;
            }
            else
            {
                if (X86Base.X64.IsSupported)
                {
                    (qEst, rEst) = X86Base.X64.DivRem(u2, u3, mod2);
                }
                else
                {
                    qEst = UDivRem2By1(u3, recipMod2, mod2, u2, out rEst);
                }
                rCarry = 0;
            }

            // q*mod1 once (correction + mul-sub)
            ulong qMod1Hi = Multiply64(qEst, mod1, out ulong qMod1Lo);

            if (rCarry == 0 && (qMod1Hi > rEst || (qMod1Hi == rEst && qMod1Lo > u1)))
            {
                qEst--;

                ulong t = qMod1Lo - mod1;
                qMod1Hi -= (t > qMod1Lo) ? 1UL : 0UL;
                qMod1Lo = t;

                ulong sum = rEst + mod2;
                rCarry = (sum < rEst) ? 1UL : 0UL;
                rEst = sum;
            }

            if (rCarry == 0 && (qMod1Hi > rEst || (qMod1Hi == rEst && qMod1Lo > u1)))
            {
                qEst--;

                ulong t = qMod1Lo - mod1;
                qMod1Hi -= (t > qMod1Lo) ? 1UL : 0UL;
                qMod1Lo = t;
            }

            // Mul-sub q*mod from the 4-limb window u0..u3. Final remainder ends up in u0..u2.
            ulong borrow = 0;

            ulong qMod0Hi = Multiply64(qEst, mod0, out ulong qMod0Lo);
            u0 = Sub(u0, qMod0Lo, ref borrow);
            ulong carry = qMod0Hi;

            ulong sum1 = qMod1Lo + carry;
            ulong c1 = (sum1 < qMod1Lo) ? 1UL : 0UL;
            carry = qMod1Hi + c1;
            u1 = Sub(u1, sum1, ref borrow);

            ulong qMod2Hi = Multiply64(qEst, mod2, out ulong qMod2Lo);
            ulong sum2 = qMod2Lo + carry;
            ulong c2 = (sum2 < qMod2Lo) ? 1UL : 0UL;
            carry = qMod2Hi + c2;
            u2 = Sub(u2, sum2, ref borrow);

            u3 = Sub(u3, carry, ref borrow);

            if (borrow != 0)
            {
                AddBack3(ref u0, ref u1, ref u2, ref u3, mod0, mod1, mod2);
            }
        }

        // D8 - De-normalise remainder.
        if (normShiftBits == 0)
        {
            remainder = Create(u0, u1, u2, 0);
            return;
        }

        {
            int inv = 64 - normShiftBits;
            ulong r0 = (u0 >> normShiftBits) | (u1 << inv);
            ulong r1 = (u1 >> normShiftBits) | (u2 << inv);
            ulong r2 = (u2 >> normShiftBits);
            remainder = Create(r0, r1, r2, 0);
        }
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void Remainder257By256Bits(in UInt256 valueLo256, in UInt256 modulus256, out UInt256 remainder)
    {
        // Computes: ( (1 << 256) + valueLo256 ) % modulus256
        // - Dividend is 257-bit: 4 explicit limbs plus an implicit top limb == 1.
        // - Modulus is up to 256-bit (4 limbs), and must have a non-zero top limb.
        // Uses Knuth D in base 2^64, specialised to a 4-limb divisor, with the top dividend limb u5 == 0.
        const ulong implicitTopLimb = 1;
        Debug.Assert(modulus256.u3 != 0);

        // D1 - Normalise modulus so its high limb has the top bit set.
        int normShiftBits = BitOperations.LeadingZeroCount(modulus256.u3);
        UInt256 normMod = ShiftLeftSmall(in modulus256, normShiftBits);
        UInt256 normValue = ShiftLeftSmall(in valueLo256, normShiftBits);

        ulong mod3 = normMod.u3;
        ulong recipMod3 = X86Base.X64.IsSupported ? 0UL : Reciprocal2By1(mod3);

        // D1 - Normalise the 257-bit dividend into limbs u0..u4 (u5 is implicitly 0).
        ulong u0 = normValue.u0;
        ulong u1 = normValue.u1;
        ulong u2 = normValue.u2;
        ulong u3 = normValue.u3;
        ulong u4 = (normShiftBits == 0)
            ? implicitTopLimb
            : (implicitTopLimb << normShiftBits) | (valueLo256.u3 >> (64 - normShiftBits));

        ulong mod0 = normMod.u0;
        ulong mod1 = normMod.u1;
        ulong mod2 = normMod.u2;

        // High quotient digit (from the top limb) can only be 0 or 1 because:
        // - u5 == 0 for a 257-bit dividend
        // - mod3 has its MSB set after normalisation
        // So we implement "qHigh = 1?" as a single attempted subtraction of the modulus.
        if (u4 >= mod3)
        {
            ulong borrow = 0;
            u1 = Sub(u1, mod0, ref borrow);
            u2 = Sub(u2, mod1, ref borrow);
            u3 = Sub(u3, mod2, ref borrow);
            u4 = Sub(u4, mod3, ref borrow);

            // If we borrowed past u4, we'd be borrowing from u5 (which is 0), so undo the subtraction.
            if (borrow != 0)
            {
                ulong carry = 0;
                AddWithCarry(u1, mod0, ref carry, out u1);
                AddWithCarry(u2, mod1, ref carry, out u2);
                AddWithCarry(u3, mod2, ref carry, out u3);
                AddWithCarry(u4, mod3, ref carry, out u4);
                // carry into u5 is ignored (u5 is outside the represented range)
            }
        }

        // Only one Knuth step remains (j = 0), estimating q0 from (u4:u3) / mod3.
        ulong q0, rHat;
        ulong rHatCarry;

        if (u4 == mod3)
        {
            q0 = ulong.MaxValue;
            ulong sum = u3 + mod3;
            rHatCarry = (sum < u3) ? 1UL : 0UL;
            rHat = sum;
        }
        else
        {
            if (X86Base.X64.IsSupported)
            {
                (q0, rHat) = X86Base.X64.DivRem(u3, u4, mod3); // (u4:u3) / mod3
            }
            else
            {
                q0 = UDivRem2By1(u4, recipMod3, mod3, u3, out rHat);
            }

            rHatCarry = 0;
        }

        // D3 correction: ensure q0 isn't too large by checking q0*mod2 against (rHat:u2).
        // Only do the second check if we decremented once.
        if (rHatCarry == 0)
        {
            ulong qMod2Hi = Multiply64(q0, mod2, out ulong qMod2Lo);

            if (qMod2Hi > rHat || (qMod2Hi == rHat && qMod2Lo > u2))
            {
                q0--;

                ulong sum = rHat + mod3;
                rHatCarry = (sum < rHat) ? 1UL : 0UL;
                rHat = sum;

                if (rHatCarry == 0)
                {
                    qMod2Hi = Multiply64(q0, mod2, out qMod2Lo);
                    if (qMod2Hi > rHat || (qMod2Hi == rHat && qMod2Lo > u2))
                        q0--;
                }
            }
        }

        // D4/D6 - Subtract q0 * modulus from the 5-limb window (u0..u4).
        // If it underflows, add modulus back once.
        ulong underflow = SubMul4(ref u0, ref u1, ref u2, ref u3, ref u4, mod0, mod1, mod2, mod3, q0);
        if (underflow != 0)
        {
            AddBack4(ref u0, ref u1, ref u2, ref u3, ref u4, mod0, mod1, mod2, mod3);
        }

        // D8 - De-normalise the remainder.
        UInt256 normRem = Create(u0, u1, u2, u3);
        remainder = ShiftRightSmall(in normRem, normShiftBits);
    }

    /// <summary>
    /// Computes the modular sum of this value and <paramref name="a"/>.
    /// </summary>
    /// <remarks>
    /// Sets <paramref name="res"/> to <c>(this + a) mod m</c>.
    /// If <paramref name="m"/> is zero, <paramref name="res"/> is set to zero.
    /// If a <see cref="System.DivideByZeroException"/> is required for a zero modulus, the caller must pre-check
    /// <paramref name="m"/> and throw before calling this method.
    /// </remarks>
    /// <param name="a">The other 256-bit addend.</param>
    /// <param name="m">The modulus. If zero, the result is defined to be zero.</param>
    /// <param name="res">On return, contains the value of <c>(this + a) mod m</c>, or zero when <paramref name="m"/> is zero.</param>
    public void AddMod(in UInt256 a, in UInt256 m, out UInt256 res) => AddMod(this, a, m, out res);

    /// <summary>
    /// Computes the remainder of dividing one <see cref="UInt256"/> value by another.
    /// </summary>
    /// <remarks>
    /// Sets <paramref name="res"/> to <c>x % y</c> when <paramref name="y"/> is non-zero.
    /// If <paramref name="y"/> is zero, <paramref name="res"/> is set to zero.
    /// This behaviour intentionally differs from <see cref="System.Numerics.BigInteger"/>-style APIs.
    /// If a <see cref="System.DivideByZeroException"/> is required for a zero divisor, the caller must pre-check
    /// <paramref name="y"/> and throw before calling this method.
    /// </remarks>
    /// <param name="x">The dividend.</param>
    /// <param name="y">The divisor. If zero, the result is defined to be zero.</param>
    /// <param name="res">On return, contains <c>x % y</c>, or zero when <paramref name="y"/> is zero.</param>
    [SkipLocalsInit]
    public static void Mod(in UInt256 x, in UInt256 y, out UInt256 res)
    {
        if (x.IsZero || y.IsZeroOrOne)
        {
            res = default;
            return;
        }

        switch (x.CompareTo(y))
        {
            case -1:
                res = x;
                return;
            case 0:
                res = default;
                return;
        }
        // At this point:
        // x != 0
        // y != 0
        // x > y

        if (x.IsUint64)
        {
            // If y > x it has already be handled by caller
            ulong quot = x.u0 / y.u0;
            ulong rem = x.u0 - (quot * y.u0);
            res = Create(rem, 0, 0, 0);
            return;
        }

        ModFull(x, y, out res);
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void ModFull(in UInt256 x, in UInt256 y, out UInt256 res)
    {
        DivideImpl(x, y, out _, out res);
    }

    /// <summary>
    /// Computes the remainder of dividing this value by <paramref name="m"/>.
    /// </summary>
    /// <remarks>
    /// Sets <paramref name="res"/> to <c>this % m</c> when <paramref name="m"/> is non-zero.
    /// If <paramref name="m"/> is zero, <paramref name="res"/> is set to zero.
    /// If a <see cref="System.DivideByZeroException"/> is required for a zero divisor, the caller must pre-check
    /// <paramref name="m"/> and throw before calling this method.
    /// </remarks>
    /// <param name="m">The divisor. If zero, the result is defined to be zero.</param>
    /// <param name="res">On return, contains <c>this % m</c>, or zero when <paramref name="m"/> is zero.</param>
    public void Mod(in UInt256 m, out UInt256 res) => Mod(this, m, out res);

    

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong Reciprocal2By1(ulong d)
    {
        // Precondition: d is normalised (bit 63 set).

        // For normalised d: (d >> 55) is in [256..511], so subtracting 256 yields [0..255].
        // This form stays identical for valid inputs, but is more obviously "byte range" to humans and JITs.
        int idx = (int)((d >> 55) - 256UL);

        ulong v0 = ReciprocalSeedTable[idx];

        ulong d40 = (d >> 24) + 1UL;

        // Keep the original algebra - all ops are modulo 2^64, so reassociation is safe.
        ulong v1 = (v0 << 11) - ((v0 * v0 * d40) >> 40) - 1UL;

        ulong v2 = (v1 << 13) + ((v1 * (0x1000_0000_0000_0000UL - v1 * d40)) >> 47);

        ulong d0 = d & 1UL;
        ulong d63 = (d >> 1) + d0;

        ulong e = ((v2 >> 1) & (0UL - d0)) - (v2 * d63);

        ulong v3 = (MulHigh(v2, e) >> 1) + (v2 << 31);

        // v4 = v3 - high(v3*d + d) - d
        ulong prodHi = Multiply64(v3, d, out ulong prodLo);

        prodHi += (prodLo > ~d) ? 1UL : 0UL;

        return v3 - prodHi - d;
    }

    // Preconditions:
    // - d normalised (msb set)
    // - u1 < d
    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong UDivRem2By1(ulong uh, ulong reciprocal, ulong d, ulong ul, out ulong rem)
    {
        ulong hi = Multiply64(reciprocal, uh, out ulong low);

        low += ul;
        ulong q = hi + uh + 1UL;
        if (low < ul)
        {
            q++;
        }

        ulong r1 = ul - (q * d);

        if (r1 > low) { q--; r1 += d; }
        if (r1 >= d) { q++; r1 -= d; }

        rem = r1;
        return q;
    }

    

    public static void ExpMod(in UInt256 b, in UInt256 e, in UInt256 m, out UInt256 result)
    {
        if (m.IsOne)
        {
            result = Zero;
            return;
        }
        UInt256 intermediate = One;
        UInt256 bs = b;
        int len = e.BitLen;
        for (int i = 0; i < len; i++)
        {
            if (e.Bit(i))
            {
                MultiplyMod(intermediate, bs, m, out intermediate);
            }
            MultiplyMod(bs, bs, m, out bs);
        }

        result = intermediate;
    }

    public void ExpMod(in UInt256 exp, in UInt256 m, out UInt256 res) => ExpMod(this, exp, m, out res);

    // MulMod calculates the modulo-m multiplication of x and y and
    // sets res to its result.
    [SkipLocalsInit]
    public static void MultiplyMod(in UInt256 x, in UInt256 y, in UInt256 m, out UInt256 res)
    {
        if (m.IsZero) ThrowDivideByZeroException();

        if (m.IsOne || x.IsZero || y.IsZero)
        {
            res = default;
            return;
        }

        // Trivial no-mul cases first.
        if (y.IsOne) { Mod(in x, in m, out res); return; }
        if (x.IsOne) { Mod(in y, in m, out res); return; }

        // Modulus-size dispatch first - keeps all the tiny-mod magic.
        if (m.IsUint64)
        {
            MulModBy64Bits(in x, in y, m.u0, out res);
            return;
        }

        if ((m.u2 | m.u3) == 0)
        {
            // Hybrid: if both operands are > 128-bit, avoid two 256->128 reductions.
            if (((x.u2 | x.u3) != 0) && ((y.u2 | y.u3) != 0))
            {
                Multiply256To512Bit(in x, in y, out UInt256 lo2, out UInt256 hi2);
                Remainder512By128Bits(in lo2, in hi2, in m, out res); // dLen will be 2
                return;
            }

            MulModBy128Bits(in x, in y, m.u0, m.u1, out res);
            return;
        }

        Multiply256To512Bit(in x, in y, out UInt256 lo, out UInt256 hi);

        if (hi.IsZero)
        {
            Mod(in lo, in m, out res);
            return;
        }

        Remainder512By256Bits(in lo, in hi, in m, out res);
    }

    [SkipLocalsInit]
    private static void MulModBy64Bits(in UInt256 x, in UInt256 y, ulong mod, out UInt256 res)
    {
        if (mod == 1) { res = default; return; }

        // Power-of-two.
        if ((mod & (mod - 1)) == 0)
        {
            ulong mask = mod - 1;
            ulong a = x.u0 & mask;
            ulong b = y.u0 & mask;
            ulong prodLo = unchecked(a * b);
            res = new UInt256(prodLo & mask, 0, 0, 0);
            return;
        }

        // Fast reduce x if it is already 64-bit.
        ulong xr;
        if ((x.u1 | x.u2 | x.u3) == 0)
        {
            ulong a = x.u0;
            xr = a < mod ? a : a % mod;
        }
        else
        {
            int shift = LeadingZeros(mod);
            ulong dn = mod << shift;
            ulong reciprocal = X86Base.X64.IsSupported ? 0 : Reciprocal2By1(dn);
            xr = X86Base.X64.IsSupported
                ? Remainder256By64BitsX86Base(in x, dn, shift)
                : Remainder256By64Bits(in x, dn, reciprocal, shift);
        }

        // If y == 1, we are done (return reduced x).
        if (y.IsOne)
        {
            res = new UInt256(xr, 0, 0, 0);
            return;
        }

        // Now reduce y similarly - but avoid recomputing shift/dn if we took the slow path.
        int sh = LeadingZeros(mod);
        ulong dnn = mod << sh;
        ulong rec = X86Base.X64.IsSupported ? 0 : Reciprocal2By1(dnn);

        ulong yr;
        if ((y.u1 | y.u2 | y.u3) == 0)
        {
            ulong b = y.u0;
            yr = b < mod ? b : b % mod;
        }
        else
        {
            yr = X86Base.X64.IsSupported
                ? Remainder256By64BitsX86Base(in y, dnn, sh)
                : Remainder256By64Bits(in y, dnn, rec, sh);
        }

        if (x.IsOne)
        {
            res = new UInt256(yr, 0, 0, 0);
            return;
        }

        ulong ph = Multiply64(xr, yr, out ulong pl);
        ulong r = X86Base.X64.IsSupported
            ? Remainder128By64BitsX86Base(ph, pl, dnn, sh)
            : Remainder128By64Bits(ph, pl, dnn, rec, sh);

        res = new UInt256(r, 0, 0, 0);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong Remainder256By64Bits(in UInt256 a, ulong dn, ulong reciprocal, int shift)
    {
        UInt256 un = ShiftLeftSmall(in a, shift);
        ulong r = shift == 0 ? 0 : a.u3 >> (64 - shift);

        _ = UDivRem2By1(r, reciprocal, dn, un.u3, out r);
        _ = UDivRem2By1(r, reciprocal, dn, un.u2, out r);
        _ = UDivRem2By1(r, reciprocal, dn, un.u1, out r);
        _ = UDivRem2By1(r, reciprocal, dn, un.u0, out r);

        // Denormalise remainder.
        return r >> shift;
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong Remainder256By64BitsX86Base(in UInt256 a, ulong dn, int shift)
    {
        UInt256 un = ShiftLeftSmall(in a, shift);
        ulong r = shift == 0 ? 0 : a.u3 >> (64 - shift);

        (_, r) = X86Base.X64.DivRem(un.u3, r, dn);
        (_, r) = X86Base.X64.DivRem(un.u2, r, dn);
        (_, r) = X86Base.X64.DivRem(un.u1, r, dn);
        (_, r) = X86Base.X64.DivRem(un.u0, r, dn);

        // Denormalise remainder.
        return r >> shift;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong Remainder128By64Bits(ulong hi, ulong lo, ulong dn, ulong reciprocal, int shift)
    {
        if (shift == 0)
        {
            ulong r = 0;
            _ = UDivRem2By1(r, reciprocal, dn, hi, out r);
            _ = UDivRem2By1(r, reciprocal, dn, lo, out r);
            return r;
        }
        else
        {
            int rshift = 64 - shift; // 1..63

            ulong un2 = hi >> rshift;
            ulong un1 = (hi << shift) | (lo >> rshift);
            ulong un0 = lo << shift;

            ulong r = un2;
            _ = UDivRem2By1(r, reciprocal, dn, un1, out r);
            _ = UDivRem2By1(r, reciprocal, dn, un0, out r);

            return r >> shift;
        }
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong Remainder128By64BitsX86Base(ulong hi, ulong lo, ulong dn, int shift)
    {
        if (shift == 0)
        {
            ulong r = 0;
            (_, r) = X86Base.X64.DivRem(hi, r, dn);
            (_, r) = X86Base.X64.DivRem(lo, r, dn);
            return r;
        }
        else
        {
            int rshift = 64 - shift; // 1..63

            ulong un2 = hi >> rshift;
            ulong un1 = (hi << shift) | (lo >> rshift);
            ulong un0 = lo << shift;

            ulong r = un2;
            (_, r) = X86Base.X64.DivRem(un1, r, dn);
            (_, r) = X86Base.X64.DivRem(un0, r, dn);

            return r >> shift;
        }
    }

    [SkipLocalsInit]
    private static void MulModBy128Bits(in UInt256 x, in UInt256 y, ulong m0, ulong m1, out UInt256 res)
    {
        // m1 != 0 here.
        scoped ref readonly UInt256 q = ref Unsafe.NullRef<UInt256>();
        if (y.IsOne)
        {
            q = ref x;
        }
        else if (x.IsOne)
        {
            q = ref y;
        }

        ulong r0;
        ulong r1;
        if (Unsafe.IsNullRef(in q))
        {
            ulong u0 = x.u0, u1 = x.u1, u2 = x.u2, u3 = x.u3;
            Remainder256By128Bits(u0, u1, u2, u3, m0, m1, out ulong x0, out ulong x1);
            u0 = y.u0; u1 = y.u1; u2 = y.u2; u3 = y.u3;
            Remainder256By128Bits(u0, u1, u2, u3, m0, m1, out ulong y0, out ulong y1);

            Mul128(x0, x1, y0, y1, out ulong p0, out ulong p1, out ulong p2, out ulong p3);
            Remainder256By128Bits(p0, p1, p2, p3, m0, m1, out r0, out r1);
        }
        else
        {
            // Single side mod; as one operand is 1.
            ulong u0 = q.u0, u1 = q.u1, u2 = q.u2, u3 = q.u3;
            Remainder256By128Bits(u0, u1, u2, u3, m0, m1, out r0, out r1);
        }
        res = new UInt256(r0, r1, 0, 0);
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void Remainder256By128Bits(ulong u0, ulong u1, ulong u2, ulong u3, ulong d0, ulong d1, out ulong r0, out ulong r1)
    {
        // Early exits for small numerators
        if ((u2 | u3) == 0)
        {
            if (u1 == 0)
            { 
                r0 = u0;
                r1 = 0;
                return;
            }
            if (u1 < d1 || (u1 == d1 && u0 < d0))
            {
                r0 = u0;
                r1 = u1;
                return;
            }
        }

        int shift = LeadingZeros(d1);
        ulong nd0, nd1;
        ulong un0, un1, un2, un3, un4;

        if (shift == 0)
        {
            un0 = u0; un1 = u1; un2 = u2; un3 = u3; un4 = 0;
            nd0 = d0; nd1 = d1;
        }
        else
        {
            int rshift = 64 - shift;
            un4 = u3 >> rshift;
            un3 = (u3 << shift) | (u2 >> rshift);
            un2 = (u2 << shift) | (u1 >> rshift);
            un1 = (u1 << shift) | (u0 >> rshift);
            un0 = u0 << shift;
            nd0 = d0 << shift;
            nd1 = (d1 << shift) | (d0 >> rshift);
        }

        ulong reciprocal = X86Base.X64.IsSupported ? 0 : Reciprocal2By1(nd1);

        // Unroll by limb count - no dynamic indexing, no struct
        if (u3 != 0)
        {
            // 4-limb numerator: 3 Knuth steps (j = 2, 1, 0)
            KnuthStep(ref un2, ref un3, ref un4, nd0, nd1, reciprocal);
            KnuthStep(ref un1, ref un2, ref un3, nd0, nd1, reciprocal);
            KnuthStep(ref un0, ref un1, ref un2, nd0, nd1, reciprocal);
        }
        else if (u2 != 0)
        {
            // 3-limb numerator: 2 Knuth steps (j = 1, 0)
            KnuthStep(ref un1, ref un2, ref un3, nd0, nd1, reciprocal);
            KnuthStep(ref un0, ref un1, ref un2, nd0, nd1, reciprocal);
        }
        else
        {
            // 2-limb numerator: 1 Knuth step (j = 0)
            KnuthStep(ref un0, ref un1, ref un2, nd0, nd1, reciprocal);
        }

        // Denormalise
        if (shift == 0)
        {
            r0 = un0;
            r1 = un1;
        }
        else
        {
            int rshift = 64 - shift;
            r0 = (un0 >> shift) | (un1 << rshift);
            r1 = un1 >> shift;
        }
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void KnuthStep(ref ulong x0, ref ulong x1, ref ulong x2, ulong nd0, ulong nd1, ulong reciprocal)
    {
        ulong oldX2 = x2;
        ulong qhat = X86Base.X64.IsSupported 
            ? EstimateQhatEstX86Base(x2, x1, nd1) 
            : EstimateQhatEst(x2, x1, nd1, reciprocal);

        ulong borrow = SubMulTo2(ref x0, ref x1, nd0, nd1, qhat);
        x2 = oldX2 - borrow;

        if (oldX2 < borrow)
        {
            // Overshoot-by-1 fix (rare).
            CorrectStep(ref x0, ref x1, ref x2, nd0, nd1);
        }
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void CorrectStep(ref ulong x0, ref ulong x1, ref ulong x2, ulong nd0, ulong nd1)
    {
        x2 += AddTo2(ref x0, ref x1, nd0, nd1);
        if (x2 != 0)
        {
            // Overshoot-by-2 fix (very rare).
            x2 += AddTo2(ref x0, ref x1, nd0, nd1);
        }
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong EstimateQhatEst(ulong u2, ulong u1, ulong dh, ulong reciprocal)
    {
        // Quotient digit saturates at b - 1. No correction needed (rhat would be >= b).
        return u2 >= dh ? ulong.MaxValue : UDivRem2By1(u2, reciprocal, dh, u1, out _);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong EstimateQhatEstX86Base(ulong u2, ulong u1, ulong dh)
    {
        if (u2 >= dh)
        {
            // Quotient digit saturates at b - 1. No correction needed (rhat would be >= b).
            return ulong.MaxValue;
        }

        (ulong qhat, _) = X86Base.X64.DivRem(u1, u2, dh);
        return qhat;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void Mul128(ulong a0, ulong a1, ulong b0, ulong b1,
    out ulong p0, out ulong p1, out ulong p2, out ulong p3)
    {
        // Products:
        // a = a0 + a1*2^64
        // b = b0 + b1*2^64
        //
        // a*b = p0 + p1*2^64 + p2*2^128 + p3*2^192

        ulong hi00 = Multiply64(a0, b0, out p0);
        ulong hi01 = Multiply64(a0, b1, out ulong lo01);
        ulong hi10 = Multiply64(a1, b0, out ulong lo10);
        ulong hi11 = Multiply64(a1, b1, out ulong lo11);

        // p1 = hi00 + lo01 + lo10
        ulong s1 = hi00 + lo01;
        ulong c1 = s1 < hi00 ? 1UL : 0UL;     // carry from first add
        ulong t1 = s1 + lo10;
        c1 += t1 < s1 ? 1UL : 0UL;            // carry from second add (c1 is now 0..2)
        p1 = t1;

        // p2 = hi01 + hi10 + lo11 + c1
        ulong s2 = hi01 + hi10;
        ulong c2 = s2 < hi01 ? 1UL : 0UL;
        ulong t2 = s2 + lo11;
        c2 += t2 < s2 ? 1UL : 0UL;            // c2 is 0..2 so far

        ulong t3 = t2 + c1;                   // add c1 as a value (0..2)
        c2 += t3 < t2 ? 1UL : 0UL;            // at most +1 overflow here, c2 becomes 0..3
        p2 = t3;

        // p3 = hi11 + c2  (fits, since overall product is 256-bit)
        p3 = hi11 + c2;
    }
    
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong SubMulTo2(ref ulong x0, ref ulong x1, ulong y0, ulong y1, ulong mul)
    {
        // Subtract q*(y1:y0) from (x1:x0) and return the borrow to subtract from x2.
        // This is the standard "mul then subtract" for Knuth D, n=2.

        ulong hi0 = Multiply64(y0, mul, out ulong lo0);
        ulong hi1 = Multiply64(y1, mul, out ulong lo1);

        // x0 -= lo0
        ulong x00 = x0;
        ulong t0 = x00 - lo0;
        ulong b0 = x00 < lo0 ? 1UL : 0UL;
        x0 = t0;

        // mid = hi0 + lo1 + b0, with carryMid (0/1)
        ulong mid = hi0 + lo1;
        ulong carryMid = mid < hi0 ? 1UL : 0UL;

        ulong mid2 = mid + b0;
        carryMid |= mid2 < b0 ? 1UL : 0UL; // b0 is 0/1
        mid = mid2;

        // x1 -= mid
        ulong x11 = x1;
        ulong t1 = x11 - mid;
        ulong b1 = x11 < mid ? 1UL : 0UL;
        x1 = t1;

        // borrow for x2
        return hi1 + carryMid + b1;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong AddTo2(ref ulong x0, ref ulong x1, ulong y0, ulong y1)
    {
        ulong x00 = x0;
        ulong s0 = x00 + y0;
        ulong c0 = s0 < x00 ? 1UL : 0UL;
        x0 = s0;

        ulong x11 = x1;
        ulong s1 = x11 + y1;
        ulong c1 = s1 < x11 ? 1UL : 0UL;

        ulong s1c = s1 + c0;
        ulong c2 = s1c < s1 ? 1UL : 0UL;
        x1 = s1c;

        return c1 | c2;
    }


[SkipLocalsInit]
private static void Remainder512By128Bits(in UInt256 lo, in UInt256 hi, in UInt256 d, out UInt256 rem)
{
Debug.Assert((d.u2 | d.u3) == 0);

ulong d0 = d.u0;
ulong d1 = d.u1;
Debug.Assert((d0 | d1) != 0);

// Numerator limbs (u0 is least significant).
ulong u0 = lo.u0, u1 = lo.u1, u2 = lo.u2, u3 = lo.u3;
ulong u4 = hi.u0, u5 = hi.u1, u6 = hi.u2, u7 = hi.u3;

// In the slow path hi != 0, so uLen is always 5..8 (as in your original).
int uLen = u7 != 0 ? 8 : (u6 != 0 ? 7 : (u5 != 0 ? 6 : 5));

// ---------------------------
// 128-bit divisor (d1 != 0)
// ---------------------------
int sh = LeadingZeros(d1);

Unsafe.SkipInit(out ULong9 unBuf);
ulong nd0, nd1;

if (sh == 0)
{
    unBuf.w0 = u0; unBuf.w1 = u1; unBuf.w2 = u2; unBuf.w3 = u3;
    unBuf.w4 = u4; unBuf.w5 = u5; unBuf.w6 = u6; unBuf.w7 = u7;
    unBuf.w8 = 0;

    nd0 = d0;
    nd1 = d1;
}
else
{
    int rsh = 64 - sh;

    unBuf.w8 = u7 >> rsh;
    unBuf.w7 = (u7 << sh) | (u6 >> rsh);
    unBuf.w6 = (u6 << sh) | (u5 >> rsh);
    unBuf.w5 = (u5 << sh) | (u4 >> rsh);
    unBuf.w4 = (u4 << sh) | (u3 >> rsh);
    unBuf.w3 = (u3 << sh) | (u2 >> rsh);
    unBuf.w2 = (u2 << sh) | (u1 >> rsh);
    unBuf.w1 = (u1 << sh) | (u0 >> rsh);
    unBuf.w0 = u0 << sh;

    nd0 = d0 << sh;
    nd1 = (d1 << sh) | (d0 >> rsh);
}

ref ulong un0 = ref unBuf.w0;

// dLen is fixed at 2 here.
UremKnuth2(ref un0, uLen - 2, nd0, nd1);

// Denormalise remainder from un[0..1].
if (sh == 0)
{
    rem = new UInt256(unBuf.w0, unBuf.w1, 0, 0);
    return;
}
else
{
    int rsh = 64 - sh;
    ulong r0 = (unBuf.w0 >> sh) | (unBuf.w1 << rsh);
    ulong r1 = unBuf.w1 >> sh;
    rem = new UInt256(r0, r1, 0, 0);
    return;
}
}

    [SkipLocalsInit]
    private static void Remainder512By256Bits(in UInt256 lo, in UInt256 hi, in UInt256 d, out UInt256 rem)
    {
        ulong d0 = d.u0, d1 = d.u1, d2 = d.u2, d3 = d.u3;
        if ((d0 | d1 | d2 | d3) == 0)
            ThrowDivideByZeroException();

        // Divisor length (1..4) and normalisation shift.
        int dLen;
        int shift;
        if (d3 != 0) { dLen = 4; shift = LeadingZeros(d3); }
        else if (d2 != 0) { dLen = 3; shift = LeadingZeros(d2); }
        else if (d1 != 0) { dLen = 2; shift = LeadingZeros(d1); }
        else { dLen = 1; shift = LeadingZeros(d0); }

        // Numerator limbs (u0 is least significant).
        ulong u0 = lo.u0, u1n = lo.u1, u2n = lo.u2, u3n = lo.u3;
        ulong u4 = hi.u0, u5 = hi.u1, u6 = hi.u2, u7 = hi.u3;

        // In the slow path hi != 0, so uLen is always 5..8.
        int uLen = u7 != 0 ? 8 : (u6 != 0 ? 7 : (u5 != 0 ? 6 : 5));

        // Normalise numerator into 9 limbs (always fully assigned - safe with SkipLocalsInit).
        Unsafe.SkipInit(out ULong9 unBuf);

        // Normalise divisor digits too (compute all 4, slice by dLen logically).
        ulong nd0, nd1, nd2v, nd3v;

        if (shift == 0)
        {
            // un[0..7] = u[0..7], un[8] = 0
            unBuf.w0 = u0; unBuf.w1 = u1n; unBuf.w2 = u2n; unBuf.w3 = u3n;
            unBuf.w4 = u4; unBuf.w5 = u5; unBuf.w6 = u6; unBuf.w7 = u7;
            unBuf.w8 = 0;

            nd0 = d0; nd1 = d1; nd2v = d2; nd3v = d3;
        }
        else
        {
            int rshift = 64 - shift; // 1..63

            unBuf.w8 = u7 >> rshift;
            unBuf.w7 = (u7 << shift) | (u6 >> rshift);
            unBuf.w6 = (u6 << shift) | (u5 >> rshift);
            unBuf.w5 = (u5 << shift) | (u4 >> rshift);
            unBuf.w4 = (u4 << shift) | (u3n >> rshift);
            unBuf.w3 = (u3n << shift) | (u2n >> rshift);
            unBuf.w2 = (u2n << shift) | (u1n >> rshift);
            unBuf.w1 = (u1n << shift) | (u0 >> rshift);
            unBuf.w0 = u0 << shift;

            nd0 = d0 << shift;
            nd1 = (d1 << shift) | (d0 >> rshift);
            nd2v = (d2 << shift) | (d1 >> rshift);
            nd3v = (d3 << shift) | (d2 >> rshift);
        }

        ref ulong un0 = ref unBuf.w0;

        // Divide (remainder only). m = uLen - dLen, loop j = m..0.
        int mQ = uLen - dLen;

        switch (dLen)
        {
            case 1:
                {
                    ulong dn = nd0; // normalised 1-limb divisor (MSB set unless original d was 0).
                    ulong reciprocal = X86Base.X64.IsSupported ? 0 : Reciprocal2By1(dn);

                    // Long division by 1 word across the significant window only.
                    ulong r = Unsafe.Add(ref un0, uLen); // un[uLen] is the top carry limb (0 if shift == 0).
                    for (int j = uLen - 1; j >= 0; j--)
                    {
                        if (X86Base.X64.IsSupported)
                        {
                            (_, r) = X86Base.X64.DivRem(Unsafe.Add(ref un0, j), r, dn);
                        }
                        else
                        {
                            _ = UDivRem2By1(r, reciprocal, dn, Unsafe.Add(ref un0, j), out r);
                        }
                    }

                    if (shift != 0)
                        r >>= shift;

                    rem = new UInt256(r, 0, 0, 0);
                    return;
                }

            case 2:
                UremKnuth2(ref un0, mQ, nd0, nd1);
                break;

            case 3:
                UremKnuth3(ref un0, mQ, nd0, nd1, nd2v);
                break;

            default: // 4
                UremKnuth4(ref un0, mQ, nd0, nd1, nd2v, nd3v);
                break;
        }

        // Denormalise remainder from un[0..dLen-1].
        if (shift == 0)
        {
            rem = dLen switch
            {
                2 => new UInt256(unBuf.w0, unBuf.w1, 0, 0),
                3 => new UInt256(unBuf.w0, unBuf.w1, unBuf.w2, 0),
                _ => new UInt256(unBuf.w0, unBuf.w1, unBuf.w2, unBuf.w3),
            };
            return;
        }
        else
        {
            int rshift = 64 - shift;

            if (dLen == 2)
            {
                ulong r0 = (unBuf.w0 >> shift) | (unBuf.w1 << rshift);
                ulong r1 = (unBuf.w1 >> shift);
                rem = new UInt256(r0, r1, 0, 0);
                return;
            }

            if (dLen == 3)
            {
                ulong r0 = (unBuf.w0 >> shift) | (unBuf.w1 << rshift);
                ulong r1 = (unBuf.w1 >> shift) | (unBuf.w2 << rshift);
                ulong r2 = (unBuf.w2 >> shift);
                rem = new UInt256(r0, r1, r2, 0);
                return;
            }

            // dLen == 4
            ulong rr0 = (unBuf.w0 >> shift) | (unBuf.w1 << rshift);
            ulong rr1 = (unBuf.w1 >> shift) | (unBuf.w2 << rshift);
            ulong rr2 = (unBuf.w2 >> shift) | (unBuf.w3 << rshift);
            ulong rr3 = (unBuf.w3 >> shift);
            rem = new UInt256(rr0, rr1, rr2, rr3);
        }
    }

    [StructLayout(LayoutKind.Sequential)]
    private struct ULong9
    {
        public ulong w0, w1, w2, w3, w4, w5, w6, w7, w8;
    }

    // ----------------- Knuth remainder-only cores -----------------

    [SkipLocalsInit]
    private static void UremKnuth2(ref ulong un0, int m, ulong d0, ulong d1)
    {
        ulong dh = d1;
        ulong dl = d0; // d[n-2]
        ulong reciprocal = X86Base.X64.IsSupported ? 0 : Reciprocal2By1(dh);

        for (int j = m; j >= 0; j--)
        {
            ref ulong uJ = ref Unsafe.Add(ref un0, j);

            ulong u2 = Unsafe.Add(ref uJ, 2);
            ulong u1 = Unsafe.Add(ref uJ, 1);
            ulong u0 = uJ;

            ulong qhat = X86Base.X64.IsSupported ? EstimateQhatX86Base(u2, u1, u0, dh, dl) : EstimateQhat(u2, u1, u0, dh, dl, reciprocal);

            ulong borrow = SubMulTo2(ref uJ, ref Unsafe.Add(ref uJ, 1), d0, d1, qhat);
            ulong newU2 = u2 - borrow;
            Unsafe.Add(ref uJ, 2) = newU2;

            if (u2 < borrow)
            {
                newU2 += AddTo2(ref uJ, ref Unsafe.Add(ref uJ, 1), d0, d1);
                Unsafe.Add(ref uJ, 2) = newU2;
            }
        }
    }

    [SkipLocalsInit]
    private static void UremKnuth3(ref ulong un0, int m, ulong d0, ulong d1, ulong d2)
    {
        ulong dh = d2;
        ulong dl = d1; // d[n-2]
        ulong reciprocal = X86Base.X64.IsSupported ? 0 : Reciprocal2By1(dh);

        for (int j = m; j >= 0; j--)
        {
            ref ulong uJ = ref Unsafe.Add(ref un0, j);

            ulong u2 = Unsafe.Add(ref uJ, 3);
            ulong u1 = Unsafe.Add(ref uJ, 2);
            ulong u0 = Unsafe.Add(ref uJ, 1);

            ulong qhat = X86Base.X64.IsSupported ? EstimateQhatX86Base(u2, u1, u0, dh, dl) : EstimateQhat(u2, u1, u0, dh, dl, reciprocal);

            ulong borrow = SubMulTo3(ref uJ, d0, d1, d2, qhat);
            ulong newU2 = u2 - borrow;
            Unsafe.Add(ref uJ, 3) = newU2;

            if (u2 < borrow)
            {
                newU2 += AddTo3(ref uJ, d0, d1, d2);
                Unsafe.Add(ref uJ, 3) = newU2;
            }
        }
    }

    [SkipLocalsInit]
    private static void UremKnuth4(ref ulong un0, int m, ulong d0, ulong d1, ulong d2, ulong d3)
    {
        ulong dh = d3;
        ulong dl = d2; // d[n-2]
        ulong reciprocal = X86Base.X64.IsSupported ? 0 : Reciprocal2By1(dh);

        for (int j = m; j >= 0; j--)
        {
            ref ulong uJ = ref Unsafe.Add(ref un0, j);

            ulong u2 = Unsafe.Add(ref uJ, 4);
            ulong u1 = Unsafe.Add(ref uJ, 3);
            ulong u0 = Unsafe.Add(ref uJ, 2);

            ulong qhat = X86Base.X64.IsSupported ? EstimateQhatX86Base(u2, u1, u0, dh, dl) : EstimateQhat(u2, u1, u0, dh, dl, reciprocal);

            ulong borrow = SubMulTo4(ref uJ, d0, d1, d2, d3, qhat);
            ulong newU2 = u2 - borrow;
            Unsafe.Add(ref uJ, 4) = newU2;

            if (u2 < borrow)
            {
                newU2 += AddTo4(ref uJ, d0, d1, d2, d3);
                Unsafe.Add(ref uJ, 4) = newU2;
            }
        }
    }

    // ----------------- Correct qhat estimation (Knuth correction loop) -----------------

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong EstimateQhat(ulong u2, ulong u1, ulong u0, ulong dh, ulong dl, ulong reciprocal)
    {
        // qhat = min((u2:b + u1) / dh, b - 1)
        // then while qhat*dl > (rhat:b + u0): qhat--, rhat += dh (stop if rhat overflows base).
        ulong qhat;
        ulong rhat;

        if (u2 > dh)
        {
            // Quotient digit saturates at b - 1. No correction needed (rhat would be >= b).
            return ulong.MaxValue;
        }

        if (u2 == dh)
        {
            qhat = ulong.MaxValue;
            rhat = u1 + dh;

            // If rhat overflowed base b, the correction inequality cannot hold.
            if (rhat < u1)
                return qhat;
        }
        else
        {
            qhat = UDivRem2By1(u2, reciprocal, dh, u1, out rhat);
        }

        // At most 2 iterations in practice for Knuth D.
        while (true)
        {
            ulong ph = Multiply64(qhat, dl, out ulong pl);
            if (ph < rhat || (ph == rhat && pl <= u0))
                break;

            qhat--;

            ulong prev = rhat;
            rhat += dh;

            // rhat >= b => correction test cannot hold any more.
            if (rhat < prev)
                break;
        }

        return qhat;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong EstimateQhatX86Base(ulong u2, ulong u1, ulong u0, ulong dh, ulong dl)
    {
        // qhat = min((u2:b + u1) / dh, b - 1)
        // then while qhat*dl > (rhat:b + u0): qhat--, rhat += dh (stop if rhat overflows base).
        ulong qhat;
        ulong rhat;

        if (u2 > dh)
        {
            // Quotient digit saturates at b - 1. No correction needed (rhat would be >= b).
            return ulong.MaxValue;
        }

        if (u2 == dh)
        {
            qhat = ulong.MaxValue;
            rhat = u1 + dh;

            // If rhat overflowed base b, the correction inequality cannot hold.
            if (rhat < u1)
                return qhat;
        }
        else
        {
            (qhat, rhat) = X86Base.X64.DivRem(u1, u2, dh);
        }

        // At most 2 iterations in practice for Knuth D.
        while (true)
        {
            ulong ph = Multiply64(qhat, dl, out ulong pl);
            if (ph < rhat || (ph == rhat && pl <= u0))
                break;

            qhat--;

            ulong prev = rhat;
            rhat += dh;

            // rhat >= b => correction test cannot hold any more.
            if (rhat < prev)
                break;
        }

        return qhat;
    }


    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong SubMulTo3(ref ulong x0, ulong y0, ulong y1, ulong y2, ulong mul)
    {
        ref ulong x1 = ref Unsafe.Add(ref x0, 1);
        ref ulong x2 = ref Unsafe.Add(ref x0, 2);

        ulong borrow = 0;

        ulong b1 = 0;
        SubtractWithBorrow(x0, borrow, ref b1, out ulong s0);
        ulong ph0 = Multiply64(y0, mul, out ulong pl0);
        ulong b2 = 0;
        SubtractWithBorrow(s0, pl0, ref b2, out x0);
        borrow = ph0 + b1 + b2;

        b1 = 0;
        SubtractWithBorrow(x1, borrow, ref b1, out ulong s1);
        ulong ph1 = Multiply64(y1, mul, out ulong pl1);
        b2 = 0;
        SubtractWithBorrow(s1, pl1, ref b2, out x1);
        borrow = ph1 + b1 + b2;

        b1 = 0;
        SubtractWithBorrow(x2, borrow, ref b1, out ulong s2);
        ulong ph2 = Multiply64(y2, mul, out ulong pl2);
        b2 = 0;
        SubtractWithBorrow(s2, pl2, ref b2, out x2);
        borrow = ph2 + b1 + b2;

        return borrow;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong SubMulTo4(ref ulong x0, ulong y0, ulong y1, ulong y2, ulong y3, ulong mul)
    {
        ref ulong x1 = ref Unsafe.Add(ref x0, 1);
        ref ulong x2 = ref Unsafe.Add(ref x0, 2);
        ref ulong x3 = ref Unsafe.Add(ref x0, 3);

        ulong borrow = 0;

        ulong b1 = 0;
        SubtractWithBorrow(x0, borrow, ref b1, out ulong s0);
        ulong ph0 = Multiply64(y0, mul, out ulong pl0);
        ulong b2 = 0;
        SubtractWithBorrow(s0, pl0, ref b2, out x0);
        borrow = ph0 + b1 + b2;

        b1 = 0;
        SubtractWithBorrow(x1, borrow, ref b1, out ulong s1);
        ulong ph1 = Multiply64(y1, mul, out ulong pl1);
        b2 = 0;
        SubtractWithBorrow(s1, pl1, ref b2, out x1);
        borrow = ph1 + b1 + b2;

        b1 = 0;
        SubtractWithBorrow(x2, borrow, ref b1, out ulong s2);
        ulong ph2 = Multiply64(y2, mul, out ulong pl2);
        b2 = 0;
        SubtractWithBorrow(s2, pl2, ref b2, out x2);
        borrow = ph2 + b1 + b2;

        b1 = 0;
        SubtractWithBorrow(x3, borrow, ref b1, out ulong s3);
        ulong ph3 = Multiply64(y3, mul, out ulong pl3);
        b2 = 0;
        SubtractWithBorrow(s3, pl3, ref b2, out x3);
        borrow = ph3 + b1 + b2;

        return borrow;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong AddTo3(ref ulong x0, ulong y0, ulong y1, ulong y2)
    {
        ref ulong x1 = ref Unsafe.Add(ref x0, 1);
        ref ulong x2 = ref Unsafe.Add(ref x0, 2);

        ulong carry = 0;
        AddWithCarry(x0, y0, ref carry, out x0);
        AddWithCarry(x1, y1, ref carry, out x1);
        AddWithCarry(x2, y2, ref carry, out x2);
        return carry;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong AddTo4(ref ulong x0, ulong y0, ulong y1, ulong y2, ulong y3)
    {
        ref ulong x1 = ref Unsafe.Add(ref x0, 1);
        ref ulong x2 = ref Unsafe.Add(ref x0, 2);
        ref ulong x3 = ref Unsafe.Add(ref x0, 3);

        ulong carry = 0;
        AddWithCarry(x0, y0, ref carry, out x0);
        AddWithCarry(x1, y1, ref carry, out x1);
        AddWithCarry(x2, y2, ref carry, out x2);
        AddWithCarry(x3, y3, ref carry, out x3);
        return carry;
    }

    public void MultiplyMod(in UInt256 a, in UInt256 m, out UInt256 res) => MultiplyMod(this, a, m, out res);

    [SkipLocalsInit]
    private static void Multiply256To512Bit(in UInt256 x, in UInt256 y, out UInt256 low, out UInt256 high)
    {
        if (x.IsUint64 && y.IsUint64)
        {
            // Fast multiply for numbers less than 2^64 (18,446,744,073,709,551,615)
            ulong highUL = Multiply64(x.u0, y.u0, out ulong lowUL);
            // Assignment to high, low after multiply in case either is used as input for x or y (by ref aliasing)
            high = default;
            low = default;
            Unsafe.AsRef(in low.u0) = lowUL;
            Unsafe.AsRef(in low.u1) = highUL;
            return;
        }

        Multiply256To512BitLarge(x, y, out low, out high);
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void Multiply256To512BitLarge(UInt256 x, UInt256 y, out UInt256 low, out UInt256 high)
    {
        // Copy inputs up front - this breaks aliasing with out params so we can store early.
        ulong x0 = x.u0, x1 = x.u1, x2 = x.u2, x3 = x.u3;
        ulong y0 = y.u0, y1 = y.u1, y2 = y.u2, y3 = y.u3;

        Unsafe.SkipInit(out low);
        Unsafe.SkipInit(out high);

        // Column 0: p0 = x0*y0 (low), carry = high
        ulong carryLo = Multiply64(x0, y0, out ulong p0);
        ulong carryHi = 0;
        Unsafe.AsRef(in low.u0) = p0;

        // Column 1: p1 = carry + x0*y1 + x1*y0
        ulong a0 = carryLo, a1 = carryHi, a2 = 0;
        MultiplyAddCarry(ref a0, ref a1, ref a2, x0, y1);
        MultiplyAddCarry(ref a0, ref a1, ref a2, x1, y0);
        Unsafe.AsRef(in low.u1) = a0;
        carryLo = a1; carryHi = a2;

        // Column 2: p2 = carry + x0*y2 + x1*y1 + x2*y0
        a0 = carryLo; a1 = carryHi; a2 = 0;
        MultiplyAddCarry(ref a0, ref a1, ref a2, x0, y2);
        MultiplyAddCarry(ref a0, ref a1, ref a2, x1, y1);
        MultiplyAddCarry(ref a0, ref a1, ref a2, x2, y0);
        Unsafe.AsRef(in low.u2) = a0;
        carryLo = a1; carryHi = a2;

        // Column 3: p3 = carry + x0*y3 + x1*y2 + x2*y1 + x3*y0
        a0 = carryLo; a1 = carryHi; a2 = 0;
        MultiplyAddCarry(ref a0, ref a1, ref a2, x0, y3);
        MultiplyAddCarry(ref a0, ref a1, ref a2, x1, y2);
        MultiplyAddCarry(ref a0, ref a1, ref a2, x2, y1);
        MultiplyAddCarry(ref a0, ref a1, ref a2, x3, y0);
        Unsafe.AsRef(in low.u3) = a0;
        carryLo = a1; carryHi = a2;

        // Column 4: p4 = carry + x1*y3 + x2*y2 + x3*y1
        a0 = carryLo; a1 = carryHi; a2 = 0;
        MultiplyAddCarry(ref a0, ref a1, ref a2, x1, y3);
        MultiplyAddCarry(ref a0, ref a1, ref a2, x2, y2);
        MultiplyAddCarry(ref a0, ref a1, ref a2, x3, y1);
        Unsafe.AsRef(in high.u0) = a0;
        carryLo = a1; carryHi = a2;

        // Column 5: p5 = carry + x2*y3 + x3*y2
        a0 = carryLo; a1 = carryHi; a2 = 0;
        MultiplyAddCarry(ref a0, ref a1, ref a2, x2, y3);
        MultiplyAddCarry(ref a0, ref a1, ref a2, x3, y2);
        Unsafe.AsRef(in high.u1) = a0;
        carryLo = a1; carryHi = a2;

        // Column 6: p6 = carry + x3*y3
        a0 = carryLo; a1 = carryHi; a2 = 0;
        MultiplyAddCarry(ref a0, ref a1, ref a2, x3, y3);
        Unsafe.AsRef(in high.u2) = a0;

        // Column 7: remaining carry (a1). For 256x256, a2 must end up 0 here.
        Unsafe.AsRef(in high.u3) = a1;
    }

    
    // Preconditions (enforced by public Divide wrapper):
    // - y != 0
    // - x > y
    // - x != y
    // - x is not uint64-only
    //
    // This implementation returns quotient only (fastest for Divide()).
    // If you need remainder too, keep the same core but unnormalise the final u-limbs.
    [SkipLocalsInit]
    private static void DivideImpl(in UInt256 x, in UInt256 y, out UInt256 quotient, out UInt256 remainder)
    {
        if (y.u3 != 0)
        {
            DivideBy256Bits(in x, in y, out quotient, out remainder);
        }
        else if (y.u2 != 0)
        {
            DivideBy192Bits(in x, in y, out quotient, out remainder);
        }
        else if (y.u1 != 0)
        {
            if (X86Base.X64.IsSupported)
            {
                DivideBy128BitsX86Base(in x, in y, out quotient, out remainder);
            }
            else
            {
                DivideBy128Bits(in x, in y, out quotient, out remainder);
            }
        }
        else
        {
            if (X86Base.X64.IsSupported)
            {
                DivideBy64BitsX86Base(in x, y.u0, out quotient, out remainder);
            }
            else
            {
                DivideBy64Bits(in x, y.u0, out quotient, out remainder);
            }
        }
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void DivideBy64BitsX86Base(in UInt256 x, ulong divisor, out UInt256 q, out UInt256 remainder)
    {
        ulong rem = 0;
        ulong q3 = 0;
        ulong u3 = x.u3;
        if (u3 != 0)
        {
            (q3, rem) = X86Base.X64.DivRem(lower: u3, upper: rem, divisor);
        }
        ulong u2 = x.u2;
        ulong q2 = 0;
        if ((u2 | rem) != 0)
        {
            (q2, rem) = X86Base.X64.DivRem(lower: u2, upper: rem, divisor);
        }
        ulong u1 = x.u1;
        ulong q1 = 0;
        if ((u1 | rem) != 0)
        {
            (q1, rem) = X86Base.X64.DivRem(lower: u1, upper: rem, divisor);
        }
        ulong u0 = x.u0;
        ulong q0 = 0;
        if ((u0 | rem) != 0)
        {
            (q0, rem) = X86Base.X64.DivRem(lower: u0, upper: rem, divisor);
        }

        q = Create(q0, q1, q2, q3);
        remainder = Create(rem, 0, 0, 0);
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void DivideBy64Bits(in UInt256 x, ulong divisor, out UInt256 q, out UInt256 remainder)
    {
        int s = BitOperations.LeadingZeroCount(divisor);
        ulong dn = divisor << s; // normalised divisor (msb set if s>0)
        // Normalise dividend into 5 limbs
        ulong u0n = x.u0;
        ulong u1n = x.u1;
        ulong u2n = x.u2;
        ulong u3n = x.u3;
        ulong rem = 0;
        if (s > 0)
        {
            int rs = 64 - s;
            rem = (u3n >> rs);
            u3n = (u3n << s) | (u2n >> rs);
            u2n = (u2n << s) | (u1n >> rs);
            u1n = (u1n << s) | (u0n >> rs);
            u0n <<= s;
        }

        ulong recip = Reciprocal2By1(dn);
        ulong q3 = ((rem | u3n) == 0) ? 0 : UDivRem2By1(rem, recip, dn, u3n, out rem);
        ulong q2 = ((rem | u2n) == 0) ? 0 : UDivRem2By1(rem, recip, dn, u2n, out rem);
        ulong q1 = ((rem | u1n) == 0) ? 0 : UDivRem2By1(rem, recip, dn, u1n, out rem);
        ulong q0 = ((rem | u0n) == 0) ? 0 : UDivRem2By1(rem, recip, dn, u0n, out rem);
        q = Create(q0, q1, q2, q3);

        // Unnormalise remainder (single limb)
        ulong r0 = rem >> s;
        remainder = Create(r0, 0, 0, 0);
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void DivideBy192Bits(in UInt256 x, in UInt256 y, out UInt256 q, out UInt256 remainder)
    {
        // n >= 2: Knuth D (specialised) with reciprocal qhat

        int shift = BitOperations.LeadingZeroCount(y.u2);

        // Normalise divisor v = y << shift
        ulong v0, v1n, v2n;
        if (shift == 0)
        {
            v0 = y.u0; v1n = y.u1; v2n = y.u2;
        }
        else
        {
            int rs = 64 - shift;
            v0 = y.u0 << shift;
            v1n = (y.u1 << shift) | (y.u0 >> rs);
            v2n = (y.u2 << shift) | (y.u1 >> rs);
        }

        // Normalise dividend u = x << shift into 5 limbs
        ulong u0n2, u1d, u2d, u3d, u4d;
        if (shift == 0)
        {
            u0n2 = x.u0; u1d = x.u1; u2d = x.u2; u3d = x.u3; u4d = 0;
        }
        else
        {
            int rs = 64 - shift;
            u0n2 = x.u0 << shift;
            u1d = (x.u1 << shift) | (x.u0 >> rs);
            u2d = (x.u2 << shift) | (x.u1 >> rs);
            u3d = (x.u3 << shift) | (x.u2 >> rs);
            u4d = (x.u3 >> rs);
        }

        ulong vRecip = X86Base.X64.IsSupported ? 0 : Reciprocal2By1(v2n);
        ulong qhat, rhat, rcarry;
        if (u4d == v2n)
        {
            qhat = ulong.MaxValue;
            ulong sum = u3d + v2n;
            rcarry = (sum < u3d) ? 1UL : 0UL;
            rhat = sum;
        }
        else
        {
            if (X86Base.X64.IsSupported)
            {
                (qhat, rhat) = X86Base.X64.DivRem(u3d, u4d, v2n); // (upper:lower) = (u4d:u3d)
            }
            else
            {
                qhat = UDivRem2By1(u4d, vRecip, v2n, u3d, out rhat);
            }
            rcarry = 0;
        }

        if (rcarry == 0)
        {
            ulong pHi = Multiply64(qhat, v1n, out ulong pLo);

            // if qhat*vNext > rhat*b + uCorr then decrement
            if (pHi > rhat || (pHi == rhat && pLo > u2d))
            {
                qhat--;

                ulong sum1 = rhat + v2n;
                if (sum1 < rhat)
                {
                    rcarry = 1;
                }

                rhat = sum1;
            }
        }

        if (rcarry == 0)
        {
            ulong pHi = Multiply64(qhat, v1n, out ulong pLo);

            // if qhat*vNext > rhat*b + uCorr then decrement
            if (pHi > rhat || (pHi == rhat && pLo > u2d))
            {
                qhat--;
            }
        }

        ulong borrow1 = 0;

        ulong pHi1 = Multiply64(qhat, v0, out ulong pLo1);
        u1d = Sub(u1d, pLo1, ref borrow1);

        ulong carry = pHi1;
        pHi1 = Multiply64(qhat, v1n, out pLo1);
        ulong sum2 = pLo1 + carry;
        ulong c2 = (sum2 < pLo1) ? 1UL : 0UL;
        carry = pHi1 + c2;
        u2d = Sub(u2d, sum2, ref borrow1);

        pHi1 = Multiply64(qhat, v2n, out pLo1);
        sum2 = pLo1 + carry;
        c2 = (sum2 < pLo1) ? 1UL : 0UL;
        carry = pHi1 + c2;
        u3d = Sub(u3d, sum2, ref borrow1);

        u4d = Sub(u4d, carry, ref borrow1);
        ulong borrow = borrow1;

        if (borrow != 0)
        {
            AddBack3(ref u1d, ref u2d, ref u3d, ref u4d, v0, v1n, v2n);
            qhat--;
        }

        ulong q1 = qhat;
        ulong qhat1, rhat1, rcarry1;
        if (u3d == v2n)
        {
            qhat1 = ulong.MaxValue;
            ulong sum3 = u2d + v2n;
            rcarry1 = (sum3 < u2d) ? 1UL : 0UL;
            rhat1 = sum3;
        }
        else
        {
            if (X86Base.X64.IsSupported)
            {
                (qhat1, rhat1) = X86Base.X64.DivRem(u2d, u3d, v2n); // (upper:lower) = (u3d:u2d)
            }
            else
            {
                qhat1 = UDivRem2By1(u3d, vRecip, v2n, u2d, out rhat1);
            }
            rcarry1 = 0;
        }

        if (rcarry1 == 0)
        {
            ulong pHi2 = Multiply64(qhat1, v1n, out ulong pLo2);

            // if qhat*vNext > rhat*b + uCorr then decrement
            if (pHi2 > rhat1 || (pHi2 == rhat1 && pLo2 > u1d))
            {
                qhat1--;

                ulong sum4 = rhat1 + v2n;
                if (sum4 < rhat1)
                {
                    rcarry1 = 1;
                }

                rhat1 = sum4;
            }
        }

        if (rcarry1 == 0)
        {
            ulong pHi3 = Multiply64(qhat1, v1n, out ulong pLo3);

            // if qhat*vNext > rhat*b + uCorr then decrement
            if (pHi3 > rhat1 || (pHi3 == rhat1 && pLo3 > u1d))
            {
                qhat1--;
            }
        }

        ulong borrow2 = 0;

        ulong pHi4 = Multiply64(qhat1, v0, out ulong pLo4);
        ulong sum6 = pLo4;
        ulong c3 = (sum6 < pLo4) ? 1UL : 0UL;
        ulong carry1 = pHi4 + c3;
        u0n2 = Sub(u0n2, sum6, ref borrow2);

        pHi4 = Multiply64(qhat1, v1n, out pLo4);
        sum6 = pLo4 + carry1;
        c3 = (sum6 < pLo4) ? 1UL : 0UL;
        carry1 = pHi4 + c3;
        u1d = Sub(u1d, sum6, ref borrow2);

        pHi4 = Multiply64(qhat1, v2n, out pLo4);
        sum6 = pLo4 + carry1;
        c3 = (sum6 < pLo4) ? 1UL : 0UL;
        carry1 = pHi4 + c3;
        u2d = Sub(u2d, sum6, ref borrow2);

        u3d = Sub(u3d, carry1, ref borrow2);
        ulong borrow3 = borrow2;

        if (borrow3 != 0)
        {
            AddBack3(ref u0n2, ref u1d, ref u2d, ref u3d, v0, v1n, v2n);
            qhat1--;
        }

        ulong q0 = qhat1;

        q = Create(q0, q1, 0, 0);

        // Remainder is u0..u2
        UInt256 remN = Create(u0n2, u1d, u2d, 0);
        remainder = ShiftRightSmall(remN, shift);
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void DivideBy256Bits(in UInt256 x, in UInt256 y, out UInt256 q, out UInt256 remainder)
    {
        // n >= 2: Knuth D (specialised) with reciprocal qhat

        int shift = BitOperations.LeadingZeroCount(y.u3);

        // Normalise divisor v = y << shift
        UInt256 u = ShiftLeftSmall(in x, shift);
        UInt256 v = ShiftLeftSmall(in y, shift);
        // Normalise dividend u = x << shift into 5 limbs
        ulong u4d;
        if (shift == 0)
        {
            u4d = 0;
        }
        else
        {
            int rs = 64 - shift;
            u4d = (x.u3 >> rs);
        }

        ulong vRecip = X86Base.X64.IsSupported ? 0 : Reciprocal2By1(v.u3);
        ulong qhat, rhat, rcarry;
        if (u4d == v.u3)
        {
            qhat = ulong.MaxValue;
            ulong sum = u.u3 + v.u3;
            rcarry = (sum < u.u3) ? 1UL : 0UL;
            rhat = sum;
        }
        else
        {
            if (X86Base.X64.IsSupported)
            {
                (qhat, rhat) = X86Base.X64.DivRem(u.u3, u4d, v.u3); // (upper:lower) = (u4d:u.u3)
            }
            else
            {
                qhat = UDivRem2By1(u4d, vRecip, v.u3, u.u3, out rhat);
            }
            rcarry = 0;
        }

        if (rcarry == 0)
        {
            ulong pHi = Multiply64(qhat, v.u2, out ulong pLo);

            // if qhat*vNext > rhat*b + uCorr then decrement
            if (pHi > rhat || (pHi == rhat && pLo > u.u2))
            {
                qhat--;

                ulong sum1 = rhat + v.u3;
                if (sum1 < rhat)
                    rcarry = 1;

                rhat = sum1;
            }
        }

        if (rcarry == 0)
        {
            ulong pHi = Multiply64(qhat, v.u2, out ulong pLo);

            // if qhat*vNext > rhat*b + uCorr then decrement
            if (pHi > rhat || (pHi == rhat && pLo > u.u2))
            {
                qhat--;
            }
        }

        ulong borrow = SubMul4(in u, ref u4d, in v, qhat, out UInt256 rem);

        if (borrow != 0)
        {
            Add(in rem, in v, out rem);
            qhat--;
        }

        ulong q0 = qhat;

        q = Create(q0, 0, 0, 0);

        // Remainder is u0..u3
        remainder = ShiftRightSmall(rem, shift);
    }

    // Shift-right by 0..63 (used to unnormalise remainder)
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static UInt256 ShiftLeftSmall(in UInt256 v, int sh)
    {
        if (sh == 0) return v;

        if (!Avx2.IsSupported)
        {
            ulong a0 = v.u0;
            ulong a1 = v.u1;
            ulong a2 = v.u2;
            ulong a3 = v.u3;

            int rs = 64 - sh;

            Unsafe.SkipInit(out UInt256 r);
            Unsafe.AsRef(in r.u0) = a0 << sh;
            Unsafe.AsRef(in r.u1) = (a1 << sh) | (a0 >> rs);
            Unsafe.AsRef(in r.u2) = (a2 << sh) | (a1 >> rs);
            Unsafe.AsRef(in r.u3) = (a3 << sh) | (a2 >> rs);

            return r;
        }
        else
        {
            Vector256<ulong> x = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in v));
            Vector128<ulong> cL = Vector128.CreateScalarUnsafe((ulong)(uint)sh);
            Vector128<ulong> cR = Vector128.CreateScalarUnsafe(64uL - (ulong)(uint)sh);

            Vector256<ulong> left = Avx2.ShiftLeftLogical(x, cL);
            Vector256<ulong> y;
            if (Avx512F.VL.IsSupported)
            {
                Vector256<ulong> prev = Avx512F.VL.AlignRight64(x, default, 3);
                Vector256<ulong> right = Avx2.ShiftRightLogical(prev, cR);
                y = Avx2.Or(left, right);
            }
            else
            {
                Vector256<ulong> right = Avx2.ShiftRightLogical(x, cR);
                Vector256<ulong> carry = Avx2.Permute4x64(right, 0x90);
                carry = Avx2.And(carry, Vector256.Create(0UL, ulong.MaxValue, ulong.MaxValue, ulong.MaxValue));
                y = Avx2.Or(left, carry);
            }

            Unsafe.SkipInit(out UInt256 r);
            Unsafe.As<UInt256, Vector256<ulong>>(ref r) = y;
            return r;
        }
    }

    // Shift-right by 0..63 (used to unnormalise remainder)
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static UInt256 ShiftRightSmall(in UInt256 v, int sh)
    {
        if (sh == 0) return v;

        if (!Avx2.IsSupported)
        {
            ulong a0 = v.u0;
            ulong a1 = v.u1;
            ulong a2 = v.u2;
            ulong a3 = v.u3;

            int rs = 64 - sh;

            Unsafe.SkipInit(out UInt256 result);
            Unsafe.AsRef(in result.u0) = (a0 >> sh) | (a1 << rs);
            Unsafe.AsRef(in result.u1) = (a1 >> sh) | (a2 << rs);
            Unsafe.AsRef(in result.u2) = (a2 >> sh) | (a3 << rs);
            Unsafe.AsRef(in result.u3) = (a3 >> sh);
            return result;
        }
        else
        {
            Vector256<ulong> x = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in v));

            // right = x >> sh
            Vector128<ulong> cR = Vector128.CreateScalarUnsafe((ulong)sh);
            Vector256<ulong> right = Avx2.ShiftRightLogical(x, cR);

            // carry = (next limb) << (64 - sh)
            Vector128<ulong> cL = Vector128.CreateScalarUnsafe((ulong)(64 - sh));

            Vector256<ulong> y;
            if (Avx512F.VL.IsSupported)
            {
                // next = [a1, a2, a3, 0]
                Vector256<ulong> next = Avx512F.VL.AlignRight64(default, x, 1);
                Vector256<ulong> carry = Avx2.ShiftLeftLogical(next, cL);
                y = Avx2.Or(right, carry);
            }
            else
            {
                Vector256<ulong> left = Avx2.ShiftLeftLogical(x, cL);
                // carry lanes: [a1<<rs, a2<<rs, a3<<rs, a0<<rs] then zero the last lane
                Vector256<ulong> carry = Avx2.Permute4x64(left, 0x39);
                carry = Avx2.And(carry, Vector256.Create(ulong.MaxValue, ulong.MaxValue, ulong.MaxValue, 0UL));
                y = Avx2.Or(right, carry);
            }

            Unsafe.SkipInit(out UInt256 r);
            Unsafe.As<UInt256, Vector256<ulong>>(ref r) = y;
            return r;
        }
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void DivideBy128BitsX86Base(in UInt256 x, in UInt256 y, out UInt256 q, out UInt256 remainder)
    {
        // n == 2: specialised Knuth D with hardware DivRem
        Debug.Assert(y.u1 != 0 && y.u2 == 0 && y.u3 == 0);

        // Normalise divisor (2 limbs)
        ulong y0 = y.u0;
        ulong y1 = y.u1;

        int shift = BitOperations.LeadingZeroCount(y1);

        ulong v0, v1n;
        if (shift != 0)
        {
            int rs = 64 - shift;
            v0 = y0 << shift;
            v1n = (y1 << shift) | (y0 >> rs);
        }
        else
        {
            v0 = y0;
            v1n = y1;
        }

        // Normalise dividend (5 limbs)
        ulong u0 = x.u0;
        ulong u1 = x.u1;
        ulong u2 = x.u2;
        ulong u3 = x.u3;
        ulong u4;

        if (shift != 0)
        {
            int rs = 64 - shift;

            u4 = u3 >> rs;
            u3 = (u3 << shift) | (u2 >> rs);
            u2 = (u2 << shift) | (u1 >> rs);
            u1 = (u1 << shift) | (u0 >> rs);
            u0 <<= shift;
        }
        else
        {
            u4 = 0;
        }

        Unsafe.SkipInit(out q);
        ref ulong qRef = ref Unsafe.As<UInt256, ulong>(ref q);

        // Fast path: if the normalised low limb is 0 then V = v1n*B.
        // That turns the whole thing into a plain 256/64 division on (u4..u1),
        // with remainder (r:u0).
        if (v0 == 0)
        {
            Debug.Assert(u4 < v1n);

            ulong r = u4;

            (ulong q2, ulong r2) = X86Base.X64.DivRem(u3, r, v1n);
            r = r2;
            (ulong q1, ulong r1) = X86Base.X64.DivRem(u2, r, v1n);
            r = r1;
            (ulong q0, ulong r0) = X86Base.X64.DivRem(u1, r, v1n);
            r = r0;

            Unsafe.Add(ref qRef, 0) = q0;
            Unsafe.Add(ref qRef, 1) = q1;
            Unsafe.Add(ref qRef, 2) = q2;
            Unsafe.Add(ref qRef, 3) = 0;

            Unsafe.SkipInit(out remainder);
            ref ulong rRef = ref Unsafe.As<UInt256, ulong>(ref remainder);

            if (shift == 0)
            {
                Unsafe.Add(ref rRef, 0) = u0;
                Unsafe.Add(ref rRef, 1) = r;
            }
            else
            {
                int rs = 64 - shift;
                Unsafe.Add(ref rRef, 0) = (u0 >> shift) | (r << rs);
                Unsafe.Add(ref rRef, 1) = r >> shift;
            }

            Unsafe.Add(ref rRef, 2) = 0;
            Unsafe.Add(ref rRef, 3) = 0;
            return;
        }

        // n == 2 trick:
        // After DivRem on v1n:
        //   (uHi*B + uMid) = qhat*v1n + rhat
        // So subtracting qhat*(v1n*B + v0) from (uHi:uMid:uLo) reduces to:
        //   (rhat:uLo) - qhat*v0
        //
        // This removes the qhat*v1n multiply and the full 3-limb subtract/add-back.

        // Step j=2: q2 from (u4:u3:u2)
        {
            // Always true for this setup: u4 < v1n, so DivRem is safe here.
            Debug.Assert(u4 < v1n);

            (ulong qhat, ulong rhat) = X86Base.X64.DivRem(u3, u4, v1n);
            bool rcarry = false;

            ulong hi = Multiply64(qhat, v0, out ulong lo);

            // Correct at most twice.
            if (!rcarry && (hi > rhat || (hi == rhat && lo > u2)))
            {
                qhat--;
                ulong lo2 = lo - v0;
                hi -= (lo < v0) ? 1UL : 0UL;
                lo = lo2;

                rhat += v1n;
                rcarry = rhat < v1n;

                if (!rcarry && (hi > rhat || (hi == rhat && lo > u2)))
                {
                    qhat--;
                    lo2 = lo - v0;
                    hi -= (lo < v0) ? 1UL : 0UL;
                    lo = lo2;

                    rhat += v1n;
                }
            }

            ulong borrow = (u2 < lo) ? 1UL : 0UL;
            u2 -= lo;
            u3 = rhat - hi - borrow;

            Unsafe.Add(ref qRef, 2) = qhat;
        }

        // Step j=1: q1 from (u3:u2:u1)
        {
            ulong rhat;
            bool rcarry;
            ulong qhat;

            // Required for DIV safety when uHi == v1n.
            if (u3 == v1n)
            {
                qhat = ulong.MaxValue;
                rhat = u2 + v1n;
                rcarry = rhat < u2;
            }
            else
            {
                (qhat, rhat) = X86Base.X64.DivRem(u2, u3, v1n);
                rcarry = false;
            }

            ulong hi = Multiply64(qhat, v0, out ulong lo);

            if (!rcarry && (hi > rhat || (hi == rhat && lo > u1)))
            {
                qhat--;
                ulong lo2 = lo - v0;
                hi -= (lo < v0) ? 1UL : 0UL;
                lo = lo2;

                rhat += v1n;
                rcarry = rhat < v1n;

                if (!rcarry && (hi > rhat || (hi == rhat && lo > u1)))
                {
                    qhat--;
                    lo2 = lo - v0;
                    hi -= (lo < v0) ? 1UL : 0UL;
                    lo = lo2;

                    rhat += v1n;
                }
            }

            ulong borrow = (u1 < lo) ? 1UL : 0UL;
            u1 -= lo;
            u2 = rhat - hi - borrow;

            Unsafe.Add(ref qRef, 1) = qhat;
        }

        // Step j=0: q0 from (u2:u1:u0)
        {
            ulong rhat;
            bool rcarry;
            ulong qhat;

            // Required for DIV safety when uHi == v1n.
            if (u2 == v1n)
            {
                qhat = ulong.MaxValue;
                rhat = u1 + v1n;
                rcarry = rhat < u1;
            }
            else
            {
                (qhat, rhat) = X86Base.X64.DivRem(u1, u2, v1n);
                rcarry = false;
            }

            ulong hi = Multiply64(qhat, v0, out ulong lo);

            if (!rcarry && (hi > rhat || (hi == rhat && lo > u0)))
            {
                qhat--;
                ulong lo2 = lo - v0;
                hi -= (lo < v0) ? 1UL : 0UL;
                lo = lo2;

                rhat += v1n;
                rcarry = rhat < v1n;

                if (!rcarry && (hi > rhat || (hi == rhat && lo > u0)))
                {
                    qhat--;
                    lo2 = lo - v0;
                    hi -= (lo < v0) ? 1UL : 0UL;
                    lo = lo2;

                    rhat += v1n;
                }
            }

            ulong borrow = (u0 < lo) ? 1UL : 0UL;
            u0 -= lo;
            u1 = rhat - hi - borrow;

            Unsafe.Add(ref qRef, 0) = qhat;
        }

        // q3 is always 0 for 256/128 here.
        Unsafe.Add(ref qRef, 3) = 0;

        // Remainder (u0..u1 in normalised space) - unnormalise.
        Unsafe.SkipInit(out remainder);
        ref ulong remRef = ref Unsafe.As<UInt256, ulong>(ref remainder);

        if (shift == 0)
        {
            Unsafe.Add(ref remRef, 0) = u0;
            Unsafe.Add(ref remRef, 1) = u1;
        }
        else
        {
            int rs = 64 - shift;
            Unsafe.Add(ref remRef, 0) = (u0 >> shift) | (u1 << rs);
            Unsafe.Add(ref remRef, 1) = u1 >> shift;
        }

        Unsafe.Add(ref remRef, 2) = 0;
        Unsafe.Add(ref remRef, 3) = 0;
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void DivideBy128Bits(in UInt256 x, in UInt256 y, out UInt256 q, out UInt256 remainder)
    {
        // n >= 2: Knuth D (specialised) with reciprocal qhat
        // Preconditions (debug-only)
        Debug.Assert(y.u1 != 0 && y.u2 == 0 && y.u3 == 0);

        // Normalise divisor (2 limbs)
        ulong y0 = y.u0;
        ulong y1 = y.u1;

        int shift = BitOperations.LeadingZeroCount(y1);

        ulong v0, v1n;
        if (shift != 0)
        {
            int rs = 64 - shift;
            v0 = y0 << shift;
            v1n = (y1 << shift) | (y0 >> rs);
        }
        else
        {
            v0 = y0;
            v1n = y1;
        }

        // Reciprocal of the normalised high limb.
        ulong vRecip = Reciprocal2By1(v1n);

        // Normalise dividend (5 limbs)
        // Load after divisor prep - avoids keeping u-limbs live across the Reciprocal call.
        ulong u0 = x.u0;
        ulong u1 = x.u1;
        ulong u2 = x.u2;
        ulong u3 = x.u3;
        ulong u4;

        if (shift != 0)
        {
            int rs = 64 - shift;

            // Shift high-to-low so each source limb is still intact when used.
            u4 = u3 >> rs;
            u3 = (u3 << shift) | (u2 >> rs);
            u2 = (u2 << shift) | (u1 >> rs);
            u1 = (u1 << shift) | (u0 >> rs);
            u0 <<= shift;
        }
        else
        {
            u4 = 0;
        }

        // Start touching out params only after all input loads are done (alias-safe).
        Unsafe.SkipInit(out q);

        // Step j=2: q2 from (u4:u3:u2)
        {
            ulong qhat;
            ulong rhat;
            bool rcarry;

            if (u4 == v1n)
            {
                qhat = ulong.MaxValue;
                rhat = u3 + v1n;
                rcarry = rhat < u3;
            }
            else
            {
                qhat = UDivRem2By1(u4, vRecip, v1n, u3, out rhat);
                rcarry = false;
            }

            ulong hi = Multiply64(qhat, v0, out var lo);

            // Correct at most twice.
            if (!rcarry && (hi > rhat || (hi == rhat && lo > u2)))
            {
                qhat--;
                ulong lo2 = lo - v0;
                hi -= (lo < v0) ? 1UL : 0UL;
                lo = lo2;

                rhat += v1n;
                rcarry = rhat < v1n;

                if (!rcarry && (hi > rhat || (hi == rhat && lo > u2)))
                {
                    qhat--;
                    lo2 = lo - v0;
                    hi -= (lo < v0) ? 1UL : 0UL;
                    lo = lo2;
                }
            }

            // Subtract qhat*v from u2,u3,u4 (3 limbs).
            ulong borrow = (u2 < lo) ? 1UL : 0UL;
            u2 -= lo;

            ulong hi1 = Multiply64(qhat, v1n, out lo);
            ulong sum = lo + hi;
            hi = hi1 + ((sum < lo) ? 1UL : 0UL);

            ulong t = u3 - sum;
            ulong b = (u3 < sum) ? 1UL : 0UL;
            u3 = t - borrow;
            borrow = b | ((t < borrow) ? 1UL : 0UL);

            t = u4 - hi;
            b = (u4 < hi) ? 1UL : 0UL;
            borrow = b | ((t < borrow) ? 1UL : 0UL);

            if (borrow != 0)
            {
                // Add-back v and decrement qhat.
                ulong s0 = u2 + v0;
                ulong c = (s0 < u2) ? 1UL : 0UL;

                ulong s1 = u3 + v1n;
                s1 += c;

                u2 = s0;
                u3 = s1;

                qhat--;
            }
            Unsafe.AsRef(in q.u2) = qhat;
        }

        // Step j=1: q1 from (u3:u2:u1)
        {
            ulong qhat;
            ulong rhat;
            bool rcarry;

            if (u3 == v1n)
            {
                qhat = ulong.MaxValue;
                rhat = u2 + v1n;
                rcarry = rhat < u2;
            }
            else
            {
                qhat = UDivRem2By1(u3, vRecip, v1n, u2, out rhat);
                rcarry = false;
            }

            ulong hi = Multiply64(qhat, v0, out var lo);

            if (!rcarry && (hi > rhat || (hi == rhat && lo > u1)))
            {
                qhat--;
                ulong lo2 = lo - v0;
                hi -= (lo < v0) ? 1UL : 0UL;
                lo = lo2;

                rhat += v1n;
                rcarry = rhat < v1n;

                if (!rcarry && (hi > rhat || (hi == rhat && lo > u1)))
                {
                    qhat--;
                    lo2 = lo - v0;
                    hi -= (lo < v0) ? 1UL : 0UL;
                    lo = lo2;
                }
            }

            ulong borrow = (u1 < lo) ? 1UL : 0UL;
            u1 -= lo;

            ulong hi1 = Multiply64(qhat, v1n, out lo);
            ulong sum = lo + hi;
            hi = hi1 + ((sum < lo) ? 1UL : 0UL);

            ulong t = u2 - sum;
            ulong b = (u2 < sum) ? 1UL : 0UL;
            u2 = t - borrow;
            borrow = b | ((t < borrow) ? 1UL : 0UL);

            t = u3 - hi;
            b = (u3 < hi) ? 1UL : 0UL;
            borrow = b | ((t < borrow) ? 1UL : 0UL);

            if (borrow != 0)
            {
                ulong s0 = u1 + v0;
                ulong c = (s0 < u1) ? 1UL : 0UL;

                ulong s1 = u2 + v1n;
                s1 += c;

                u1 = s0;
                u2 = s1;

                qhat--;
            }
            Unsafe.AsRef(in q.u1) = qhat;
        }

        // Step j=0: q0 from (u2:u1:u0)
        {
            ulong qhat;
            ulong rhat;
            bool rcarry;

            if (u2 == v1n)
            {
                qhat = ulong.MaxValue;
                rhat = u1 + v1n;
                rcarry = rhat < u1;
            }
            else
            {
                qhat = UDivRem2By1(u2, vRecip, v1n, u1, out rhat);
                rcarry = false;
            }

            ulong hi = Multiply64(qhat, v0, out var lo);

            if (!rcarry && (hi > rhat || (hi == rhat && lo > u0)))
            {
                qhat--;
                ulong lo2 = lo - v0;
                hi -= (lo < v0) ? 1UL : 0UL;
                lo = lo2;

                rhat += v1n;
                rcarry = rhat < v1n;

                if (!rcarry && (hi > rhat || (hi == rhat && lo > u0)))
                {
                    qhat--;
                    lo2 = lo - v0;
                    hi -= (lo < v0) ? 1UL : 0UL;
                    lo = lo2;
                }
            }

            ulong borrow = (u0 < lo) ? 1UL : 0UL;
            u0 -= lo;

            ulong hi1 = Multiply64(qhat, v1n, out lo);
            ulong sum = lo + hi;
            hi = hi1 + ((sum < lo) ? 1UL : 0UL);

            ulong t = u1 - sum;
            ulong b = (u1 < sum) ? 1UL : 0UL;
            u1 = t - borrow;
            borrow = b | ((t < borrow) ? 1UL : 0UL);

            t = u2 - hi;
            b = (u2 < hi) ? 1UL : 0UL;
            borrow = b | ((t < borrow) ? 1UL : 0UL);

            if (borrow != 0)
            {
                ulong s0 = u0 + v0;
                ulong c = (s0 < u0) ? 1UL : 0UL;

                ulong s1 = u1 + v1n;
                s1 += c;

                u0 = s0;
                u1 = s1;

                qhat--;
            }

            Unsafe.AsRef(in q.u0) = qhat;
        }

        // q3 is always 0 for 256/128 here.
        Unsafe.AsRef(in q.u3) = 0;

        // Remainder (u0..u1 in normalised space) - unnormalise.
        Unsafe.SkipInit(out remainder);

        if (shift == 0)
        {
            Unsafe.AsRef(in remainder.u0) = u0;
            Unsafe.AsRef(in remainder.u1) = u1;
        }
        else
        {
            int rs = 64 - shift;
            Unsafe.AsRef(in remainder.u0) = (u0 >> shift) | (u1 << rs);
            Unsafe.AsRef(in remainder.u1) = u1 >> shift;
        }

        Unsafe.AsRef(in remainder.u2) = 0;
        Unsafe.AsRef(in remainder.u3) = 0;
    }

    // Knuth steps (unrolled)
    // qhat correction (at most twice in Knuth D)
    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong SubMul4(in UInt256 u, ref ulong u4, in UInt256 v, ulong q, out UInt256 rem)
    {
        ulong borrow = 0;

        ulong pHi = Multiply64(q, v.u0, out ulong pLo);
        ulong sum = pLo;
        ulong c2 = (sum < pLo) ? 1UL : 0UL;
        ulong carry = pHi + c2;
        var r0 = Sub(u.u0, sum, ref borrow);

        pHi = Multiply64(q, v.u1, out pLo);
        sum = pLo + carry;
        c2 = (sum < pLo) ? 1UL : 0UL;
        carry = pHi + c2;
        var r1 = Sub(u.u1, sum, ref borrow);

        pHi = Multiply64(q, v.u2, out pLo);
        sum = pLo + carry;
        c2 = (sum < pLo) ? 1UL : 0UL;
        carry = pHi + c2;
        var r2 = Sub(u.u2, sum, ref borrow);
        pHi = Multiply64(q, v.u3, out pLo);
        sum = pLo + carry;
        c2 = (sum < pLo) ? 1UL : 0UL;
        carry = pHi + c2;
        var r3 = Sub(u.u3, sum, ref borrow);

        u4 = Sub(u4, carry, ref borrow);

        rem = Create(r0, r1, r2, r3);
        return borrow;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong SubMul4(ref ulong u0, ref ulong u1, ref ulong u2, ref ulong u3, ref ulong u4, ulong v0, ulong v1, ulong v2, ulong v3, ulong q)
    {
        ulong borrow = 0;

        ulong pHi = Multiply64(q, v0, out ulong pLo);
        ulong sum = pLo;
        ulong c2 = (sum < pLo) ? 1UL : 0UL;
        ulong carry = pHi + c2;
        u0 = Sub(u0, sum, ref borrow);

        pHi = Multiply64(q, v1, out pLo);
        sum = pLo + carry;
        c2 = (sum < pLo) ? 1UL : 0UL;
        carry = pHi + c2;
        u1 = Sub(u1, sum, ref borrow);

        pHi = Multiply64(q, v2, out pLo);
        sum = pLo + carry;
        c2 = (sum < pLo) ? 1UL : 0UL;
        carry = pHi + c2;
        u2 = Sub(u2, sum, ref borrow);

        pHi = Multiply64(q, v3, out pLo);
        sum = pLo + carry;
        c2 = (sum < pLo) ? 1UL : 0UL;
        carry = pHi + c2;
        u3 = Sub(u3, sum, ref borrow);

        u4 = Sub(u4, carry, ref borrow);

        return borrow;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void AddBack3(ref ulong u0, ref ulong u1, ref ulong u2, ref ulong u3, ulong v0, ulong v1, ulong v2)
    {
        ulong sum = u0 + v0;
        ulong carry = (sum < u0) ? 1UL : 0UL;
        u0 = sum;

        sum = u1 + v1;
        ulong c = (sum < u1) ? 1UL : 0UL;
        sum += carry;
        carry = c | ((sum < carry) ? 1UL : 0UL);
        u1 = sum;

        sum = u2 + v2;
        c = (sum < u2) ? 1UL : 0UL;
        sum += carry;
        carry = c | ((sum < carry) ? 1UL : 0UL);
        u2 = sum;

        u3 += carry;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void AddBack4(ref ulong u0, ref ulong u1, ref ulong u2, ref ulong u3, ref ulong u4, ulong v0, ulong v1, ulong v2, ulong v3)
    {
        ulong c = 0;
        AddWithCarry(u0, v0, ref c, out u0);
        AddWithCarry(u1, v1, ref c, out u1);
        AddWithCarry(u2, v2, ref c, out u2);
        AddWithCarry(u3, v3, ref c, out u3);
        u4 += c;
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong MulHigh(ulong a, ulong b)
    {
        if (Bmi2.X64.IsSupported)
        {
            return Bmi2.X64.MultiplyNoFlags(a, b);
        }
        else if (ArmBase.Arm64.IsSupported)
        {
            return ArmBase.Arm64.MultiplyHigh(a, b);
        }
        else
        {
            return Math.BigMul(a, b, out _);
        }
    }
}
