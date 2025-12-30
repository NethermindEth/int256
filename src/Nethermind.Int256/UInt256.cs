// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

#pragma warning disable SYSLIB5004 // DivRem is [Experimental] as of net10

using System;
using System.Buffers.Binary;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Globalization;
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
        ulong result = x + y + carry;
        // both msb bits are 1 or one of them is 1 and we had carry from lower bits
        carry = ((x & y) | ((x | y) & (~result))) >> 63;
        sum = result;
    }

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

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static int Len64(ulong x) => 64 - BitOperations.LeadingZeroCount(x);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static int LeadingZeros(ulong x) => BitOperations.LeadingZeroCount(x);

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
        // #if DEBUG
        //             Debug.Assert((BigInteger)res == ((BigInteger)a - (BigInteger)b + ((BigInteger)1 << 256)) % ((BigInteger)1 << 256));
        // #endif
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

        if (false && Avx512F.IsSupported && Avx512DQ.IsSupported && Avx512DQ.VL.IsSupported)
        {
            // Recent optimizations have made scalar faster
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
            ? 192 + Len64(u3)
            : u2 != 0
                ? 128 + Len64(u2)
                : u1 != 0
                    ? 64 + Len64(u1)
                    : Len64(u0);

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

        if (!Unsafe.IsNullRef(in q))
        {
            ulong u0 = q.u0, u1 = q.u1, u2 = q.u2, u3 = q.u3;
            Remainder256By128Bits(u0, u1, u2, u3, m0, m1, out ulong r0, out ulong r1);
            res = new UInt256(r0, r1, 0, 0);
            return;
        }
        {
            ulong u0 = x.u0, u1 = x.u1, u2 = x.u2, u3 = x.u3;
            Remainder256By128Bits(u0, u1, u2, u3, m0, m1, out ulong x0, out ulong x1);
            u0 = y.u0; u1 = y.u1; u2 = y.u2; u3 = y.u3;
            Remainder256By128Bits(u0, u1, u2, u3, m0, m1, out ulong y0, out ulong y1);

            Mul128(x0, x1, y0, y1, out ulong p0, out ulong p1, out ulong p2, out ulong p3);
            Remainder256By128Bits(p0, p1, p2, p3, m0, m1, out ulong rr0, out ulong rr1);

            res = new UInt256(rr0, rr1, 0, 0);
        }
    }

    [StructLayout(LayoutKind.Sequential)]
    private struct ULong5
    {
        public ulong w0, w1, w2, w3, w4;
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void Remainder256By128Bits(ulong u0, ulong u1, ulong u2, ulong u3, ulong d0, ulong d1, out ulong r0, out ulong r1)
    {
        // d1 != 0 (caller guarantees 128-bit modulus)
        int shift = LeadingZeros(d1);

        // If numerator < 2^64, remainder is numerator (since divisor >= 2^64).
        if ((u1 | u2 | u3) == 0)
        {
            r0 = u0;
            r1 = 0;
            return;
        }

        ulong nd0, nd1;

        Unsafe.SkipInit(out ULong5 un);

        if (shift == 0)
        {
            // Normalised == original
            un.w0 = u0; un.w1 = u1; un.w2 = u2; un.w3 = u3; un.w4 = 0;
            nd0 = d0; nd1 = d1;
        }
        else
        {
            int rshift = 64 - shift;

            un.w4 = u3 >> rshift;
            un.w3 = (u3 << shift) | (u2 >> rshift);
            un.w2 = (u2 << shift) | (u1 >> rshift);
            un.w1 = (u1 << shift) | (u0 >> rshift);
            un.w0 = u0 << shift;

            nd0 = d0 << shift;
            nd1 = (d1 << shift) | (d0 >> rshift);
        }

        // Determine uLen (significant limbs of original numerator).
        int uLen = u3 != 0 ? 4 : (u2 != 0 ? 3 : 2); // we already handled uLen 1 above

        // dLen is 2.
        int m = uLen - 2;

        ref ulong un0 = ref un.w0;

        // Knuth remainder-only for dLen=2 with corrected qhat.
        ulong dh = nd1;
        ulong dl = nd0; // d[n-2]
        ulong reciprocal = X86Base.X64.IsSupported ? 0 : Reciprocal2By1(dh);

        for (int j = m; j >= 0; j--)
        {
            ref ulong uJ = ref Unsafe.Add(ref un0, j);

            ulong u4 = Unsafe.Add(ref uJ, 2);
            ulong u5 = Unsafe.Add(ref uJ, 1);
            ulong u6 = uJ;

            ulong qhat = X86Base.X64.IsSupported ? EstimateQhatX86Base(u4, u5, u6, dh, dl) : EstimateQhat(u4, u5, u6, dh, dl, reciprocal);

            ulong borrow = SubMulTo2(ref uJ, nd0, nd1, qhat);
            ulong newU2 = u4 - borrow;
            Unsafe.Add(ref uJ, 2) = newU2;

            if (u4 < borrow)
            {
                newU2 += AddTo2(ref uJ, nd0, nd1);
                Unsafe.Add(ref uJ, 2) = newU2;
            }
        }

        // Denormalise remainder from un[0..1].
        if (shift == 0)
        {
            r0 = un.w0;
            r1 = un.w1;
            return;
        }
        else
        {
            int rshift = 64 - shift;
            r0 = (un.w0 >> shift) | (un.w1 << rshift);
            r1 = (un.w1 >> shift);
        }
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
    private static ulong SubMulTo2(ref ulong x0, ulong y0, ulong y1, ulong mul)
    {
        // Compute y * mul as 192-bit value: [pl0, mid, high]
        ulong ph0 = Multiply64(y0, mul, out ulong pl0);
        ulong ph1 = Multiply64(y1, mul, out ulong pl1);
    
        // Accumulate middle: ph0 + pl1 with carry to high
        ulong mid = ph0 + pl1;
        ulong high = ph1 + (mid < ph0 ? 1UL : 0UL);
    
        // Subtract [pl0, mid, high] from [x0, x1, implicit_x2]
        ref ulong x1 = ref Unsafe.Add(ref x0, 1);
    
        ulong r0 = x0 - pl0;
        ulong b0 = x0 < pl0 ? 1UL : 0UL;  // Simple comparison - JIT knows this pattern
    
        ulong t1 = x1 - mid;
        ulong b1 = x1 < mid ? 1UL : 0UL;
        ulong r1 = t1 - b0;
        b1 += r1 > t1 ? 1UL : 0UL;  // Borrow from subtracting b0
    
        x0 = r0;
        x1 = r1;
    
        return high + b1;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong AddTo2(ref ulong x0, ulong y0, ulong y1)
    {
        ref ulong x1 = ref Unsafe.Add(ref x0, 1);

        ulong carry = 0;
        AddWithCarry(x0, y0, ref carry, out x0);
        AddWithCarry(x1, y1, ref carry, out x1);
        return carry;
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

            ulong borrow = SubMulTo2(ref uJ, d0, d1, qhat);
            ulong newU2 = u2 - borrow;
            Unsafe.Add(ref uJ, 2) = newU2;

            if (u2 < borrow)
            {
                newU2 += AddTo2(ref uJ, d0, d1);
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
            return u0 == other && u1 == 0 && u2 == 0 && u3 == 0;
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
            return u0 == other && u1 == 0 && u2 == 0 && u3 == 0;
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

    public const int Len = 4;

    [DoesNotReturn, StackTraceHidden]
    private static void ThrowDivideByZeroException() => throw new DivideByZeroException();

    [DoesNotReturn]
    private static void ThrowOverflowException(string message) => throw new OverflowException(message);

    [DoesNotReturn]
    private static void ThrowNotSupportedException() => throw new NotSupportedException();

    [DoesNotReturn]
    private static ulong ThrowIndexOutOfRangeException() => throw new IndexOutOfRangeException();

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
}
