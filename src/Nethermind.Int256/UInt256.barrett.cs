// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System.Runtime.CompilerServices;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    // Reduces hi:lo modulo a modulus with m.u3 != 0. Both builds reduce the moduli below by Barrett reduction with
    // their reciprocals as constants.
    private static partial void Remainder512ByFullModulus(in UInt256 lo, in UInt256 hi, in UInt256 m, out UInt256 rem);

    // A full-width modulus m (m.u3 != 0) and mu = floor((2^512 - 1) / m), 2^256 < mu < 2^320, as constants, so each
    // reduction is compiled for its modulus. Internal so the tests can supply a deliberately wrong mu.
    internal interface IBarrettModulus
    {
        static abstract ulong M0 { get; }
        static abstract ulong M1 { get; }
        static abstract ulong M2 { get; }
        static abstract ulong M3 { get; }
        static abstract ulong Mu0 { get; }
        static abstract ulong Mu1 { get; }
        static abstract ulong Mu2 { get; }
        static abstract ulong Mu3 { get; }
        static abstract ulong Mu4 { get; }
    }

    // BN254 (alt_bn128) scalar field r: MiMC and Poseidon hashing (Tornado Cash, Semaphore), SNARK verifiers.
    internal readonly struct Bn254R : IShortBarrettModulus
    {
        public static int Bits => 254;
        public static ulong Nu0 => 0x620703A6BE1DE925UL;
        public static ulong Nu1 => 0x7144852009E880AEUL;
        public static ulong Nu2 => 0xAB074A5868073014UL;
        public static ulong Nu3 => 0x54A47462623A04A7UL;
        public const ulong Top = 0x30644E72E131A029UL;
        public static ulong M0 => 0x43E1F593F0000001UL;
        public static ulong M1 => 0x2833E84879B97091UL;
        public static ulong M2 => 0xB85045B68181585DUL;
        public static ulong M3 => Top;
        public static ulong Mu0 => 0x20703A6BE1DE9259UL;
        public static ulong Mu1 => 0x144852009E880AE6UL;
        public static ulong Mu2 => 0xB074A58680730147UL;
        public static ulong Mu3 => 0x4A47462623A04A7AUL;
        public static ulong Mu4 => 0x0000000000000005UL;
    }

    // BN254 (alt_bn128) base field p: SNARK verifiers.
    internal readonly struct Bn254P : IShortBarrettModulus
    {
        public static int Bits => 254;
        public static ulong Nu0 => 0x6F3AED8A19BF90E5UL;
        public static ulong Nu1 => 0xAE965E1767CD4C08UL;
        public static ulong Nu2 => 0xAB074A5868073013UL;
        public static ulong Nu3 => 0x54A47462623A04A7UL;
        public const ulong Top = 0x30644E72E131A029UL;
        public static ulong M0 => 0x3C208C16D87CFD47UL;
        public static ulong M1 => 0x97816A916871CA8DUL;
        public static ulong M2 => 0xB85045B68181585DUL;
        public static ulong M3 => Top;
        public static ulong Mu0 => 0xF3AED8A19BF90E51UL;
        public static ulong Mu1 => 0xE965E1767CD4C086UL;
        public static ulong Mu2 => 0xB074A5868073013AUL;
        public static ulong Mu3 => 0x4A47462623A04A7AUL;
        public static ulong Mu4 => 0x0000000000000005UL;
    }

    // secp256k1 group order n.
    internal readonly struct Secp256k1N : IBarrettModulus
    {
        public const ulong Top = 0xFFFFFFFFFFFFFFFFUL;
        public static ulong M0 => 0xBFD25E8CD0364141UL;
        public static ulong M1 => 0xBAAEDCE6AF48A03BUL;
        public static ulong M2 => 0xFFFFFFFFFFFFFFFEUL;
        public static ulong M3 => Top;
        public static ulong Mu0 => 0x402DA1732FC9BEC0UL;
        public static ulong Mu1 => 0x4551231950B75FC4UL;
        public static ulong Mu2 => 0x0000000000000001UL;
        public static ulong Mu3 => 0x0000000000000000UL;
        public static ulong Mu4 => 0x0000000000000001UL;
    }

    // P-256 (secp256r1) base field p: WebAuthn and passkey verifiers.
    internal readonly struct P256P : IBarrettModulus
    {
        public const ulong Top = 0xFFFFFFFF00000001UL;
        public static ulong M0 => 0xFFFFFFFFFFFFFFFFUL;
        public static ulong M1 => 0x00000000FFFFFFFFUL;
        public static ulong M2 => 0x0000000000000000UL;
        public static ulong M3 => Top;
        public static ulong Mu0 => 0x0000000000000003UL;
        public static ulong Mu1 => 0xFFFFFFFEFFFFFFFFUL;
        public static ulong Mu2 => 0xFFFFFFFEFFFFFFFEUL;
        public static ulong Mu3 => 0x00000000FFFFFFFFUL;
        public static ulong Mu4 => 0x0000000000000001UL;
    }

    // P-256 (secp256r1) group order n.
    internal readonly struct P256N : IBarrettModulus
    {
        public const ulong Top = 0xFFFFFFFF00000000UL;
        public static ulong M0 => 0xF3B9CAC2FC632551UL;
        public static ulong M1 => 0xBCE6FAADA7179E84UL;
        public static ulong M2 => 0xFFFFFFFFFFFFFFFFUL;
        public static ulong M3 => Top;
        public static ulong Mu0 => 0x012FFD85EEDF9BFEUL;
        public static ulong Mu1 => 0x43190552DF1A6C21UL;
        public static ulong Mu2 => 0xFFFFFFFEFFFFFFFFUL;
        public static ulong Mu3 => 0x00000000FFFFFFFFUL;
        public static ulong Mu4 => 0x0000000000000001UL;
    }

    internal interface IShortBarrettModulus : IBarrettModulus
    {
        static abstract int Bits { get; }
        static abstract ulong Nu0 { get; }
        static abstract ulong Nu1 { get; }
        static abstract ulong Nu2 { get; }
        static abstract ulong Nu3 { get; }
    }

    internal readonly struct Prime251 : IShortBarrettModulus
    {
        public static int Bits => 252;
        public static ulong Nu0 => 0x000000028C81FFFBUL;
        public static ulong Nu1 => 0xFFFFFFFFFECCF000UL;
        public static ulong Nu2 => 0x000000000000907FUL;
        public static ulong Nu3 => 0x1FFFFFFFFFFFFFBCUL;
        public const ulong Top = 0x0800000000000011UL;
        public static ulong M0 => 0x0000000000000001UL;
        public static ulong M1 => 0x0000000000000000UL;
        public static ulong M2 => 0x0000000000000000UL;
        public static ulong M3 => Top;
        public static ulong Mu0 => 0x0000028C81FFFBFFUL;
        public static ulong Mu1 => 0xFFFFFFFECCF00000UL;
        public static ulong Mu2 => 0x0000000000907FFFUL;
        public static ulong Mu3 => 0xFFFFFFFFFFFFBC00UL;
        public static ulong Mu4 => 0x000000000000001FUL;
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.NoInlining)]
    internal static void Remainder512ByPseudoMersenne(in UInt256 lo, in UInt256 hi, ulong c, out UInt256 rem)
    {
        ulong h0 = Multiply64(hi.u0, c, out ulong l0);
        ulong h1 = Multiply64(hi.u1, c, out ulong l1);
        ulong h2 = Multiply64(hi.u2, c, out ulong l2);
        ulong h3 = Multiply64(hi.u3, c, out ulong l3);

        ulong carry = 0;
        AddWithCarry(lo.u0, l0, ref carry, out ulong r0);
        AddWithCarry(lo.u1, l1, ref carry, out ulong r1);
        AddWithCarry(lo.u2, l2, ref carry, out ulong r2);
        AddWithCarry(lo.u3, l3, ref carry, out ulong r3);
        ulong top = h3 + carry;
        carry = 0;
        AddWithCarry(r1, h0, ref carry, out r1);
        AddWithCarry(r2, h1, ref carry, out r2);
        AddWithCarry(r3, h2, ref carry, out r3);
        top += carry;

        ulong th = Multiply64(top, c, out ulong tl);
        carry = 0;
        AddWithCarry(r0, tl, ref carry, out r0);
        AddWithCarry(r1, th, ref carry, out r1);
        AddWithCarry(r2, 0, ref carry, out r2);
        AddWithCarry(r3, 0, ref carry, out r3);
        if (carry != 0)
        {
            carry = 0;
            AddWithCarry(r0, c, ref carry, out r0);
            AddWithCarry(r1, 0, ref carry, out r1);
            AddWithCarry(r2, 0, ref carry, out r2);
            r3 += carry;
        }

        carry = 0;
        AddWithCarry(r0, c, ref carry, out ulong s0);
        AddWithCarry(r1, 0, ref carry, out ulong s1);
        AddWithCarry(r2, 0, ref carry, out ulong s2);
        AddWithCarry(r3, 0, ref carry, out ulong s3);
        if (carry != 0)
        {
            Store4(out rem, s0, s1, s2, s3);
            return;
        }

        Store4(out rem, r0, r1, r2, r3);
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    internal static void Remainder512ByShortBarrettOrDivide<TModulus>(in UInt256 lo, in UInt256 hi, in UInt256 m, out UInt256 rem)
        where TModulus : struct, IShortBarrettModulus
    {
        if ((hi.u3 >> (2 * TModulus.Bits - 448)) != 0)
        {
            Remainder512ByBarrettOrDivide<TModulus>(in lo, in hi, in m, out rem);
            return;
        }

        if (Remainder512ByShortBarrett<TModulus>(in lo, in hi, out rem) < 0) Remainder512By256Bits(in lo, in hi, in m, out rem);
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.NoInlining)]
    internal static int Remainder512ByShortBarrett<TModulus>(in UInt256 lo, in UInt256 hi, out UInt256 rem)
        where TModulus : struct, IShortBarrettModulus
    {
        int s = TModulus.Bits - 193;
        ulong x3 = lo.u3, x4 = hi.u0, x5 = hi.u1, x6 = hi.u2, x7 = hi.u3;
        ulong a0 = (x3 >> s) | (x4 << (64 - s));
        ulong a1 = (x4 >> s) | (x5 << (64 - s));
        ulong a2 = (x5 >> s) | (x6 << (64 - s));
        ulong a3 = (x6 >> s) | (x7 << (64 - s));

        ulong c3 = 0, k3 = 0, c4 = 0, k4 = 0, c5 = 0, k5 = 0, c6 = 0, k6 = 0, c7 = 0, k7 = 0;
        c3 = AddAndCountCarry(c3, MulHigh(a0, TModulus.Nu2), ref k3);
        c3 = AddAndCountCarry(c3, MulHigh(a1, TModulus.Nu1), ref k3);
        c3 = AddAndCountCarry(c3, MulHigh(a2, TModulus.Nu0), ref k3);

        MultiplyAccumulate(a0, TModulus.Nu3, ref c3, ref k3, ref c4, ref k4);
        MultiplyAccumulate(a1, TModulus.Nu2, ref c3, ref k3, ref c4, ref k4);
        MultiplyAccumulate(a2, TModulus.Nu1, ref c3, ref k3, ref c4, ref k4);
        MultiplyAccumulate(a3, TModulus.Nu0, ref c3, ref k3, ref c4, ref k4);

        MultiplyAccumulate(a1, TModulus.Nu3, ref c4, ref k4, ref c5, ref k5);
        MultiplyAccumulate(a2, TModulus.Nu2, ref c4, ref k4, ref c5, ref k5);
        MultiplyAccumulate(a3, TModulus.Nu1, ref c4, ref k4, ref c5, ref k5);

        MultiplyAccumulate(a2, TModulus.Nu3, ref c5, ref k5, ref c6, ref k6);
        MultiplyAccumulate(a3, TModulus.Nu2, ref c5, ref k5, ref c6, ref k6);

        MultiplyAccumulate(a3, TModulus.Nu3, ref c6, ref k6, ref c7, ref k7);

        c4 = AddAndCountCarry(c4, k3, ref k4);
        c5 = AddAndCountCarry(c5, k4, ref k5);
        c6 = AddAndCountCarry(c6, k5, ref k6);
        c7 += k6;

        int r = TModulus.Bits - 191;
        ulong q0 = (c3 >> r) | (c4 << (64 - r));
        ulong q1 = (c4 >> r) | (c5 << (64 - r));
        ulong q2 = (c5 >> r) | (c6 << (64 - r));
        ulong q3 = (c6 >> r) | (c7 << (64 - r));

        ulong p0 = 0, j0 = 0, p1 = 0, j1 = 0, p2 = 0, j2 = 0, p3 = 0, j3 = 0;
        MultiplyAccumulate(q0, TModulus.M0, ref p0, ref j0, ref p1, ref j1);
        MultiplyAccumulate(q0, TModulus.M1, ref p1, ref j1, ref p2, ref j2);
        MultiplyAccumulate(q1, TModulus.M0, ref p1, ref j1, ref p2, ref j2);
        MultiplyAccumulate(q0, TModulus.M2, ref p2, ref j2, ref p3, ref j3);
        MultiplyAccumulate(q1, TModulus.M1, ref p2, ref j2, ref p3, ref j3);
        MultiplyAccumulate(q2, TModulus.M0, ref p2, ref j2, ref p3, ref j3);
        p2 = AddAndCountCarry(p2, j1, ref j2);
        p3 += j2 + q0 * TModulus.M3 + q1 * TModulus.M2 + q2 * TModulus.M1 + q3 * TModulus.M0;

        ulong borrow = 0;
        ulong r0 = Sub(lo.u0, p0, ref borrow);
        ulong r1 = Sub(lo.u1, p1, ref borrow);
        ulong r2 = Sub(lo.u2, p2, ref borrow);
        ulong r3 = x3 - p3 - borrow;

        int passes = 0;
        while (true)
        {
            borrow = 0;
            ulong d0 = Sub(r0, TModulus.M0, ref borrow);
            ulong d1 = Sub(r1, TModulus.M1, ref borrow);
            ulong d2 = Sub(r2, TModulus.M2, ref borrow);
            ulong d3 = Sub(r3, TModulus.M3, ref borrow);
            if (borrow != 0) break;

            if (++passes > 3)
            {
                Unsafe.SkipInit(out rem);
                return -1;
            }

            r0 = d0; r1 = d1; r2 = d2; r3 = d3;
        }

        Store4(out rem, r0, r1, r2, r3);
        return passes;

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        static void MultiplyAccumulate(ulong a, ulong b, ref ulong s, ref ulong k, ref ulong t, ref ulong j)
        {
            if (b == 0) return;
            if (b == 1)
            {
                s = AddAndCountCarry(s, a, ref k);
                return;
            }

            ulong high = Multiply64(a, b, out ulong low);
            s = AddAndCountCarry(s, low, ref k);
            t = AddAndCountCarry(t, high, ref j);
        }
    }

    // hi:lo mod m for m equal to the modulus of TModulus: the reduction, or the division if its correction overran.
    // rem may share storage with m: the reduction writes rem only on success, and the division reads m first.
    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    internal static void Remainder512ByBarrettOrDivide<TModulus>(in UInt256 lo, in UInt256 hi, in UInt256 m, out UInt256 rem)
        where TModulus : struct, IBarrettModulus
    {
        if (Remainder512ByBarrett<TModulus>(in lo, in hi, out rem) < 0) Remainder512By256Bits(in lo, in hi, in m, out rem);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    internal static bool IsModulus<TModulus>(in UInt256 m) where TModulus : struct, IBarrettModulus
        => ((m.u0 ^ TModulus.M0) | (m.u1 ^ TModulus.M1) | (m.u2 ^ TModulus.M2) | (m.u3 ^ TModulus.M3)) == 0;

    // Barrett reduction (HAC 14.42) of x = hi:lo < 2^512 by the modulus m of TModulus.
    // q1 = x >> 192; qhat = (q1 * mu) >> 320 from the partial products in columns 3..9 only. The
    // dropped products (columns 0..2) sum to less than 4 * 2^256, so qhat is at most one below the
    // exact Barrett quotient, which is at most two below floor(x / m). Hence 0 <= x - qhat * m < 4m
    // < 2^320: the difference is computed mod 2^320 and finished by subtracting m while it is >= m.
    // Products are taken by diagonal; each adds its low half to the column of its diagonal and its high
    // half to the next column, and the carries of a column are counted apart from its sum, so no add
    // waits on a carry; one add per finished column ripples the counted carries upwards.
    // Returns the number of subtractions (at most one for the moduli above), or -1 without writing rem
    // when three did not suffice, which only a wrong estimate could cause; the caller then divides. So an
    // estimate that misses floor(x / m) by less than 2^320 / m - 4 (over 2^64) costs speed, never the result.
    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.NoInlining)]
    internal static int Remainder512ByBarrett<TModulus>(in UInt256 lo, in UInt256 hi, out UInt256 rem)
        where TModulus : struct, IBarrettModulus
    {
        ulong x3 = lo.u3, x4 = hi.u0, x5 = hi.u1, x6 = hi.u2, x7 = hi.u3;

        // q1 * mu, q1 = (x3, x4, x5, x6, x7). (s, k) is the column of the current diagonal, (t, j) the next one.
        ulong s = 0, k = 0, t = 0, j = 0;
        MultiplyAccumulate(x3, TModulus.Mu3, ref s, ref k, ref t, ref j);
        MultiplyAccumulate(x4, TModulus.Mu2, ref s, ref k, ref t, ref j);
        MultiplyAccumulate(x5, TModulus.Mu1, ref s, ref k, ref t, ref j);
        MultiplyAccumulate(x6, TModulus.Mu0, ref s, ref k, ref t, ref j);
        ulong carry = k;
        s = t; k = j; t = 0; j = 0;

        MultiplyAccumulate(x3, TModulus.Mu4, ref s, ref k, ref t, ref j);
        MultiplyAccumulate(x4, TModulus.Mu3, ref s, ref k, ref t, ref j);
        MultiplyAccumulate(x5, TModulus.Mu2, ref s, ref k, ref t, ref j);
        MultiplyAccumulate(x6, TModulus.Mu1, ref s, ref k, ref t, ref j);
        MultiplyAccumulate(x7, TModulus.Mu0, ref s, ref k, ref t, ref j);
        AddAndCountCarry(s, carry, ref k);
        carry = k;
        s = t; k = j; t = 0; j = 0;

        MultiplyAccumulate(x4, TModulus.Mu4, ref s, ref k, ref t, ref j);
        MultiplyAccumulate(x5, TModulus.Mu3, ref s, ref k, ref t, ref j);
        MultiplyAccumulate(x6, TModulus.Mu2, ref s, ref k, ref t, ref j);
        MultiplyAccumulate(x7, TModulus.Mu1, ref s, ref k, ref t, ref j);
        ulong q0 = AddAndCountCarry(s, carry, ref k);
        carry = k;
        s = t; k = j; t = 0; j = 0;

        MultiplyAccumulate(x5, TModulus.Mu4, ref s, ref k, ref t, ref j);
        MultiplyAccumulate(x6, TModulus.Mu3, ref s, ref k, ref t, ref j);
        MultiplyAccumulate(x7, TModulus.Mu2, ref s, ref k, ref t, ref j);
        ulong q1 = AddAndCountCarry(s, carry, ref k);
        carry = k;
        s = t; k = j; t = 0; j = 0;

        MultiplyAccumulate(x6, TModulus.Mu4, ref s, ref k, ref t, ref j);
        MultiplyAccumulate(x7, TModulus.Mu3, ref s, ref k, ref t, ref j);
        ulong q2 = AddAndCountCarry(s, carry, ref k);
        carry = k;
        s = t; k = j; t = 0; j = 0;

        MultiplyAccumulate(x7, TModulus.Mu4, ref s, ref k, ref t, ref j);
        ulong q3 = AddAndCountCarry(s, carry, ref k);
        // The product is below 2^640, so the top column cannot carry out.
        ulong q4 = t + k;

        // (qhat * m) mod 2^320 the same way; the top column needs only the low halves.
        s = 0; k = 0; t = 0; j = 0;
        MultiplyAccumulate(q0, TModulus.M0, ref s, ref k, ref t, ref j);
        ulong p0 = s;
        s = t; k = j; t = 0; j = 0;

        MultiplyAccumulate(q0, TModulus.M1, ref s, ref k, ref t, ref j);
        MultiplyAccumulate(q1, TModulus.M0, ref s, ref k, ref t, ref j);
        ulong p1 = s;
        carry = k;
        s = t; k = j; t = 0; j = 0;

        MultiplyAccumulate(q0, TModulus.M2, ref s, ref k, ref t, ref j);
        MultiplyAccumulate(q1, TModulus.M1, ref s, ref k, ref t, ref j);
        MultiplyAccumulate(q2, TModulus.M0, ref s, ref k, ref t, ref j);
        ulong p2 = AddAndCountCarry(s, carry, ref k);
        carry = k;
        s = t; k = j; t = 0; j = 0;

        MultiplyAccumulate(q0, TModulus.M3, ref s, ref k, ref t, ref j);
        MultiplyAccumulate(q1, TModulus.M2, ref s, ref k, ref t, ref j);
        MultiplyAccumulate(q2, TModulus.M1, ref s, ref k, ref t, ref j);
        MultiplyAccumulate(q3, TModulus.M0, ref s, ref k, ref t, ref j);
        ulong p3 = AddAndCountCarry(s, carry, ref k);
        ulong p4 = t + k + q1 * TModulus.M3 + q2 * TModulus.M2 + q3 * TModulus.M1 + q4 * TModulus.M0;

        // r = (x mod 2^320) - (qhat * m mod 2^320), mod 2^320.
        ulong borrow = 0;
        ulong r0 = Sub(lo.u0, p0, ref borrow);
        ulong r1 = Sub(lo.u1, p1, ref borrow);
        ulong r2 = Sub(lo.u2, p2, ref borrow);
        ulong r3 = Sub(x3, p3, ref borrow);
        ulong r4 = x4 - p4 - borrow;

        int passes = 0;
        while (r4 != 0 || !LessThanModulus(r0, r1, r2, r3))
        {
            if (++passes > 3)
            {
                Unsafe.SkipInit(out rem);
                return -1;
            }

            borrow = 0;
            r0 = Sub(r0, TModulus.M0, ref borrow);
            r1 = Sub(r1, TModulus.M1, ref borrow);
            r2 = Sub(r2, TModulus.M2, ref borrow);
            r3 = Sub(r3, TModulus.M3, ref borrow);
            r4 -= borrow;
        }

        Store4(out rem, r0, r1, r2, r3);
        return passes;

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        static void MultiplyAccumulate(ulong a, ulong b, ref ulong s, ref ulong k, ref ulong t, ref ulong j)
        {
            // Zero and one limbs of the constants need no multiplication.
            if (b == 0) return;
            if (b == 1)
            {
                s = AddAndCountCarry(s, a, ref k);
                return;
            }

            ulong high = Multiply64(a, b, out ulong low);
            s = AddAndCountCarry(s, low, ref k);
            t = AddAndCountCarry(t, high, ref j);
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        static bool LessThanModulus(ulong a0, ulong a1, ulong a2, ulong a3)
        {
            ulong borrow = 0;
            Sub(a0, TModulus.M0, ref borrow);
            Sub(a1, TModulus.M1, ref borrow);
            Sub(a2, TModulus.M2, ref borrow);
            Sub(a3, TModulus.M3, ref borrow);
            return borrow != 0;
        }
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void Remainder512ByKnownModulus(in UInt256 lo, in UInt256 hi, in UInt256 m, out UInt256 rem)
    {
        // BN254 r and p share their top two limbs, as do secp256k1 p and n.
        switch (m.u3)
        {
            case Bn254R.Top:
                if (IsModulus<Bn254R>(in m))
                {
                    Remainder512ByShortBarrettOrDivide<Bn254R>(in lo, in hi, in m, out rem);
                    return;
                }

                if (IsModulus<Bn254P>(in m))
                {
                    Remainder512ByShortBarrettOrDivide<Bn254P>(in lo, in hi, in m, out rem);
                    return;
                }

                break;
            case Secp256k1N.Top:
                if ((m.u1 & m.u2) == ulong.MaxValue && m.u0 > 1)
                {
                    Remainder512ByPseudoMersenne(in lo, in hi, 0UL - m.u0, out rem);
                    return;
                }

                if (IsModulus<Secp256k1N>(in m))
                {
                    Remainder512ByBarrettOrDivide<Secp256k1N>(in lo, in hi, in m, out rem);
                    return;
                }

                break;
            case P256P.Top:
                if (IsModulus<P256P>(in m))
                {
                    Remainder512ByBarrettOrDivide<P256P>(in lo, in hi, in m, out rem);
                    return;
                }

                break;
            case Prime251.Top:
                if (IsModulus<Prime251>(in m))
                {
                    Remainder512ByShortBarrettOrDivide<Prime251>(in lo, in hi, in m, out rem);
                    return;
                }

                break;
            case P256N.Top:
                if (IsModulus<P256N>(in m))
                {
                    Remainder512ByBarrettOrDivide<P256N>(in lo, in hi, in m, out rem);
                    return;
                }

                break;
        }

        Remainder512By256Bits(in lo, in hi, in m, out rem);
    }
}
