// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System.Runtime.CompilerServices;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    // Reduces hi:lo modulo a modulus with m.u3 != 0. The standard build reduces the moduli below by Barrett
    // reduction with their reciprocals as constants; the zkEVM build divides.
    private static partial void Remainder512ByFullModulus(in UInt256 lo, in UInt256 hi, in UInt256 m, out UInt256 rem);

    // A full-width modulus m (m.u3 != 0) and mu = floor((2^512 - 1) / m), 2^256 < mu < 2^320, as constants, so each
    // reduction is compiled for its modulus.
    private interface IBarrettModulus
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
    private readonly struct Bn254R : IBarrettModulus
    {
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
    private readonly struct Bn254P : IBarrettModulus
    {
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

    // secp256k1 base field p.
    private readonly struct Secp256k1P : IBarrettModulus
    {
        public const ulong Top = 0xFFFFFFFFFFFFFFFFUL;
        public static ulong M0 => 0xFFFFFFFEFFFFFC2FUL;
        public static ulong M1 => 0xFFFFFFFFFFFFFFFFUL;
        public static ulong M2 => 0xFFFFFFFFFFFFFFFFUL;
        public static ulong M3 => Top;
        public static ulong Mu0 => 0x00000001000003D1UL;
        public static ulong Mu1 => 0x0000000000000000UL;
        public static ulong Mu2 => 0x0000000000000000UL;
        public static ulong Mu3 => 0x0000000000000000UL;
        public static ulong Mu4 => 0x0000000000000001UL;
    }

    // secp256k1 group order n.
    private readonly struct Secp256k1N : IBarrettModulus
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
    private readonly struct P256P : IBarrettModulus
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
    private readonly struct P256N : IBarrettModulus
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
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool IsModulus<TModulus>(in UInt256 m) where TModulus : struct, IBarrettModulus
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
    // when three did not suffice, which only a wrong estimate could cause: the caller then divides, so
    // the estimate decides the speed and never the result.
    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static int Remainder512ByBarrett<TModulus>(in UInt256 lo, in UInt256 hi, out UInt256 rem)
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
}
