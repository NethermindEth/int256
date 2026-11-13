using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.X86;

namespace Nethermind.Int256;

// Mirrors the production op_LessThan call graph and CompareTo; each case symbol mutates one reached body.
public readonly partial struct UInt256
{
    public static bool operator <(in UInt256 a, in UInt256 b) => GreaterThan(in b, in a);
    public static bool operator >(in UInt256 a, in UInt256 b) => LessThanOperator(in b, in a);

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

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool LessThan(in UInt256 a, in UInt256 b)
    {
        if (Avx512F.VL.IsSupported && Avx512DQ.IsSupported)
        {
            return LessThanAvx2(in a, in b);
        }

        if (!Avx2.IsSupported && Vector256.IsHardwareAccelerated)
        {
            return LessThanVector256(in a, in b);
        }

        return LessThanScalar(in a, in b);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    internal static bool LessThanScalar(in UInt256 a, in UInt256 b)
    {
#if COMPARISON_ALTERNATIVE
        if (a.u3 < b.u3) return true;
        if (b.u3 < a.u3) return false;
        if (a.u2 < b.u2) return true;
        if (b.u2 < a.u2) return false;
        if (a.u1 < b.u1) return true;
        if (b.u1 < a.u1) return false;
        return a.u0 < b.u0;
#elif COMPARISON_LOW_FIRST
        if (a.u0 != b.u0)
            return a.u0 < b.u0;
        if (a.u2 != b.u2)
            return a.u2 < b.u2;
        if (a.u1 != b.u1)
            return a.u1 < b.u1;
        return a.u3 < b.u3;
#elif COMPARISON_SIGNED
        if (a.u3 != b.u3)
            return (long)a.u3 < (long)b.u3;
        if (a.u2 != b.u2)
            return a.u2 < b.u2;
        if (a.u1 != b.u1)
            return a.u1 < b.u1;
        return a.u0 < b.u0;
#else
        if (a.u3 != b.u3)
            return a.u3 < b.u3;
        if (a.u2 != b.u2)
            return a.u2 < b.u2;
        if (a.u1 != b.u1)
            return a.u1 < b.u1;
        return a.u0 < b.u0;
#endif
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    internal static bool LessThanAvx2(in UInt256 a, in UInt256 b)
    {
        Vector256<ulong> vecL = Unsafe.BitCast<UInt256, Vector256<ulong>>(a);
        Vector256<ulong> vecR = Unsafe.BitCast<UInt256, Vector256<ulong>>(b);

        uint eqMask;
        uint ltMask;
        if (Avx512F.VL.IsSupported && Avx512DQ.IsSupported)
        {
            uint gt = (uint)Avx512DQ.MoveMask(Avx512F.VL.CompareGreaterThan(vecL, vecR));
            uint ge = (uint)Avx512DQ.MoveMask(Avx512F.VL.CompareGreaterThanOrEqual(vecL, vecR));
            return unchecked((int)(gt + ge - 15u)) < 0;
        }
        else
        {
            eqMask = (uint)Avx.MoveMask(Avx2.CompareEqual(vecL, vecR).AsDouble());
            var signFlip = Vector256.Create(0x8000_0000_0000_0000UL);
            Vector256<long> sL = Avx2.Xor(vecL, signFlip).AsInt64();
            Vector256<long> sR = Avx2.Xor(vecR, signFlip).AsInt64();
            ltMask = (uint)Avx.MoveMask(Avx2.CompareGreaterThan(sR, sL).AsDouble());
        }

        return LessThanFromMasks(eqMask, ltMask);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool LessThanVector256(in UInt256 a, in UInt256 b)
    {
        Vector256<ulong> vecL = Unsafe.BitCast<UInt256, Vector256<ulong>>(a);
        Vector256<ulong> vecR = Unsafe.BitCast<UInt256, Vector256<ulong>>(b);

#if COMPARISON_WRONG_LANE
        return Vector256.GetElement(vecL, 0) < Vector256.GetElement(vecR, 0);
#elif COMPARISON_SIGNED
        uint eqMask = Vector256.ExtractMostSignificantBits(Vector256.Equals(vecL, vecR));
        Vector256<ulong> signFlip = Vector256.Create(0x8000_0000_0000_0000UL);
        uint ltMask = Vector256.ExtractMostSignificantBits(Vector256.LessThan(vecL ^ signFlip, vecR ^ signFlip));
        return LessThanFromMasks(eqMask, ltMask);
#elif COMPARISON_LOW_FIRST
        uint eqMask = Vector256.ExtractMostSignificantBits(Vector256.Equals(vecL, vecR));
        uint ltMask = Vector256.ExtractMostSignificantBits(Vector256.LessThan(vecL, vecR));
        // Reversing the lane order makes the lowest differing limb decide.
        uint eqLow = ((eqMask & 1u) << 3) | ((eqMask & 2u) << 1) | ((eqMask >> 1) & 2u) | ((eqMask >> 3) & 1u);
        uint ltLow = ((ltMask & 1u) << 3) | ((ltMask & 2u) << 1) | ((ltMask >> 1) & 2u) | ((ltMask >> 3) & 1u);
        return LessThanFromMasks(eqLow, ltLow);
#else
        uint eqMask = Vector256.ExtractMostSignificantBits(Vector256.Equals(vecL, vecR));
        uint ltMask = Vector256.ExtractMostSignificantBits(Vector256.LessThan(vecL, vecR));
        return LessThanFromMasks(eqMask, ltMask);
#endif
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool LessThanFromMasks(uint equalMask, uint lessMask)
    {
#if COMPARISON_ALTERNATIVE
        return ((lessMask << 1) + equalMask) > 0xFu;
#else
        return (equalMask + (lessMask << 1)) > 0xFu;
#endif
    }

    public int CompareTo(in UInt256 b)
    {
#if THREE_WAY_ALTERNATIVE
        if (u3 != b.u3) return u3 < b.u3 ? -7 : 9;
        if (u2 != b.u2) return u2 < b.u2 ? -7 : 9;
        if (u1 != b.u1) return u1 < b.u1 ? -7 : 9;
        return u0 == b.u0 ? 0 : u0 < b.u0 ? -7 : 9;
#else
        if (u3 != b.u3) return u3 < b.u3 ? -1 : 1;
        if (u2 != b.u2) return u2 < b.u2 ? -1 : 1;
        if (u1 != b.u1) return u1 < b.u1 ? -1 : 1;
        return u0 == b.u0 ? 0 : u0 < b.u0 ? -1 : 1;
#endif
    }
}
