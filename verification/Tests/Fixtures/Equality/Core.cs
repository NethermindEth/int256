using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.X86;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
#if RENAMED
    private static bool ReferenceEqual(in UInt256 a, in UInt256 b) => RewrittenReferenceEqual(in a, in b);

    private static bool RewrittenReferenceEqual(
#else
    private static bool ReferenceEqual(
#endif
        in UInt256 a, in UInt256 b)
    {
        if (Vector256.IsHardwareAccelerated)
        {
#if WRONG_LANE
            return a.u0 == b.u0;
#elif WRONG_REDUCTION
            return !(Vector256.Equals(Unsafe.BitCast<UInt256, Vector256<ulong>>(a),
                Unsafe.BitCast<UInt256, Vector256<ulong>>(b)) == Vector256<ulong>.Zero);
#elif EQUIVALENT_REDUCTION
            return (Unsafe.BitCast<UInt256, Vector256<ulong>>(a) ^
                Unsafe.BitCast<UInt256, Vector256<ulong>>(b)) == Vector256<ulong>.Zero;
#else
            return Unsafe.BitCast<UInt256, Vector256<ulong>>(a) ==
                Unsafe.BitCast<UInt256, Vector256<ulong>>(b);
#endif
        }
        if (Sse41.IsSupported)
        {
            ref Vector128<ulong> av = ref Unsafe.As<UInt256, Vector128<ulong>>(ref Unsafe.AsRef(in a));
            ref Vector128<ulong> bv = ref Unsafe.As<UInt256, Vector128<ulong>>(ref Unsafe.AsRef(in b));
#if WRONG_LANE
            return (av ^ bv) == Vector128<ulong>.Zero;
#elif WRONG_REDUCTION
            return ((av ^ bv) & (Unsafe.Add(ref av, 1) ^ Unsafe.Add(ref bv, 1))) == Vector128<ulong>.Zero;
#elif EQUIVALENT_REDUCTION
            return ((Unsafe.Add(ref av, 1) ^ Unsafe.Add(ref bv, 1)) | (av ^ bv)) == Vector128<ulong>.Zero;
#else
            return ((av ^ bv) | (Unsafe.Add(ref av, 1) ^ Unsafe.Add(ref bv, 1))) == Vector128<ulong>.Zero;
#endif
        }
#if EQUIVALENT_SCALAR
        return a.u0 == b.u0 && a.u1 == b.u1 && a.u2 == b.u2 && a.u3 == b.u3;
#elif WRONG_LANE
        return ((a.u0 ^ b.u0) | (a.u1 ^ b.u1) | (a.u2 ^ b.u2)) == 0;
#elif WRONG_REDUCTION
        return ((a.u0 ^ b.u0) & (a.u1 ^ b.u1) & (a.u2 ^ b.u2) & (a.u3 ^ b.u3)) == 0;
#else
        return ((a.u0 ^ b.u0) | (a.u1 ^ b.u1) | (a.u2 ^ b.u2) | (a.u3 ^ b.u3)) == 0;
#endif
    }

    private bool ScalarEqual(in UInt256 other) =>
#if EQUIVALENT_SCALAR
        u0 == other.u0 && u1 == other.u1 && u2 == other.u2 && u3 == other.u3;
#else
        ((u0 ^ other.u0) | (u1 ^ other.u1) | (u2 ^ other.u2) | (u3 ^ other.u3)) == 0;
#endif

#if RENAMED
    private static bool PrimitiveEqual(in UInt256 a, uint other) => RewrittenPrimitiveEqual(in a, other);
    private static bool RewrittenPrimitiveEqual(
#else
    private static bool PrimitiveEqual(
#endif
        in UInt256 a, uint other) => Vector256.IsHardwareAccelerated
#if EQUIVALENT_REDUCTION
        ? Vector256.CreateScalar(other) == Unsafe.BitCast<UInt256, Vector256<uint>>(a)
#else
        ? (Vector256.CreateScalar(other) ^ Unsafe.BitCast<UInt256, Vector256<uint>>(a)) == Vector256<uint>.Zero
#endif
        : a.ScalarEqual(new UInt256(other));

#if RENAMED
    private static bool PrimitiveEqual(in UInt256 a, ulong other) => RewrittenPrimitiveEqual(in a, other);
    private static bool RewrittenPrimitiveEqual(
#else
    private static bool PrimitiveEqual(
#endif
        in UInt256 a, ulong other) => Vector256.IsHardwareAccelerated
#if EQUIVALENT_REDUCTION
        ? Vector256.CreateScalar(other) == Unsafe.BitCast<UInt256, Vector256<ulong>>(a)
#else
        ? (Vector256.CreateScalar(other) ^ Unsafe.BitCast<UInt256, Vector256<ulong>>(a)) == Vector256<ulong>.Zero
#endif
        : a.ScalarEqual(new UInt256(other));
}
