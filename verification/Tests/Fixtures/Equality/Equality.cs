// Mirrors the production equality call graph; each case symbol changes one private body.
using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.X86;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    public static bool operator ==(in UInt256 a, int b) => a.Equals(b);
    public static bool operator ==(int a, in UInt256 b) => b.Equals(a);
    [OverloadResolutionPriority(1)]
    public static bool operator ==(in UInt256 a, uint b) => a.Equals(b);
    [OverloadResolutionPriority(1)]
    public static bool operator ==(uint a, in UInt256 b) => b.Equals(a);
    public static bool operator ==(in UInt256 a, long b) => a.Equals(b);
    public static bool operator ==(long a, in UInt256 b) => b.Equals(a);
    [OverloadResolutionPriority(1)]
    public static bool operator ==(in UInt256 a, ulong b) => a.Equals(b);
    [OverloadResolutionPriority(1)]
    public static bool operator ==(ulong a, in UInt256 b) => b.Equals(a);
#if WRONG_POLARITY
    public static bool operator !=(in UInt256 a, int b) => a.Equals(b);
    public static bool operator !=(int a, in UInt256 b) => b.Equals(a);
    [OverloadResolutionPriority(1)]
    public static bool operator !=(in UInt256 a, uint b) => a.Equals(b);
    [OverloadResolutionPriority(1)]
    public static bool operator !=(uint a, in UInt256 b) => b.Equals(a);
    public static bool operator !=(in UInt256 a, long b) => a.Equals(b);
    public static bool operator !=(long a, in UInt256 b) => b.Equals(a);
    [OverloadResolutionPriority(1)]
    public static bool operator !=(in UInt256 a, ulong b) => a.Equals(b);
    [OverloadResolutionPriority(1)]
    public static bool operator !=(ulong a, in UInt256 b) => b.Equals(a);
#else
    public static bool operator !=(in UInt256 a, int b) => !a.Equals(b);
    public static bool operator !=(int a, in UInt256 b) => !b.Equals(a);
    [OverloadResolutionPriority(1)]
    public static bool operator !=(in UInt256 a, uint b) => !a.Equals(b);
    [OverloadResolutionPriority(1)]
    public static bool operator !=(uint a, in UInt256 b) => !b.Equals(a);
    public static bool operator !=(in UInt256 a, long b) => !a.Equals(b);
    public static bool operator !=(long a, in UInt256 b) => !b.Equals(a);
    [OverloadResolutionPriority(1)]
    public static bool operator !=(in UInt256 a, ulong b) => !a.Equals(b);
    [OverloadResolutionPriority(1)]
    public static bool operator !=(ulong a, in UInt256 b) => !b.Equals(a);
#endif

    public static bool operator ==(in UInt256 a, in UInt256 b) => a.Equals(b);

#if WRONG_POLARITY
    public static bool operator !=(in UInt256 a, in UInt256 b) => a == b;
#else
    public static bool operator !=(in UInt256 a, in UInt256 b) => !(a == b);
#endif

    public bool Equals(int other)
    {
#if WRONG_SIGNED
        return Equals((uint)other);
#else
        return other >= 0 && Equals((uint)other);
#endif
    }

#if WRONG_SIGNED
    public bool Equals(long other) => Equals((ulong)other);
#else
    public bool Equals(long other) => other >= 0 && Equals((ulong)other);
#endif

#if WRONG_SNAPSHOT
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public bool Equals(UInt256 other) => Equals(in this);
#else
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public bool Equals(UInt256 other) => Equals(in other);
#endif

#if RENAMED
    // Renamed helpers; each public dispatcher forwards to a renamed static copy of its body.
    [OverloadResolutionPriority(1)]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public bool Equals(uint other) => RewrittenEquals(in this, other);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool RewrittenEquals(in UInt256 a, uint other)
        => Vector256.IsHardwareAccelerated
            ? RewrittenVector(in a, other)
            : a.RewrittenScalar(new UInt256(other, 0, 0, 0));

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool RewrittenVector(in UInt256 a, uint other)
        => (Vector256.CreateScalar(other) ^ Unsafe.BitCast<UInt256, Vector256<uint>>(a)) == Vector256<uint>.Zero;

    [OverloadResolutionPriority(1)]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public bool Equals(ulong other) => RewrittenEquals(in this, other);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool RewrittenEquals(in UInt256 a, ulong other)
        => Vector256.IsHardwareAccelerated
            ? RewrittenVector(in a, other)
            : a.RewrittenScalar(new UInt256(other, 0, 0, 0));

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool RewrittenVector(in UInt256 a, ulong other)
        => (Vector256.CreateScalar(other) ^ Unsafe.BitCast<UInt256, Vector256<ulong>>(a)) == Vector256<ulong>.Zero;

    [OverloadResolutionPriority(1)]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public bool Equals(in UInt256 other) => RewrittenEquals(in this, in other);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool RewrittenEquals(in UInt256 a, in UInt256 b)
        => Vector256.IsHardwareAccelerated
            ? RewrittenVector(in a, in b)
            : Sse41.IsSupported
                ? RewrittenHalves(in a, in b)
                : a.RewrittenScalar(in b);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool RewrittenVector(in UInt256 a, in UInt256 b)
        => Unsafe.BitCast<UInt256, Vector256<ulong>>(a) == Unsafe.BitCast<UInt256, Vector256<ulong>>(b);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool RewrittenHalves(in UInt256 a, in UInt256 b)
    {
        ref Vector128<ulong> av = ref Unsafe.As<UInt256, Vector128<ulong>>(ref Unsafe.AsRef(in a));
        ref Vector128<ulong> bv = ref Unsafe.As<UInt256, Vector128<ulong>>(ref Unsafe.AsRef(in b));
        return ((av ^ bv) | (Unsafe.Add(ref av, 1) ^ Unsafe.Add(ref bv, 1))) == Vector128<ulong>.Zero;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private bool RewrittenScalar(in UInt256 other)
        => ((u0 ^ other.u0) | (u1 ^ other.u1) | (u2 ^ other.u2) | (u3 ^ other.u3)) == 0;
#else
    [OverloadResolutionPriority(1)]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public bool Equals(uint other)
        => Vector256.IsHardwareAccelerated
            ? EqualsVector(in this, other)
            : EqualsScalar(new UInt256(other, 0, 0, 0));

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool EqualsVector(in UInt256 a, uint other)
#if EQUIVALENT_REDUCTION
        => Vector256.CreateScalar(other) == Unsafe.BitCast<UInt256, Vector256<uint>>(a);
#else
        => (Vector256.CreateScalar(other) ^ Unsafe.BitCast<UInt256, Vector256<uint>>(a)) == Vector256<uint>.Zero;
#endif

    [OverloadResolutionPriority(1)]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public bool Equals(ulong other)
        => Vector256.IsHardwareAccelerated
            ? EqualsVector(in this, other)
            : EqualsScalar(new UInt256(other, 0, 0, 0));

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool EqualsVector(in UInt256 a, ulong other)
#if EQUIVALENT_REDUCTION
        => Vector256.CreateScalar(other) == Unsafe.BitCast<UInt256, Vector256<ulong>>(a);
#else
        => (Vector256.CreateScalar(other) ^ Unsafe.BitCast<UInt256, Vector256<ulong>>(a)) == Vector256<ulong>.Zero;
#endif

    [OverloadResolutionPriority(1)]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public bool Equals(in UInt256 other)
#if WRONG_RECEIVER
        => Vector256.IsHardwareAccelerated
            ? EqualsVector(in other, in other)
            : Sse41.IsSupported
                ? EqualsVector128(in other, in other)
                : other.EqualsScalar(in other);
#else
        => Vector256.IsHardwareAccelerated
            ? EqualsVector(in this, in other)
            : Sse41.IsSupported
                ? EqualsVector128(in this, in other)
                : EqualsScalar(in other);
#endif

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool EqualsVector(in UInt256 a, in UInt256 b)
#if WRONG_LANE
        => a.u0 == b.u0;
#elif WRONG_REDUCTION
        => !(Vector256.Equals(Unsafe.BitCast<UInt256, Vector256<ulong>>(a), Unsafe.BitCast<UInt256, Vector256<ulong>>(b)) == Vector256<ulong>.Zero);
#elif EQUIVALENT_REDUCTION
        => (Unsafe.BitCast<UInt256, Vector256<ulong>>(a) ^ Unsafe.BitCast<UInt256, Vector256<ulong>>(b)) == Vector256<ulong>.Zero;
#else
        => Unsafe.BitCast<UInt256, Vector256<ulong>>(a) == Unsafe.BitCast<UInt256, Vector256<ulong>>(b);
#endif

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool EqualsVector128(in UInt256 a, in UInt256 b)
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

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private bool EqualsScalar(in UInt256 other)
#if EQUIVALENT_SCALAR
        => u0 == other.u0 && u1 == other.u1 && u2 == other.u2 && u3 == other.u3;
#elif WRONG_LANE
        => ((u0 ^ other.u0) | (u1 ^ other.u1) | (u2 ^ other.u2)) == 0;
#elif WRONG_REDUCTION
        => ((u0 ^ other.u0) & (u1 ^ other.u1) & (u2 ^ other.u2) & (u3 ^ other.u3)) == 0;
#else
        => ((u0 ^ other.u0) | (u1 ^ other.u1) | (u2 ^ other.u2) | (u3 ^ other.u3)) == 0;
#endif
#endif
}
