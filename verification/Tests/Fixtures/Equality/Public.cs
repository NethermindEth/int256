namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    /// <summary>Creates a scalar fixture value.</summary>
    public UInt256(ulong value) : this(value, 0, 0, 0) { }
    /// <summary>Equality fixture entry.</summary>
    public override bool Equals(object? obj) => obj is UInt256 value && Equals(in value);
    /// <summary>Equality fixture entry.</summary>
    public override int GetHashCode() => unchecked((int)u0);

    /// <summary>Equality fixture entry.</summary>
    public bool Equals(in UInt256 other)
#if WRONG_RECEIVER
        => ReferenceEqual(in other, in other);
#else
        => ReferenceEqual(in this, in other);
#endif
    /// <summary>Equality fixture entry.</summary>
    public bool Equals(UInt256 other)
#if WRONG_SNAPSHOT
        => Equals(in this);
#else
        => Equals(in other);
#endif
    /// <summary>Equality fixture entry.</summary>
    public bool Equals(uint other) => PrimitiveEqual(in this, other);
    /// <summary>Equality fixture entry.</summary>
    public bool Equals(ulong other) => PrimitiveEqual(in this, other);
    /// <summary>Equality fixture entry.</summary>
    public bool Equals(int other) =>
#if !WRONG_SIGNED
        other >= 0 &&
#endif
        Equals((uint)other);
    /// <summary>Equality fixture entry.</summary>
    public bool Equals(long other) =>
#if !WRONG_SIGNED
        other >= 0 &&
#endif
        Equals((ulong)other);

    /// <summary>Equality fixture entry.</summary>
    public static bool operator ==(in UInt256 a, int b) => a.Equals(b);
    /// <summary>Equality fixture entry.</summary>
    public static bool operator !=(in UInt256 a, int b) => Unequal(a.Equals(b));
    /// <summary>Equality fixture entry.</summary>
    public static bool operator ==(int a, in UInt256 b) => b.Equals(a);
    /// <summary>Equality fixture entry.</summary>
    public static bool operator !=(int a, in UInt256 b) => Unequal(b.Equals(a));
    /// <summary>Equality fixture entry.</summary>
    public static bool operator ==(in UInt256 a, uint b) => a.Equals(b);
    /// <summary>Equality fixture entry.</summary>
    public static bool operator !=(in UInt256 a, uint b) => Unequal(a.Equals(b));
    /// <summary>Equality fixture entry.</summary>
    public static bool operator ==(uint a, in UInt256 b) => b.Equals(a);
    /// <summary>Equality fixture entry.</summary>
    public static bool operator !=(uint a, in UInt256 b) => Unequal(b.Equals(a));
    /// <summary>Equality fixture entry.</summary>
    public static bool operator ==(in UInt256 a, long b) => a.Equals(b);
    /// <summary>Equality fixture entry.</summary>
    public static bool operator !=(in UInt256 a, long b) => Unequal(a.Equals(b));
    /// <summary>Equality fixture entry.</summary>
    public static bool operator ==(long a, in UInt256 b) => b.Equals(a);
    /// <summary>Equality fixture entry.</summary>
    public static bool operator !=(long a, in UInt256 b) => Unequal(b.Equals(a));
    /// <summary>Equality fixture entry.</summary>
    public static bool operator ==(in UInt256 a, ulong b) => a.Equals(b);
    /// <summary>Equality fixture entry.</summary>
    public static bool operator !=(in UInt256 a, ulong b) => Unequal(a.Equals(b));
    /// <summary>Equality fixture entry.</summary>
    public static bool operator ==(ulong a, in UInt256 b) => b.Equals(a);
    /// <summary>Equality fixture entry.</summary>
    public static bool operator !=(ulong a, in UInt256 b) => Unequal(b.Equals(a));
    /// <summary>Equality fixture entry.</summary>
    public static bool operator ==(in UInt256 a, in UInt256 b) => a.Equals(in b);
    /// <summary>Equality fixture entry.</summary>
    public static bool operator !=(in UInt256 a, in UInt256 b) => Unequal(a.Equals(in b));
    private static bool Unequal(bool equal) =>
#if WRONG_POLARITY
        equal;
#else
        !equal;
#endif
}
