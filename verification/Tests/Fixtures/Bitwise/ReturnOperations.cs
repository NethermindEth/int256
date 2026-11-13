namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static ulong WordAnd(ulong left, ulong right) =>
#if RETURN_WRONG
        left ^ right;
#elif RETURN_HELPER
        ~(~left | ~right);
#else
        left & right;
#endif

    private static ulong WordOr(ulong left, ulong right) =>
#if RETURN_WRONG
        left ^ right;
#elif RETURN_HELPER
        ~(~left & ~right);
#else
        left | right;
#endif

    private static ulong WordNot(ulong input) =>
#if RETURN_WRONG
        input;
#elif RETURN_HELPER
        input ^ ulong.MaxValue;
#else
        ~input;
#endif

    public static void And(in UInt256 left, in UInt256 right, out UInt256 result)
    {
#if RETURN_EARLY
        result = new UInt256(WordAnd(left.u0, right.u0), 0, 0, 0);
        System.Runtime.CompilerServices.Unsafe.AsRef(in result.u1) = WordAnd(left.u1, right.u1);
        System.Runtime.CompilerServices.Unsafe.AsRef(in result.u2) = WordAnd(left.u2, right.u2);
        System.Runtime.CompilerServices.Unsafe.AsRef(in result.u3) = WordAnd(left.u3, right.u3);
#else
        result = new UInt256(WordAnd(left.u0, right.u0), WordAnd(left.u1, right.u1),
            WordAnd(left.u2, right.u2), WordAnd(left.u3, right.u3));
#endif
    }

    public static void Or(in UInt256 left, in UInt256 right, out UInt256 result)
    {
#if RETURN_EARLY
        result = new UInt256(WordOr(left.u0, right.u0), 0, 0, 0);
        System.Runtime.CompilerServices.Unsafe.AsRef(in result.u1) = WordOr(left.u1, right.u1);
        System.Runtime.CompilerServices.Unsafe.AsRef(in result.u2) = WordOr(left.u2, right.u2);
        System.Runtime.CompilerServices.Unsafe.AsRef(in result.u3) = WordOr(left.u3, right.u3);
#else
        result = new UInt256(WordOr(left.u0, right.u0), WordOr(left.u1, right.u1),
            WordOr(left.u2, right.u2), WordOr(left.u3, right.u3));
#endif
    }

    public static void Not(in UInt256 input, out UInt256 result)
    {
#if RETURN_EARLY
        result = new UInt256(WordNot(input.u0), 0, 0, 0);
        System.Runtime.CompilerServices.Unsafe.AsRef(in result.u1) = WordNot(input.u1);
        System.Runtime.CompilerServices.Unsafe.AsRef(in result.u2) = WordNot(input.u2);
        System.Runtime.CompilerServices.Unsafe.AsRef(in result.u3) = WordNot(input.u3);
#else
        result = new UInt256(WordNot(input.u0), WordNot(input.u1), WordNot(input.u2), WordNot(input.u3));
#endif
    }
}
