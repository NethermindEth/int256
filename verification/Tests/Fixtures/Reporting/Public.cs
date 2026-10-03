namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    /// <summary>Return the carry flag while storing the wrapped sum.</summary>
    public static bool AddOverflow(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        bool flag = AddOverflowCore(in a, in b, out res);
#if WRONG_REPORTING_FLAG
        return !flag;
#else
        return flag;
#endif
    }

    /// <summary>Return the borrow flag while storing the wrapped difference.</summary>
    public static bool SubtractUnderflow(in UInt256 a, in UInt256 b, out UInt256 res)
    {
#if RENAMED
        bool flag = DifferenceDispatcher(in a, in b, out res);
#else
        bool flag = SubtractImpl(in a, in b, out res);
#endif
#if WRONG_REPORTING_FLAG
        return !flag;
#else
        return flag;
#endif
    }
}
