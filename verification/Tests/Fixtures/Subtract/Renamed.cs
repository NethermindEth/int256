using System.Runtime.CompilerServices;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    /// <summary>Subtracts initial input values modulo 2^256, allowing overlap.</summary>
    public static void Subtract(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        DifferenceImplementation(in a, in b, out res);
    }

    private static bool DifferenceImplementation(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        return DifferenceScalar(in a, in b, out res);
    }
    private static bool DifferenceScalar(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        ulong b0 = b.u0;
        if ((b.u1 | b.u2 | b.u3) == 0)
            return DifferenceWord(in a, b0, out res);
        ulong borrow = 0;
        DifferenceBorrow(a.u0, b0, ref borrow, out ulong r0);
        DifferenceBorrow(a.u1, b.u1, ref borrow, out ulong r1);
        DifferenceBorrow(a.u2, b.u2, ref borrow, out ulong r2);
        DifferenceBorrow(a.u3, b.u3, ref borrow, out ulong r3);
        WriteWords(out res, r0, r1, r2, r3);
        return borrow != 0;
    }
    private static bool DifferenceWord(in UInt256 a, ulong b0, out UInt256 res)
    {
        ulong a0 = a.u0, a1 = a.u1, a2 = a.u2, a3 = a.u3;
        ulong r0 = a0 - b0;
        if (a0 >= b0)
        {
            WriteWords(out res, r0, a1, a2, a3);
            return false;
        }
        if (a1 != 0)
        {
            WriteWords(out res, r0, a1 - 1, a2, a3);
            return false;
        }
        if (a2 != 0)
        {
            WriteWords(out res, r0, ulong.MaxValue, a2 - 1, a3);
            return false;
        }
        if (a3 != 0)
        {
            WriteWords(out res, r0, ulong.MaxValue, ulong.MaxValue, a3 - 1);
            return false;
        }

        WriteWords(out res, r0, ulong.MaxValue, ulong.MaxValue, ulong.MaxValue);
        return true;
    }

    // Inputs are read into locals before this runs, so res may alias either operand
    private static void DifferenceBorrow(ulong a, ulong b, ref ulong borrow, out ulong res)
    {
        res = a - b - borrow;
        borrow = (a < b ? 1UL : 0UL) | (borrow & (a == b ? 1UL : 0UL));
    }
    private static void WriteWords(out UInt256 res, ulong r0, ulong r1, ulong r2, ulong r3)
    {
        Unsafe.SkipInit(out res);
        Unsafe.AsRef(in res.u0) = r0;
        Unsafe.AsRef(in res.u1) = r1;
        Unsafe.AsRef(in res.u2) = r2;
        Unsafe.AsRef(in res.u3) = r3;
    }
}
