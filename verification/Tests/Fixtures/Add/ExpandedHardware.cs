using System.Runtime.CompilerServices;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    /// <summary>Adds initial input values, allowing arbitrary overlap.</summary>
    public static void Add(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        if (System.Runtime.Intrinsics.X86.Avx2.IsSupported)
        {
            ulong word = a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            word = word * b.u0 + a.u0;
            Unsafe.SkipInit(out res);
            Unsafe.AsRef(in res.u0) = word;
            return;
        }
        AddScalar(in a, in b, out res, false);
    }
}
