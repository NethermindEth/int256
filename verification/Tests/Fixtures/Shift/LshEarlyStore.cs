
namespace Nethermind.Int256;
public readonly partial struct UInt256
{
/// <summary>Executes the selected left shift fixture.</summary>
public static void Lsh(in UInt256 x, int n, out UInt256 res)
    {
        int wordShift = n >> 6;
        if ((uint)wordShift >= (uint)Len)
        {
            if (wordShift >= 0 || (n & 63) == 0)
            {
                res = default;
                return;
            }

            wordShift = 0;
        }

        int bitShift = n & 63;
        int carryShift = 63 - bitShift;
        // Read every limb up front: res is allowed to alias x.
        System.Runtime.CompilerServices.Unsafe.SkipInit(out res);
        System.Runtime.CompilerServices.Unsafe.AsRef(in res.u0) = 0;
        ulong x0 = x.u0, x1 = x.u1, x2 = x.u2, x3 = x.u3;

        // (lo >> 1) >> (63 - bitShift) equals lo >> (64 - bitShift) but also yields 0 when
        // bitShift is 0, so whole-word counts need no separate path.
        if (wordShift == 0)
        {
            SetLimbs(out res,
                x0 << bitShift,
                (x1 << bitShift) | ((x0 >> 1) >> carryShift),
                (x2 << bitShift) | ((x1 >> 1) >> carryShift),
                (x3 << bitShift) | ((x2 >> 1) >> carryShift));
        }
        else if (wordShift == 1)
        {
            SetLimbs(out res,
                0,
                x0 << bitShift,
                (x1 << bitShift) | ((x0 >> 1) >> carryShift),
                (x2 << bitShift) | ((x1 >> 1) >> carryShift));
        }
        else if (wordShift == 2)
        {
            SetLimbs(out res,
                0,
                0,
                x0 << bitShift,
                (x1 << bitShift) | ((x0 >> 1) >> carryShift));
        }
        else
        {
            SetLimbs(out res, 0, 0, 0, x0 << bitShift);
        }
    }
}
