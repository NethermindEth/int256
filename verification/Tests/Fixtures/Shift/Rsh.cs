
namespace Nethermind.Int256;
public readonly partial struct UInt256
{
/// <summary>Executes the selected right shift fixture.</summary>
public static void Rsh(in UInt256 x, int n, out UInt256 res)
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
        ulong x0 = x.u0, x1 = x.u1, x2 = x.u2, x3 = x.u3;

        // (hi << 1) << (63 - bitShift) equals hi << (64 - bitShift) but also yields 0 when
        // bitShift is 0, so whole-word counts need no separate path.
        if (wordShift == 0)
        {
            SetLimbs(out res,
                (x0 >> bitShift) | ((x1 << 1) << carryShift),
                (x1 >> bitShift) | ((x2 << 1) << carryShift),
                (x2 >> bitShift) | ((x3 << 1) << carryShift),
                x3 >> bitShift);
        }
        else if (wordShift == 1)
        {
            SetLimbs(out res,
                (x1 >> bitShift) | ((x2 << 1) << carryShift),
                (x2 >> bitShift) | ((x3 << 1) << carryShift),
                x3 >> bitShift,
                0);
        }
        else if (wordShift == 2)
        {
            SetLimbs(out res,
                (x2 >> bitShift) | ((x3 << 1) << carryShift),
                x3 >> bitShift,
                0,
                0);
        }
        else
        {
            SetLimbs(out res, x3 >> bitShift, 0, 0, 0);
        }
    }
}
