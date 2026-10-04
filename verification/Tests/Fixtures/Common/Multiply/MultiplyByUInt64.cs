using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;

namespace Nethermind.Int256;
public readonly partial struct UInt256
{
    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void MultiplyByUInt64(in UInt256 x, ulong y, out UInt256 res)
    {
        if (y <= 1)
        {
            // Two plain stores: a conditional expression goes through a stack temp, and a block zero of an out
            // parameter that resolves to a promoted Vector256 local makes .NET 10.0.11 emit vmovq ymm, r64.
            if (y == 0)
            {
                StoreProduct(out res, 0, 0, 0, 0);
            }
            else
            {
                res = x;
            }
            return;
        }

        ulong x0 = x.u0;
        ulong x1 = x.u1;
        ulong x2 = x.u2;
        ulong x3 = x.u3;

        // y first: mulx takes its first operand from rdx, and keeping the shared limb there saves a move per product.
        ulong carry = Multiply64(y, x0, out ulong r0);
        ulong high = Multiply64(y, x1, out ulong low);
        ulong r1 = low + carry;
        carry = high + (r1 < low ? 1UL : 0UL);

        high = Multiply64(y, x2, out low);
        ulong r2 = low + carry;
        carry = high + (r2 < low ? 1UL : 0UL);

        ulong r3 = x3 * y + carry;
        StoreProduct(out res, r0, r1, r2, r3);
    }
}
