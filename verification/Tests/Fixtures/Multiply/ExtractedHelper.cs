using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.X86;

namespace Nethermind.Int256;
public readonly partial struct UInt256
{
    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void Multiply(in UInt256 x, in UInt256 y, out UInt256 res)
    {
        ulong x0 = x.u0;
        ulong y0 = y.u0;
        ulong xTop = x.u2 | x.u3;
        ulong yTop = y.u2 | y.u3;
        ulong xHigh = x.u1 | xTop;
        ulong yHigh = y.u1 | yTop;
        if ((xHigh | yHigh) == 0)
        {
            // Zero and one take this path or the one-limb ladder; a dedicated shortcut cost every call two vector tests.
            ulong high = WideProduct(x0, y0, out ulong low);
            StoreProduct(out res, low, high, 0, 0);
            return;
        }
        if (yHigh == 0)
        {
            MultiplyByUInt64(in x, y0, out res);
            return;
        }
        if (xHigh == 0)
        {
            MultiplyByUInt64(in y, x0, out res);
            return;
        }
        if ((xTop | yTop) == 0)
        {
            MultiplyLimbs2x2(in x, in y, out res);
            return;
        }
        if (xTop == 0)
        {
            MultiplyLimbs2x4(in x, in y, out res);
            return;
        }
        if (yTop == 0)
        {
            MultiplyLimbs2x4(in y, in x, out res);
            return;
        }
        MultiplyLimbs4x4(in x, in y, out res);
    }

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
        ulong carry = WideProduct(y, x0, out ulong r0);
        ulong high = WideProduct(y, x1, out ulong low);
        ulong r1 = low + carry;
        carry = high + (r1 < low ? 1UL : 0UL);

        high = WideProduct(y, x2, out low);
        ulong r2 = low + carry;
        carry = high + (r2 < low ? 1UL : 0UL);

        ulong r3 = x3 * y + carry;
        StoreProduct(out res, r0, r1, r2, r3);
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void MultiplyLimbs2x2(in UInt256 x, in UInt256 y, out UInt256 res)
    {
        ulong x0 = x.u0;
        ulong y0 = y.u0;
        ulong x1 = x.u1;
        ulong y1 = y.u1;

        ulong h00 = WideProduct(x0, y0, out ulong r0);
        ulong h01 = WideProduct(x0, y1, out ulong l01);
        ulong carry = 0;
        ulong r1 = AddAndCountCarry(h00, l01, ref carry);
        ulong h10 = WideProduct(x1, y0, out ulong l10);
        r1 = AddAndCountCarry(r1, l10, ref carry);

        ulong r2 = carry;
        carry = 0;
        r2 = AddAndCountCarry(r2, h01, ref carry);
        r2 = AddAndCountCarry(r2, h10, ref carry);
        ulong h11 = WideProduct(x1, y1, out ulong l11);
        r2 = AddAndCountCarry(r2, l11, ref carry);
        StoreProduct(out res, r0, r1, r2, h11 + carry);
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void MultiplyLimbs2x4(in UInt256 x, in UInt256 y, out UInt256 res)
    {
        ulong x0 = x.u0;
        ulong x1 = x.u1;
        ulong y0 = y.u0;
        ulong y1 = y.u1;
        ulong y2 = y.u2;

        ulong r3 = x0 * y.u3 + x1 * y2;

        ulong h00 = WideProduct(x0, y0, out ulong r0);
        ulong h01 = WideProduct(x0, y1, out ulong l01);
        ulong carry = 0;
        ulong r1 = AddAndCountCarry(h00, l01, ref carry);
        ulong h10 = WideProduct(x1, y0, out ulong l10);
        r1 = AddAndCountCarry(r1, l10, ref carry);

        ulong r2 = carry;
        carry = 0;
        r2 = AddAndCountCarry(r2, h01, ref carry);
        r2 = AddAndCountCarry(r2, h10, ref carry);
        ulong h02 = WideProduct(x0, y2, out ulong l02);
        r2 = AddAndCountCarry(r2, l02, ref carry);
        r3 += h02;
        ulong h11 = WideProduct(x1, y1, out ulong l11);
        r2 = AddAndCountCarry(r2, l11, ref carry);
        r3 += h11 + carry;
        StoreProduct(out res, r0, r1, r2, r3);
    }

    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void MultiplyLimbs4x4(in UInt256 x, in UInt256 y, out UInt256 res)
    {
        ulong x0 = x.u0;
        ulong y0 = y.u0;
        ulong x1 = x.u1;
        ulong y1 = y.u1;
        ulong x2 = x.u2;
        ulong y2 = y.u2;

        // The top limb only needs low halves; taking them first retires x3 and y3 before the carry columns start.
        ulong r3;
        if (Avx512DQ.VL.IsSupported)
        {
            Vector256<ulong> xv = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in x));
            Vector256<ulong> yv = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in y));
            r3 = Vector256.Sum(Avx512DQ.VL.MultiplyLow(xv, Avx2.Permute4x64(yv, 0x1B)));
        }
        else if (Avx2.IsSupported)
        {
            Vector256<ulong> xv = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in x));
            Vector256<ulong> yv = Avx2.Permute4x64(Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in y)), 0x1B);
            Vector256<ulong> cross = Avx2.Add(
                Avx2.Multiply(xv.AsUInt32(), Avx2.ShiftRightLogical(yv, 32).AsUInt32()),
                Avx2.Multiply(Avx2.ShiftRightLogical(xv, 32).AsUInt32(), yv.AsUInt32()));
            r3 = Vector256.Sum(Avx2.Add(Avx2.Multiply(xv.AsUInt32(), yv.AsUInt32()), Avx2.ShiftLeftLogical(cross, 32)));
        }
        else r3 = x0 * y.u3 + x1 * y2 + x2 * y1 + x.u3 * y0;

        ulong h00 = WideProduct(x0, y0, out ulong r0);
        ulong h01 = WideProduct(x0, y1, out ulong l01);
        ulong h10 = WideProduct(x1, y0, out ulong l10);
        ulong carry = 0;
        ulong r1 = AddAndCountCarry(h00, l01, ref carry);
        r1 = AddAndCountCarry(r1, l10, ref carry);

        // Each product is folded into its column as soon as it exists so no more than one pair is in flight.
        ulong r2 = carry;
        carry = 0;
        r2 = AddAndCountCarry(r2, h01, ref carry);
        r2 = AddAndCountCarry(r2, h10, ref carry);
        ulong h02 = WideProduct(x0, y2, out ulong l02);
        r2 = AddAndCountCarry(r2, l02, ref carry);
        r3 += h02;
        ulong h11 = WideProduct(x1, y1, out ulong l11);
        r2 = AddAndCountCarry(r2, l11, ref carry);
        r3 += h11;
        ulong h20 = WideProduct(x2, y0, out ulong l20);
        r2 = AddAndCountCarry(r2, l20, ref carry);
        r3 += h20 + carry;
        StoreProduct(out res, r0, r1, r2, r3);
    }

    private static ulong WideProduct(ulong a, ulong b, out ulong low) => Multiply64(a, b, out low);
}
