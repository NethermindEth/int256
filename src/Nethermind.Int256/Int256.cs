// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Buffers.Binary;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.X86;

[assembly: InternalsVisibleTo("Nethermind.Int256.Tests")]

namespace Nethermind.Int256;

public readonly struct Int256 : IEquatable<Int256>, IComparable, IComparable<Int256>, IInteger<Int256>, IConvertible
{
    public static readonly Int256 Zero = (Int256)0UL;
    public static readonly Int256 One = (Int256)1UL;
    public static readonly Int256 MinusOne = -1L;
    public static readonly Int256 Max = new Int256(((BigInteger.One << 255) - 1));

    internal readonly UInt256 _value;

    public Int256(ReadOnlySpan<byte> bytes, bool isBigEndian)
    {
        _value = new UInt256(bytes, isBigEndian);
    }

    public Int256(UInt256 value)
    {
        _value = value;
    }

    public Int256(BigInteger big)
    {
        if (big.Sign < 0)
        {
            (new Int256((UInt256)(-big))).Neg(out Int256 neg);
            _value = neg._value;
        }
        else
        {
            _value = (UInt256)big;
        }
    }

    public Int256(int n)
    {
        if (n < 0)
        {
            Int256 value = new(new UInt256((ulong)-n));
            value.Neg(out Int256 res);
            _value = res._value;
        }
        else
        {
            _value = new UInt256((ulong)n);
        }
    }

    public static explicit operator Int256(int n) => new Int256(n);

    public Int256 OneValue => One;

    public Int256 ZeroValue => Zero;

    public int Sign
    {
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        get => _value.IsZero ? 0 : _value.u3 < 0x8000000000000000ul ? 1 : -1;
    }
    public bool IsNegative
    {
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        get => unchecked((long)_value.u3) < 0;
    }

    public static Int256 operator +(in Int256 a, in Int256 b)
    {
        Add(in a, in b, out Int256 res);
        return res;
    }

    public static bool AddOverflow(in Int256 a, in Int256 b, out Int256 res)
    {
        var overflow = UInt256.AddOverflow(a._value, b._value, out UInt256 ures);
        res = new Int256(ures);
        return overflow;
    }

    public static void Add(in Int256 a, in Int256 b, out Int256 res)
    {
        UInt256.AddOverflow(a._value, b._value, out UInt256 ures);
        res = new Int256(ures);
    }

    public void Add(in Int256 a, out Int256 res) => Add(this, a, out res);

    public static void AddMod(in Int256 x, in Int256 y, in Int256 m, out Int256 res)
    {
        Int256 mt = m;
        if (mt.IsOne)
        {
            res = Zero;
            return;
        }

        if (m.IsNegative)
        {
            m.Neg(out mt);
        }
        bool xIsNegative = x.IsNegative;
        bool yIsNegative = y.IsNegative;
        if (xIsNegative && yIsNegative)
        {
            x.Neg(out Int256 xNeg);
            y.Neg(out Int256 yNeg);
            xNeg._value.AddMod(yNeg._value, mt._value, out UInt256 ures);
            res = new Int256(ures);
            res.Neg(out res);
        }
        else if (!xIsNegative && !yIsNegative)
        {
            x._value.AddMod(y._value, mt._value, out UInt256 ures);
            res = new Int256(ures);
        }
        else
        {
            x.Add(y, out res);
            res.Mod(mt, out res);
        }
    }

    public void AddMod(in Int256 a, in Int256 m, out Int256 res) => AddMod(this, a, m, out res);

    public static void Subtract(in Int256 a, in Int256 b, out Int256 res)
    {
        a._value.Subtract(b._value, out UInt256 ures);
        res = new Int256(ures);
    }

    public void Subtract(in Int256 a, out Int256 res) => Subtract(this, a, out res);

    public static void SubtractMod(in Int256 x, in Int256 y, in Int256 m, out Int256 res)
    {
        var mt = m;
        if (mt.IsOne)
        {
            res = Int256.Zero;
            return;
        }

        if (m.IsNegative)
        {
            m.Neg(out mt);
        }
        bool xIsNegative = x.IsNegative;
        bool yIsNegative = y.IsNegative;
        if (xIsNegative && !yIsNegative)
        {
            x.Neg(out Int256 xNeg);
            xNeg._value.AddMod(y._value, mt._value, out UInt256 ures);
            res = new Int256(ures);
            res.Neg(out res);
        }
        else if (!xIsNegative && yIsNegative)
        {
            y.Neg(out Int256 yNeg);
            x._value.AddMod(yNeg._value, mt._value, out UInt256 ures);
            res = new Int256(ures);
        }
        else
        {
            x.Subtract(y, out res);
            res.Mod(mt, out res);
        }
    }

    public void SubtractMod(in Int256 a, in Int256 m, out Int256 res) => SubtractMod(this, a, m, out res);

    public static void Multiply(in Int256 a, in Int256 b, out Int256 res)
    {
        // Truncated multiplication is sign-agnostic in two's complement: negation is exact mod 2**256,
        // so the sign-magnitude round trip cancelled itself and the raw product is already signed.
        Unsafe.SkipInit(out res);
        UInt256.Multiply(in a._value, in b._value, out Unsafe.As<Int256, UInt256>(ref res));
    }

    public void Multiply(in Int256 a, out Int256 res) => Multiply(this, a, out res);

    public static void MultiplyMod(in Int256 x, in Int256 y, in Int256 m, out Int256 res)
    {
        var mAbs = m;
        if (m.IsNegative)
        {
            m.Neg(out mAbs);
        }
        bool xIsNegative = x.IsNegative;
        bool yIsNegative = y.IsNegative;
        if (xIsNegative != yIsNegative)
        {
            var xAbs = x;
            var yAbs = y;
            if (xIsNegative)
            {
                x.Neg(out xAbs);
            }
            else
            {
                y.Neg(out yAbs);
            }
            xAbs._value.MultiplyMod(yAbs._value, mAbs._value, out UInt256 ures);
            res = new Int256(ures);
            res.Neg(out res);
        }
        else
        {
            var xAbs = x;
            var yAbs = y;
            if (xIsNegative)
            {
                x.Neg(out xAbs);
                y.Neg(out yAbs);
            }
            xAbs._value.MultiplyMod(yAbs._value, mAbs._value, out UInt256 ures);
            res = new Int256(ures);
        }
    }

    public void MultiplyMod(in Int256 a, in Int256 m, out Int256 res) => MultiplyMod(this, a, m, out res);

    public static void Divide(in Int256 n, in Int256 d, out Int256 res)
    {
        bool nIsNegative = n.IsNegative;
        bool dIsNegative = d.IsNegative;
        UInt256 value;
        if (!nIsNegative)
        {
            if (!dIsNegative)
            {
                // pos / pos
                UInt256.Divide(n._value, d._value, out value);
                res = new Int256(value);
                return;
            }
            else
            {
                // pos / neg
                Neg(d, out Int256 neg);
                UInt256.Divide(n._value, neg._value, out value);
                res = new Int256(value);
                res.Neg(out res);
                return;
            }
        }

        Neg(n, out Int256 nNeg);
        if (dIsNegative)
        {
            // neg / neg
            Neg(d, out Int256 dNeg);
            UInt256.Divide(nNeg._value, dNeg._value, out value);
            res = new Int256(value);
            return;
        }
        // neg / pos
        UInt256.Divide(nNeg._value, d._value, out value);
        res = new Int256(value);
        res.Neg(out res);
    }

    public void Divide(in Int256 a, out Int256 res) => Divide(this, a, out res);

    public static void Exp(in Int256 b, in Int256 e, out Int256 res)
    {
        if (e.IsNegative)
        {
            throw new ArgumentException("exponent must be non-negative");
        }
        // Repeated multiplication inherits multiplication's sign-agnosticism: raising the raw words
        // gives the signed power mod 2**256, odd exponents of a negative base included.
        Unsafe.SkipInit(out res);
        UInt256.Exp(in b._value, in e._value, out Unsafe.As<Int256, UInt256>(ref res));
    }

    public void Exp(in Int256 exp, out Int256 res) => Exp(this, exp, out res);

    public static void ExpMod(in Int256 bs, in Int256 exp, in Int256 m, out Int256 res)
    {
        if (exp.IsNegative)
        {
            throw new ArgumentException("exponent must not be negative");
        }
        Int256 bv = bs;
        bool switchSign = false;
        if (bs.IsNegative)
        {
            bv.Neg(out bv);
            switchSign = exp._value.Bit(0);
        }
        var mAbs = m;
        if (m.IsNegative)
        {
            mAbs.Neg(out mAbs);
        }
        UInt256.ExpMod(bv._value, exp._value, mAbs._value, out UInt256 ures);
        res = new Int256(ures);
        if (switchSign)
        {
            res.Neg(out res);
        }
    }

    public void ExpMod(in Int256 exp, in Int256 m, out Int256 res) => ExpMod(this, exp, m, out res);

    public static void LeftShift(in Int256 x, int n, out Int256 res)
    {
        x._value.LeftShift(n, out UInt256 ures);
        res = new Int256(ures);
    }

    // Mod sets res to (sign x) * { abs(x) modulus abs(y) }, and throws when y is zero.
    public static void Mod(in Int256 x, in Int256 y, out Int256 res)
    {
        bool xIsNegative = x.IsNegative;
        bool yIsNegative = y.IsNegative;

        // Only the magnitudes divide and the remainder keeps the dividend's sign, but taking absolute
        // values into locals up front copied both operands - 32 bytes each - even when neither needed
        // it and both already sat where Mod wants them.
        if (!(xIsNegative | yIsNegative))
        {
            UInt256.Mod(in x._value, in y._value, out UInt256 positive);
            res = new Int256(positive);
            return;
        }

        Int256 xIn = x, yIn = y;
        if (xIsNegative) Neg(x, out xIn);
        if (yIsNegative) Neg(y, out yIn);
        UInt256.Mod(in xIn._value, in yIn._value, out UInt256 value);
        res = new Int256(value);
        if (xIsNegative) Neg(res, out res);
    }

    public void Mod(in Int256 m, out Int256 res) => Mod(this, m, out res);

    // Abs sets res to the absolute value
    //   Abs(0)        = 0
    //   Abs(1)        = 1
    //   Abs(2**255)   = -2**255
    //   Abs(2**256-1) = -1
    public void Abs(out Int256 res)
    {
        if (!IsNegative)
        {
            res = this;
        }
        else
        {
            Neg(this, out res);
        }
    }

    // Neg returns -x mod 2**256.
    public static void Neg(in Int256 x, out Int256 neg)
    {
        UInt256.Subtract(UInt256.Zero, x._value, out UInt256 value);
        neg = new Int256(value);
    }

    public void Neg(out Int256 res) => Neg(this, out res);

    public void LeftShift(int n, out Int256 res) => LeftShift(this, n, out res);

    /// <summary>
    /// Shifts <paramref name="x"/> right by <paramref name="n"/> bits, filling the vacated high bits with
    /// the sign of <paramref name="x"/> and discarding bits shifted out of bit 0.
    /// </summary>
    /// <remarks>
    /// Counts of 256 or more produce 0 or -1 according to the sign. Negative counts keep the unsigned
    /// type's behaviour: a negative multiple of 64 produces 0 or -1, any other negative count shifts by
    /// <c>n &amp; 63</c> with no word shift. <paramref name="res"/> may alias <paramref name="x"/>.
    /// </remarks>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void Rsh(in Int256 x, int n, out Int256 res)
    {
        // Read every limb up front: res is allowed to alias x.
        ulong x0 = x._value.u0, x1 = x._value.u1, x2 = x._value.u2, x3 = x._value.u3;
        long top = unchecked((long)x3);

        int wordShift = n >> 6;
        if ((uint)wordShift >= (uint)UInt256.Len)
        {
            if (wordShift >= 0 || (n & 63) == 0)
            {
                ulong saturated = (ulong)(top >> 63);
                SetLimbs(out res, saturated, saturated, saturated, saturated);
                return;
            }

            wordShift = 0;
        }

        int bitShift = n & 63;
        int carryShift = 63 - bitShift;

        if (Avx2.IsSupported)
        {
            // Funnel in the vector domain. The scalar form below has to hand four general registers to
            // the 32-byte store, and vmovq plus vpinsrq cost 5 and 6 cycles each crossing back.
            Vector256<ulong> v = Unsafe.BitCast<UInt256, Vector256<ulong>>(x._value);
            // The top limb's sign in every lane: what the funnel shifts in from above.
            Vector256<ulong> fill = Avx2.Permute4x64(Vector256.LessThan(v.AsInt64(), Vector256<long>.Zero).AsUInt64(), 0xFF);
            Vector256<ulong> lo, hi;
            if (Avx512F.VL.IsSupported)
            {
                // Window k selects limbs k..k+3, and an index past limb 3 takes a lane of the fill.
                ref Vector256<ulong> windows = ref Unsafe.As<byte, Vector256<ulong>>(ref MemoryMarshal.GetReference(ShiftWindows));
                lo = Avx512F.VL.PermuteVar4x64x2(v, Unsafe.Add(ref windows, (nuint)wordShift), fill);
                hi = Avx512F.VL.PermuteVar4x64x2(v, Unsafe.Add(ref windows, (nuint)wordShift + 1), fill);
            }
            else
            {
                // vpermd reaches every lane but only one operand, so the vacated lanes are selected
                // from the fill afterwards. Its indices wrap, which is why the mask has to follow.
                ref Vector256<uint> windows = ref Unsafe.As<byte, Vector256<uint>>(ref MemoryMarshal.GetReference(ShiftWindowPairs));
                ref Vector256<ulong> vacated = ref Unsafe.As<byte, Vector256<ulong>>(ref MemoryMarshal.GetReference(ShiftVacated));
                Vector256<uint> value = v.AsUInt32();
                lo = Vector256.ConditionalSelect(Unsafe.Add(ref vacated, (nuint)wordShift), fill,
                    Avx2.PermuteVar8x32(value, Unsafe.Add(ref windows, (nuint)wordShift)).AsUInt64());
                hi = Vector256.ConditionalSelect(Unsafe.Add(ref vacated, (nuint)wordShift + 1), fill,
                    Avx2.PermuteVar8x32(value, Unsafe.Add(ref windows, (nuint)wordShift + 1)).AsUInt64());
            }

            Unsafe.SkipInit(out res);
            Unsafe.As<Int256, Vector256<ulong>>(ref res) =
                Avx2.ShiftRightLogical(lo, Vector128.CreateScalar((ulong)bitShift))
                | Avx2.ShiftLeftLogical(Avx2.ShiftLeftLogical(hi, 1), Vector128.CreateScalar((ulong)carryShift));
            return;
        }

        // Two identities keep this the unsigned funnel with no arithmetic of its own: an arithmetic shift
        // of the top limb is that limb's funnel step with the sign already shifted in, and
        // (hi << 1) << (63 - bitShift) equals hi << (64 - bitShift) while still yielding 0 at bitShift 0,
        // so whole-word counts need no separate path.
        if (wordShift == 0)
        {
            SetLimbs(out res,
                (x0 >> bitShift) | ((x1 << 1) << carryShift),
                (x1 >> bitShift) | ((x2 << 1) << carryShift),
                (x2 >> bitShift) | ((x3 << 1) << carryShift),
                (ulong)(top >> bitShift));
        }
        else if (wordShift == 1)
        {
            SetLimbs(out res,
                (x1 >> bitShift) | ((x2 << 1) << carryShift),
                (x2 >> bitShift) | ((x3 << 1) << carryShift),
                (ulong)(top >> bitShift),
                (ulong)(top >> 63));
        }
        else if (wordShift == 2)
        {
            ulong fill = (ulong)(top >> 63);
            SetLimbs(out res,
                (x2 >> bitShift) | ((x3 << 1) << carryShift),
                (ulong)(top >> bitShift),
                fill,
                fill);
        }
        else
        {
            ulong fill = (ulong)(top >> 63);
            SetLimbs(out res,
                (ulong)(top >> bitShift),
                fill,
                fill,
                fill);
        }
    }

    /// <summary>
    /// Lane windows for the signed shift's permute: entry <c>k</c> is <c>[k, k+1, k+2, k+3]</c>, so
    /// entry <c>wordShift</c> puts limb <c>wordShift + i</c> in lane <c>i</c>. An index past limb 3
    /// addresses the second permute operand, which carries the sign fill.
    /// </summary>
    private static ReadOnlySpan<byte> ShiftWindows =>
    [
        // window 0: limbs 0..3
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,

        // window 1: limbs 1..4
        0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,

        // window 2: limbs 2..5
        0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,

        // window 3: limbs 3..6
        0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x06, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,

        // window 4: limbs 4..7
        0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x06, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    ];

    /// <summary>
    /// The same windows as <see cref="ShiftWindows"/> in 32-bit lanes, for vpermd, which addresses one
    /// operand and wraps: lanes the shift vacates come out as limb 0 and are replaced via
    /// <see cref="ShiftVacated"/>.
    /// </summary>
    private static ReadOnlySpan<byte> ShiftWindowPairs =>
    [
        // window 0: limb pairs 0..3, wrapping past limb 3
        0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x05, 0x00, 0x00, 0x00, 0x06, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00,

        // window 1: limb pairs 1..4, wrapping past limb 3
        0x02, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x05, 0x00, 0x00, 0x00, 0x06, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,

        // window 2: limb pairs 2..5, wrapping past limb 3
        0x04, 0x00, 0x00, 0x00, 0x05, 0x00, 0x00, 0x00, 0x06, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00,

        // window 3: limb pairs 3..6, wrapping past limb 3
        0x06, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x05, 0x00, 0x00, 0x00,

        // window 4: limb pairs 4..7, wrapping past limb 3
        0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x05, 0x00, 0x00, 0x00, 0x06, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00,
    ];

    /// <summary>All-ones in the lanes that window <c>k</c> leaves past the top limb, zero elsewhere.</summary>
    private static ReadOnlySpan<byte> ShiftVacated =>
    [
        // window 0: lanes from limb 0 up, all-ones where the shift vacates
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,

        // window 1: lanes from limb 1 up, all-ones where the shift vacates
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,

        // window 2: lanes from limb 2 up, all-ones where the shift vacates
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,

        // window 3: lanes from limb 3 up, all-ones where the shift vacates
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,

        // window 4: lanes from limb 4 up, all-ones where the shift vacates
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
        0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    ];

    /// <summary>Writes a result built from four separate limbs, in one store of the full width.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void SetLimbs(out Int256 res, ulong z0, ulong z1, ulong z2, ulong z3)
    {
        Unsafe.SkipInit(out res);
        UInt256.SetLimbs(out Unsafe.As<Int256, UInt256>(ref res), z0, z1, z2, z3);
    }

    public static void RightShift(in Int256 x, int n, out Int256 res) => Rsh(x, n, out res);

    public void RightShift(int n, out Int256 res) => RightShift(this, n, out res);

    public void Convert(out BigInteger big)
    {
        if (IsNegative)
        {
            Abs(out Int256 res);
            res._value.Convert(out big);
            big = -big;
        }
        else
        {
            _value.Convert(out big);
        }
    }

    public override string ToString()
    {
        return ToString(null);
    }

    [OverloadResolutionPriority(1)]
    private bool Equals(in Int256 other) => _value.Equals(other._value);

    public bool Equals(Int256 other) => _value.Equals(other._value);

    public override bool Equals(object? obj) => obj is Int256 other && Equals(other);

    public override int GetHashCode() => _value.GetHashCode();

    public static bool operator ==(in Int256 a, in Int256 b) => a.Equals(b);

    public static bool operator !=(in Int256 a, in Int256 b) => !(a == b);

    public bool IsZero
    {
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        get => _value.IsZero;
    }

    public bool IsOne
    {
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        get => _value.IsOne;
    }

    public Int256 MaximalValue => Max;

    public int CompareTo(object? obj) => obj is not Int256 int256 ? throw new InvalidOperationException() : CompareTo(int256);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public int CompareTo(Int256 b) => CompareTo(in b);

    [OverloadResolutionPriority(1)]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public int CompareTo(in Int256 b)
    {
        // The sign lives in the top limb, so comparing that limb signed and the rest unsigned is the
        // whole of two's-complement order: one descending pass, and no bias to apply first.
        long top = unchecked((long)_value.u3);
        long bTop = unchecked((long)b._value.u3);
        if (top != bTop) return top < bTop ? -1 : 1;
        if (_value.u2 != b._value.u2) return _value.u2 < b._value.u2 ? -1 : 1;
        if (_value.u1 != b._value.u1) return _value.u1 < b._value.u1 ? -1 : 1;
        return _value.u0 == b._value.u0 ? 0 : _value.u0 < b._value.u0 ? -1 : 1;
    }

    public static explicit operator UInt256(Int256 z) => z._value;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool operator <(in Int256 z, in Int256 x)
    {
        // Signed on the top limb, unsigned below: one descending pass, no sign-class branch.
        long top = unchecked((long)z._value.u3);
        long xTop = unchecked((long)x._value.u3);
        if (top != xTop) return top < xTop;
        if (z._value.u2 != x._value.u2) return z._value.u2 < x._value.u2;
        if (z._value.u1 != x._value.u1) return z._value.u1 < x._value.u1;
        return z._value.u0 < x._value.u0;
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool operator >(in Int256 z, in Int256 x) => x < z;

    public static explicit operator Int256(ulong value) => new((UInt256)value);

    public static implicit operator Int256(long value) => new(value);

    public static explicit operator BigInteger(Int256 x)
    {
        Span<byte> bytes = stackalloc byte[32];
        BinaryPrimitives.WriteUInt64LittleEndian(bytes.Slice(0, 8), x._value.u0);
        BinaryPrimitives.WriteUInt64LittleEndian(bytes.Slice(8, 8), x._value.u1);
        BinaryPrimitives.WriteUInt64LittleEndian(bytes.Slice(16, 8), x._value.u2);
        BinaryPrimitives.WriteUInt64LittleEndian(bytes.Slice(24, 8), x._value.u3);
        return new BigInteger(bytes);
    }

    public static explicit operator Int256(BigInteger big) => new(big);

    public TypeCode GetTypeCode() => TypeCode.Object;
    public bool ToBoolean(IFormatProvider? provider) => !IsZero;
    public byte ToByte(IFormatProvider? provider) => System.Convert.ToByte(ToDecimal(provider), provider);
    public char ToChar(IFormatProvider? provider) => System.Convert.ToChar(ToDecimal(provider), provider);
    public DateTime ToDateTime(IFormatProvider? provider) => System.Convert.ToDateTime(ToDecimal(provider), provider);
    public decimal ToDecimal(IFormatProvider? provider) => (decimal)(BigInteger)this;
    public double ToDouble(IFormatProvider? provider) => (double)(BigInteger)this;
    public short ToInt16(IFormatProvider? provider) => System.Convert.ToInt16(ToDecimal(provider), provider);
    public int ToInt32(IFormatProvider? provider) => System.Convert.ToInt32(ToDecimal(provider), provider);
    public long ToInt64(IFormatProvider? provider) => System.Convert.ToInt64(ToDecimal(provider), provider);
    public sbyte ToSByte(IFormatProvider? provider) => System.Convert.ToSByte(ToDecimal(provider), provider);
    public float ToSingle(IFormatProvider? provider) => (float)(BigInteger)this;
    public object ToType(Type conversionType, IFormatProvider? provider) => conversionType == typeof(BigInteger)
        ? (BigInteger)this
        : System.Convert.ChangeType(ToDecimal(provider), conversionType, provider);
    public ushort ToUInt16(IFormatProvider? provider) => System.Convert.ToUInt16(ToDecimal(provider), provider);
    public uint ToUInt32(IFormatProvider? provider) => System.Convert.ToUInt32(ToDecimal(provider), provider);
    public ulong ToUInt64(IFormatProvider? provider) => System.Convert.ToUInt64(ToDecimal(provider), provider);

    public string ToString(IFormatProvider? provider)
    {
        if (IsNegative)
        {
            Neg(out Int256 res);
            return "-" + res._value.ToString(provider);
        }
        return _value.ToString(provider);
    }

    public static void And(in Int256 a, in Int256 b, out Int256 res)
    {
        UInt256.And(in a._value, in b._value, out var o);
        res = new Int256(o);
    }

    public static void Xor(in Int256 a, in Int256 b, out Int256 res)
    {
        UInt256.Xor(in a._value, in b._value, out var o);
        res = new Int256(o);
    }

    public static void Or(in Int256 a, in Int256 b, out Int256 res)
    {
        UInt256.Or(in a._value, in b._value, out var o);
        res = new Int256(o);
    }

    public static void Not(in Int256 a, out Int256 res)
    {
        UInt256.Not(in a._value, out var o);
        res = new Int256(o);
    }
}
