using System;
using System.Buffers.Binary;
using System.Numerics;
using System.Runtime.CompilerServices;

namespace Nethermind.Int256
{
    public readonly struct Int256 : IComparable, IComparable<Int256>, IInteger<Int256>
    {
        public static readonly Int256 Zero = (Int256)0UL;
        public static readonly Int256 One = (Int256)1UL;
        public static readonly Int256 MinusOne = -1L;
        public static readonly Int256 Max = new Int256(((BigInteger.One << 255) - 1));

        private readonly UInt256 value;

        public Int256(ReadOnlySpan<byte> bytes, bool isBigEndian)
        {
            this.value = new UInt256(bytes, isBigEndian);
        }

        public Int256(UInt256 value)
        {
            this.value = value;
        }

        public Int256(BigInteger big)
        {
            if (big.Sign < 0)
            {
                (new Int256((UInt256)(-big))).Neg(out Int256 neg);
                this.value = neg.value;
            }
            else
            {
                this.value = (UInt256)big;
            }
        }

        public Int256(int n)
        {
            if (n < 0)
            {
                var value = new Int256(new UInt256((ulong)-n));
                value.Neg(out Int256 res);
                this.value = res.value;
            }
            else
            {
                this.value = new UInt256((ulong)n);
            }
        }

        public static explicit operator Int256(int n)
        {
            return new Int256(n);
        }

        public Int256 OneValue => One;

        public Int256 ZeroValue => Zero;

        public int Sign
        {
            get
            {
                if (value.IsZero)
                {
                    return 0;
                }
                if (value.u3 < 0x8000000000000000ul)
                {
                    return 1;
                }
                return -1;
            }
        }

        public static void Add(in Int256 a, in Int256 b, out Int256 res)
        {
            UInt256.Add(a.value, b.value, out UInt256 ures);
            res = new Int256(ures);
        }

        public void Add(in Int256 a, out Int256 res) => Add(this, a, out res);

        public static void AddMod(in Int256 x, in Int256 y, in Int256 m, out Int256 res)
        {
            var mt = m;
            if (mt.IsOne)
            {
                res = Int256.Zero;
                return;
            }

            if (m.Sign < 0)
            {
                m.Neg(out mt);
            }
            int xSign = x.Sign;
            int ySign = y.Sign;
            if (xSign < 0 && ySign < 0)
            {
                x.Neg(out Int256 xNeg);
                y.Neg(out Int256 yNeg);
                xNeg.value.AddMod(yNeg.value, mt.value, out UInt256 ures);
                res = new Int256(ures);
                res.Neg(out res);
            }
            else if (xSign > 0 && ySign > 0)
            {
                x.value.AddMod(y.value, mt.value, out UInt256 ures);
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
            a.value.Subtract(b.value, out UInt256 ures);
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

            if (m.Sign < 0)
            {
                m.Neg(out mt);
            }
            int xSign = x.Sign;
            int ySign = y.Sign;
            if (xSign < 0 && ySign > 0)
            {
                x.Neg(out Int256 xNeg);
                xNeg.value.AddMod(y.value, mt.value, out UInt256 ures);
                res = new Int256(ures);
                res.Neg(out res);
            }
            else if (xSign > 0 && ySign < 0)
            {
                y.Neg(out Int256 yNeg);
                x.value.AddMod(yNeg.value, mt.value, out UInt256 ures);
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
            Int256 av = a, bv = b;
            if (a.Sign < 0)
            {
                a.Neg(out av);
            }
            if (b.Sign < 0)
            {
                b.Neg(out bv);
            }
            UInt256.Multiply(av.value, bv.value, out UInt256 ures);
            res = new Int256(ures);
            int aSign = a.Sign;
            int bSign = b.Sign;
            if ((aSign < 0 && bSign < 0) || (aSign >= 0 && bSign >= 0))
            {
                return;
            }
            res.Neg(out res);
        }

        public void Multiply(in Int256 a, out Int256 res) => Multiply(this, a, out res);

        public static void MultiplyMod(in Int256 x, in Int256 y, in Int256 m, out Int256 res)
        {
            var mAbs = m;
            if (m.Sign < 0)
            {
                m.Neg(out mAbs);
            }
            int xSign = x.Sign;
            int ySign = y.Sign;
            if ((xSign < 0 && ySign >= 0) || (xSign >= 0 && ySign < 0))
            {
                var xAbs = x;
                var yAbs = y;
                if (xSign < 0)
                {
                    x.Neg(out xAbs);
                }
                else
                {
                    y.Neg(out yAbs);
                }
                xAbs.value.MultiplyMod(yAbs.value, mAbs.value, out UInt256 ures);
                res = new Int256(ures);
                res.Neg(out res);
            }
            else
            {
                var xAbs = x;
                var yAbs = y;
                if (xSign < 0)
                {
                    x.Neg(out xAbs);
                    y.Neg(out yAbs);
                }
                xAbs.value.MultiplyMod(yAbs.value, mAbs.value, out UInt256 ures);
                res = new Int256(ures);
            }
        }

        public void MultiplyMod(in Int256 a, in Int256 m, out Int256 res) => MultiplyMod(this, a, m, out res);

        public static void Divide(in Int256 n, in Int256 d, out Int256 res)
        {
            UInt256 value;
            if (n.Sign >= 0)
            {
                if (d.Sign >= 0)
                {
                    // pos / pos
                    UInt256.Divide(n.value, d.value, out value);
                    res = new Int256(value);
                    return;
                }
                else
                {
                    // pos / neg
                    Neg(d, out Int256 neg);
                    UInt256.Divide(n.value, neg.value, out value);
                    res = new Int256(value);
                    res.Neg(out res);
                    return;
                }
            }

            Neg(n, out Int256 nNeg);
            if (d.Sign < 0)
            {
                // neg / neg
                Neg(d, out Int256 dNeg);
                UInt256.Divide(nNeg.value, dNeg.value, out value);
                res = new Int256(value);
                return;
            }
            // neg / pos
            UInt256.Divide(nNeg.value, d.value, out value);
            res = new Int256(value);
            res.Neg(out res);
        }

        public void Divide(in Int256 a, out Int256 res) => Divide(this, a, out res);

        public static void Exp(in Int256 b, in Int256 e, out Int256 res)
        {
            if (e.Sign < 0)
            {
                throw new ArgumentException("exponent must be non-negative");
            }
            if (b.Sign < 0)
            {
                b.Neg(out Int256 neg);
                UInt256.Exp(neg.value, e.value, out UInt256 ures);
                if (!e.value.Bit(0))
                {
                    res = new Int256(ures);
                }
                else
                {
                    res = new Int256(ures);
                    res.Neg(out res);
                }
            }
            else
            {
                UInt256.Exp(b.value, e.value, out UInt256 ures);
                res = new Int256(ures);
            }
        }

        public void Exp(in Int256 exp, out Int256 res) => Exp(this, exp, out res);

        public static void ExpMod(in Int256 bs, in Int256 exp, in Int256 m, out Int256 res)
        {
            if (exp < Zero)
            {
                throw new ArgumentException("exponent must not be negative");
            }
            Int256 bv = bs;
            bool switchSign = false;
            if (bs.Sign < 0)
            {
                bv.Neg(out bv);
                switchSign = exp.value.Bit(0);
            }
            var mAbs = m;
            if (mAbs.Sign < 0)
            {
                mAbs.Neg(out mAbs);
            }
            UInt256.ExpMod(bv.value, exp.value, mAbs.value, out UInt256 ures);
            res = new Int256(ures);
            if (switchSign)
            {
                res.Neg(out res);
            }
        }

        public void ExpMod(in Int256 exp, in Int256 m, out Int256 res) => ExpMod(this, exp, m, out res);

        public static void LeftShift(in Int256 x, int n, out Int256 res)
        {
            x.value.LeftShift(n, out UInt256 ures);
            res = new Int256(ures);
        }

        // Mod sets res to (sign x) * { abs(x) modulus abs(y) }
        // If y == 0, z is set to 0 (OBS: differs from the big.Int)
        public static void Mod(in Int256 x, in Int256 y, out Int256 res)
        {
            Int256 xIn = x, yIn = y;
            int xs = x.Sign;

            // abs x
            if (xs == -1)
            {
                Neg(x, out xIn);
            }
            // abs y
            if (y.Sign == -1)
            {
                Neg(y, out yIn);
            }
            UInt256.Mod((UInt256)xIn, (UInt256)yIn, out UInt256 value);
            res = new Int256(value);
            if (xs == -1)
            {
                Neg(res, out res);
            }
        }

        public void Mod(in Int256 m, out Int256 res) => Mod(this, m, out res);

        // Abs sets res to the absolute value
        //   Abs(0)        = 0
        //   Abs(1)        = 1
        //   Abs(2**255)   = -2**255
        //   Abs(2**256-1) = -1
        public void Abs(out Int256 res)
        {
            if (Sign >= 0)
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
            UInt256.Subtract(UInt256.Zero, x.value, out UInt256 value);
            neg = new Int256(value);
        }

        public void Neg(out Int256 res) => Neg(this, out res);

        public void LeftShift(int n, out Int256 res) => LeftShift(this, n, out res);

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static long Rsh(long a, int n)
        {
            var n1 = n / 2;
            var n2 = n - n1;
            return (a >> n1) >> n2;
        }

        private void Srsh64(out Int256 res)
        {
            res = new Int256(new UInt256(this.value.u1, this.value.u2, this.value.u3, ulong.MaxValue));
        }

        private void Srsh128(out Int256 res)
        {
            res = new Int256(new UInt256(this.value.u2, this.value.u3, ulong.MaxValue, ulong.MaxValue));
        }

        private void Srsh192(out Int256 res)
        {
            res = new Int256(new UInt256(this.value.u3, ulong.MaxValue, ulong.MaxValue, ulong.MaxValue));
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static void Rsh(in Int256 x, int n, out Int256 res)
        {
            if (x.Sign >= 0)
            {
                x.value.RightShift(n, out UInt256 ures);
                res = new Int256(ures);
                return;
            }
            if (n % 64 == 0)
            {
                switch (n)
                {
                    case 0:
                        res = x;
                        return;
                    case 64:
                        x.Srsh64(out res);
                        return;
                    case 128:
                        x.Srsh128(out res);
                        return;
                    case 192:
                        x.Srsh192(out res);
                        return;
                    default:
                        One.Neg(out res);
                        return;
                }
            }
            res = x;
            ulong z0 = x.value.u0, z1 = x.value.u1, z2 = x.value.u2, z3 = x.value.u3;
            ulong a = UInt256.Lsh(ulong.MaxValue, 64 - (n % 64));
            // Big swaps first
            if (n > 192)
            {
                if (n > 256)
                {
                    One.Neg(out res);
                    return;
                }
                x.Srsh192(out res);
                z0 = res.value.u0;
                z1 = res.value.u1;
                z2 = res.value.u2;
                z3 = res.value.u3;
                n -= 192;
                goto sh192;
            }
            else if (n > 128)
            {
                x.Srsh128(out res);
                z0 = res.value.u0;
                z1 = res.value.u1;
                z2 = res.value.u2;
                z3 = res.value.u3;
                n -= 128;
                goto sh128;
            }
            else if (n > 64)
            {
                x.Srsh64(out res);
                z0 = res.value.u0;
                z1 = res.value.u1;
                z2 = res.value.u2;
                z3 = res.value.u3;
                n -= 64;
                goto sh64;
            }
            else
            {
                res = x;
                z0 = res.value.u0;
                z1 = res.value.u1;
                z2 = res.value.u2;
                z3 = res.value.u3;
            }

            // remaining shifts
            z3 = UInt256.Rsh(res.value.u3, n) | a;
            a = UInt256.Lsh(res.value.u3, 64 - n);

        sh64:
            z2 = UInt256.Rsh(res.value.u2, n) | a;
            a = UInt256.Lsh(res.value.u2, 64 - n);

        sh128:
            z1 = UInt256.Rsh(res.value.u1, n) | a;
            a = UInt256.Lsh(res.value.u1, 64 - n);

        sh192:
            z0 = UInt256.Rsh(res.value.u0, n) | a;

            res = new Int256(new UInt256(z0, z1, z2, z3));
        }

        public static void RightShift(in Int256 x, int n, out Int256 res)
        {
            Rsh(x, n, out res);
        }

        public void RightShift(int n, out Int256 res) => RightShift(this, n, out res);

        public void Convert(out BigInteger big)
        {
            if (Sign < 0)
            {
                Abs(out Int256 res);
                res.value.Convert(out big);
                big = -big;
            }
            else
            {
                value.Convert(out big);
            }
        }

        public override string ToString()
        {
            if (Sign < 0)
            {
                Neg(out Int256 res);
                return "-" + res.value.ToString();
            }
            return value.ToString();
        }

        private bool Equals(in Int256 other) => value.Equals(other.value);

        public override bool Equals(object? obj)
        {
            return obj is Int256 other && Equals(other);
        }

        public override int GetHashCode() => value.GetHashCode();

        public static bool operator ==(in Int256 a, in Int256 b) => a.Equals(b);

        public static bool operator !=(in Int256 a, in Int256 b) => !(a == b);

        public bool IsZero => this == Zero;

        public bool IsOne => this == One;

        public Int256 MaximalValue => Max;

        public int CompareTo(object? obj)
        {
            if (!(obj is Int256))
            {
                throw new InvalidOperationException();
            }

            return CompareTo((Int256) obj);
        }

        public int CompareTo(Int256 b)
        {
            if (this < b)
            {
                return -1;
            }

            if (Equals(b))
            {
                return 0;
            }

            return 1;
        }

        public static explicit operator UInt256(Int256 z) => z.value;

        public static bool operator <(in Int256 z, in Int256 x)
        {
            int zSign = z.Sign;
            int xSign = x.Sign;

            if (zSign >= 0)
            {
                if (xSign < 0)
                {
                    return false;
                }
            }
            else if (xSign >= 0)
            {
                return true;
            }

            return z.value < x.value;
        }
        public static bool operator >(in Int256 z, in Int256 x) => x < z;

        public static explicit operator Int256(ulong value)
        {
            return new Int256((UInt256)value);
        }

        public static implicit operator Int256(long value)
        {
            return new Int256(value);
        }

        public static explicit operator BigInteger(Int256 x)
        {
            Span<byte> bytes = stackalloc byte[32];
            BinaryPrimitives.WriteUInt64LittleEndian(bytes.Slice(0, 8), x.value.u0);
            BinaryPrimitives.WriteUInt64LittleEndian(bytes.Slice(8, 8), x.value.u1);
            BinaryPrimitives.WriteUInt64LittleEndian(bytes.Slice(16, 8), x.value.u2);
            BinaryPrimitives.WriteUInt64LittleEndian(bytes.Slice(24, 8), x.value.u3);
            return new BigInteger(bytes);
        }

        public static explicit operator Int256(BigInteger big)
        {
            return new Int256(big);
        }
    }
}
