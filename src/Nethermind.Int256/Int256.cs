using System;
using System.Buffers.Binary;
using System.Numerics;
using System.Runtime.CompilerServices;

[assembly: InternalsVisibleTo("Nethermind.Int256.Test")]

namespace Nethermind.Int256
{
    public readonly struct Int256 : IComparable, IComparable<Int256>, IInteger<Int256>, IConvertible
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

        public int Sign => _value.IsZero ? 0 : _value.u3 < 0x8000000000000000ul ? 1 : -1;
        public bool IsNegative => Sign < 0;

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
            UInt256.Add(a._value, b._value, out UInt256 ures);
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
                xNeg._value.AddMod(yNeg._value, mt._value, out UInt256 ures);
                res = new Int256(ures);
                res.Neg(out res);
            }
            else if (xSign > 0 && ySign > 0)
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

            if (m.Sign < 0)
            {
                m.Neg(out mt);
            }
            int xSign = x.Sign;
            int ySign = y.Sign;
            if (xSign < 0 && ySign > 0)
            {
                x.Neg(out Int256 xNeg);
                xNeg._value.AddMod(y._value, mt._value, out UInt256 ures);
                res = new Int256(ures);
                res.Neg(out res);
            }
            else if (xSign > 0 && ySign < 0)
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
            Int256 av = a, bv = b;
            if (a.Sign < 0)
            {
                a.Neg(out av);
            }
            if (b.Sign < 0)
            {
                b.Neg(out bv);
            }
            UInt256.Multiply(av._value, bv._value, out UInt256 ures);
            int aSign = a.Sign;
            int bSign = b.Sign;
            res = new Int256(ures);
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
                xAbs._value.MultiplyMod(yAbs._value, mAbs._value, out UInt256 ures);
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
                xAbs._value.MultiplyMod(yAbs._value, mAbs._value, out UInt256 ures);
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
            if (d.Sign < 0)
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
            if (e.Sign < 0)
            {
                throw new ArgumentException("exponent must be non-negative");
            }
            if (b.Sign < 0)
            {
                b.Neg(out Int256 neg);
                UInt256.Exp(neg._value, e._value, out UInt256 ures);
                if (!e._value.Bit(0))
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
                UInt256.Exp(b._value, e._value, out UInt256 ures);
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
                switchSign = exp._value.Bit(0);
            }
            var mAbs = m;
            if (mAbs.Sign < 0)
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
            UInt256.Subtract(UInt256.Zero, x._value, out UInt256 value);
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
            res = new Int256(new UInt256(_value.u1, _value.u2, _value.u3, ulong.MaxValue));
        }

        private void Srsh128(out Int256 res)
        {
            res = new Int256(new UInt256(_value.u2, _value.u3, ulong.MaxValue, ulong.MaxValue));
        }

        private void Srsh192(out Int256 res)
        {
            res = new Int256(new UInt256(_value.u3, ulong.MaxValue, ulong.MaxValue, ulong.MaxValue));
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static void Rsh(in Int256 x, int n, out Int256 res)
        {
            if (x.Sign >= 0)
            {
                x._value.RightShift(n, out UInt256 ures);
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
            ulong z0 = x._value.u0, z1 = x._value.u1, z2 = x._value.u2, z3 = x._value.u3;
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
                z0 = res._value.u0;
                z1 = res._value.u1;
                z2 = res._value.u2;
                z3 = res._value.u3;
                n -= 192;
                goto sh192;
            }
            else if (n > 128)
            {
                x.Srsh128(out res);
                z0 = res._value.u0;
                z1 = res._value.u1;
                z2 = res._value.u2;
                z3 = res._value.u3;
                n -= 128;
                goto sh128;
            }
            else if (n > 64)
            {
                x.Srsh64(out res);
                z0 = res._value.u0;
                z1 = res._value.u1;
                z2 = res._value.u2;
                z3 = res._value.u3;
                n -= 64;
                goto sh64;
            }
            else
            {
                res = x;
                z0 = res._value.u0;
                z1 = res._value.u1;
                z2 = res._value.u2;
                z3 = res._value.u3;
            }

            // remaining shifts
            z3 = UInt256.Rsh(res._value.u3, n) | a;
            a = UInt256.Lsh(res._value.u3, 64 - n);

        sh64:
            z2 = UInt256.Rsh(res._value.u2, n) | a;
            a = UInt256.Lsh(res._value.u2, 64 - n);

        sh128:
            z1 = UInt256.Rsh(res._value.u1, n) | a;
            a = UInt256.Lsh(res._value.u1, 64 - n);

        sh192:
            z0 = UInt256.Rsh(res._value.u0, n) | a;

            res = new Int256(new UInt256(z0, z1, z2, z3));
        }

        public static void RightShift(in Int256 x, int n, out Int256 res) => Rsh(x, n, out res);

        public void RightShift(int n, out Int256 res) => RightShift(this, n, out res);

        public void Convert(out BigInteger big)
        {
            if (Sign < 0)
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

        private bool Equals(in Int256 other) => _value.Equals(other._value);

        public override bool Equals(object? obj) => obj is Int256 other && Equals(other);

        public override int GetHashCode() => _value.GetHashCode();

        public static bool operator ==(in Int256 a, in Int256 b) => a.Equals(b);

        public static bool operator !=(in Int256 a, in Int256 b) => !(a == b);

        public bool IsZero => this == Zero;

        public bool IsOne => this == One;

        public Int256 MaximalValue => Max;

        public int CompareTo(object? obj) => obj is not Int256 int256 ? throw new InvalidOperationException() : CompareTo(int256);

        public int CompareTo(Int256 b) => this < b ? -1 : Equals(b) ? 0 : 1;

        public static explicit operator UInt256(Int256 z) => z._value;

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

            return z._value < x._value;
        }
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
}
