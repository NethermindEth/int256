// SPDX-FileCopyrightText: 2023 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Buffers.Binary;
using System.Diagnostics.CodeAnalysis;
using System.Globalization;
using System.Numerics;
using System.Runtime.CompilerServices;

[assembly: InternalsVisibleTo("Nethermind.Int256.Tests")]

namespace Nethermind.Int256
{
    public readonly struct Int256 :
        IEquatable<Int256>,
        IComparable,
        IComparable<Int256>,
        IConvertible,
        ISpanFormattable,
        ISpanParsable<Int256>,
        IBinaryInteger<Int256>,
        ISignedNumber<Int256>,
        IMinMaxValue<Int256>,
        IInteger<Int256>
    {
        public static readonly Int256 Zero = (Int256)0UL;
        public static readonly Int256 One = (Int256)1UL;
        public static readonly Int256 MinusOne = -1L;
        public static readonly Int256 Max = new Int256(((BigInteger.One << 255) - 1));
        public static readonly Int256 Min = new Int256(-(BigInteger.One << 255));

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

        public int Sign => _value.IsZero ? 0 : _value.u3 < 0x8000000000000000ul ? 1 : -1;
        public bool IsNegative => Sign < 0;

        public static Int256 operator +(in Int256 a, in Int256 b)
        {
            Add(in a, in b, out Int256 res);
            return res;
        }

        public static Int256 operator +(Int256 a, Int256 b)
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
            int aSign = a.Sign;
            int bSign = b.Sign;
            if (aSign < 0)
            {
                a.Neg(out av);
            }
            if (bSign < 0)
            {
                b.Neg(out bv);
            }
            UInt256.Multiply(av._value, bv._value, out UInt256 ures);
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

        [OverloadResolutionPriority(1)]
        private bool Equals(in Int256 other) => _value.Equals(other._value);

        public bool Equals(Int256 other) => _value.Equals(other._value);

        public override bool Equals(object? obj) => obj is Int256 other && Equals(other);

        public override int GetHashCode() => _value.GetHashCode();

        public static bool operator ==(in Int256 a, in Int256 b) => a.Equals(b);

        public static bool operator !=(in Int256 a, in Int256 b) => !(a == b);

        public bool IsZero => this == Zero;

        public bool IsOne => this == One;

        public Int256 ZeroValue => Zero;

        public Int256 OneValue => One;

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

        #region Additional Operators for Interface Compliance

        public static bool operator ==(Int256 a, Int256 b) => a.Equals(b);
        public static bool operator !=(Int256 a, Int256 b) => !a.Equals(b);
        public static bool operator <(Int256 a, Int256 b)
        {
            int aSign = a.Sign;
            int bSign = b.Sign;

            if (aSign >= 0)
            {
                if (bSign < 0)
                    return false;
            }
            else if (bSign >= 0)
            {
                return true;
            }

            return a._value < b._value;
        }
        public static bool operator >(Int256 a, Int256 b) => b < a;
        public static bool operator <=(in Int256 a, in Int256 b) => !(b < a);
        public static bool operator <=(Int256 a, Int256 b) => !(b < a);
        public static bool operator >=(in Int256 a, in Int256 b) => !(a < b);
        public static bool operator >=(Int256 a, Int256 b) => !(a < b);

        public static Int256 operator -(in Int256 a, in Int256 b)
        {
            Subtract(in a, in b, out Int256 res);
            return res;
        }

        public static Int256 operator -(Int256 a, Int256 b)
        {
            Subtract(in a, in b, out Int256 res);
            return res;
        }

        public static Int256 operator *(in Int256 a, in Int256 b)
        {
            Multiply(in a, in b, out Int256 res);
            return res;
        }

        public static Int256 operator *(Int256 a, Int256 b)
        {
            Multiply(in a, in b, out Int256 res);
            return res;
        }

        public static Int256 operator /(in Int256 a, in Int256 b)
        {
            Divide(in a, in b, out Int256 res);
            return res;
        }

        public static Int256 operator /(Int256 a, Int256 b)
        {
            Divide(in a, in b, out Int256 res);
            return res;
        }

        public static Int256 operator %(in Int256 a, in Int256 b)
        {
            Mod(in a, in b, out Int256 res);
            return res;
        }

        public static Int256 operator %(Int256 a, Int256 b)
        {
            Mod(in a, in b, out Int256 res);
            return res;
        }

        public static Int256 operator ++(in Int256 a)
        {
            Add(in a, One, out Int256 res);
            return res;
        }

        public static Int256 operator ++(Int256 a)
        {
            Add(in a, One, out Int256 res);
            return res;
        }

        public static Int256 operator --(in Int256 a)
        {
            Subtract(in a, One, out Int256 res);
            return res;
        }

        public static Int256 operator --(Int256 a)
        {
            Subtract(in a, One, out Int256 res);
            return res;
        }

        public static Int256 operator +(Int256 value) => value;

        public static Int256 operator -(Int256 value)
        {
            Neg(in value, out Int256 res);
            return res;
        }

        public static Int256 operator &(in Int256 a, in Int256 b)
        {
            And(in a, in b, out Int256 res);
            return res;
        }

        public static Int256 operator &(Int256 a, Int256 b)
        {
            And(in a, in b, out Int256 res);
            return res;
        }

        public static Int256 operator |(in Int256 a, in Int256 b)
        {
            Or(in a, in b, out Int256 res);
            return res;
        }

        public static Int256 operator |(Int256 a, Int256 b)
        {
            Or(in a, in b, out Int256 res);
            return res;
        }

        public static Int256 operator ^(in Int256 a, in Int256 b)
        {
            Xor(in a, in b, out Int256 res);
            return res;
        }

        public static Int256 operator ^(Int256 a, Int256 b)
        {
            Xor(in a, in b, out Int256 res);
            return res;
        }

        public static Int256 operator ~(in Int256 a)
        {
            Not(in a, out Int256 res);
            return res;
        }

        public static Int256 operator ~(Int256 a)
        {
            Not(in a, out Int256 res);
            return res;
        }

        public static Int256 operator <<(in Int256 a, int n)
        {
            LeftShift(in a, n, out Int256 res);
            return res;
        }

        public static Int256 operator <<(Int256 a, int n)
        {
            LeftShift(in a, n, out Int256 res);
            return res;
        }

        public static Int256 operator >>(in Int256 a, int n)
        {
            RightShift(in a, n, out Int256 res);
            return res;
        }

        public static Int256 operator >>(Int256 a, int n)
        {
            RightShift(in a, n, out Int256 res);
            return res;
        }

        public static Int256 operator >>>(Int256 value, int shiftAmount)
        {
            UInt256.Rsh(in value._value, shiftAmount, out UInt256 result);
            return new Int256(result);
        }

        #endregion

        #region INumberBase<Int256> Implementation

        static Int256 INumberBase<Int256>.One => One;
        static int INumberBase<Int256>.Radix => 2;
        static Int256 INumberBase<Int256>.Zero => Zero;
        static Int256 IAdditiveIdentity<Int256, Int256>.AdditiveIdentity => Zero;
        static Int256 IMultiplicativeIdentity<Int256, Int256>.MultiplicativeIdentity => One;

        public static Int256 Abs(Int256 value)
        {
            if (value.Sign >= 0)
                return value;
            Neg(in value, out Int256 result);
            return result;
        }

        static bool INumberBase<Int256>.IsCanonical(Int256 value) => true;
        static bool INumberBase<Int256>.IsComplexNumber(Int256 value) => false;
        public static bool IsEvenInteger(Int256 value) => (value._value.u0 & 1) == 0;
        static bool INumberBase<Int256>.IsFinite(Int256 value) => true;
        static bool INumberBase<Int256>.IsImaginaryNumber(Int256 value) => false;
        static bool INumberBase<Int256>.IsInfinity(Int256 value) => false;
        static bool INumberBase<Int256>.IsInteger(Int256 value) => true;
        static bool INumberBase<Int256>.IsNaN(Int256 value) => false;
        static bool INumberBase<Int256>.IsNegative(Int256 value) => value.Sign < 0;
        static bool INumberBase<Int256>.IsNegativeInfinity(Int256 value) => false;
        static bool INumberBase<Int256>.IsNormal(Int256 value) => !value.IsZero;
        public static bool IsOddInteger(Int256 value) => (value._value.u0 & 1) != 0;
        static bool INumberBase<Int256>.IsPositive(Int256 value) => value.Sign >= 0;
        static bool INumberBase<Int256>.IsPositiveInfinity(Int256 value) => false;
        static bool INumberBase<Int256>.IsRealNumber(Int256 value) => true;
        static bool INumberBase<Int256>.IsSubnormal(Int256 value) => false;
        static bool INumberBase<Int256>.IsZero(Int256 value) => value.IsZero;

        public static Int256 MaxMagnitude(Int256 x, Int256 y)
        {
            var absX = Abs(x);
            var absY = Abs(y);
            return absX > absY ? x : y;
        }

        public static Int256 MaxMagnitudeNumber(Int256 x, Int256 y) => MaxMagnitude(x, y);

        public static Int256 MinMagnitude(Int256 x, Int256 y)
        {
            var absX = Abs(x);
            var absY = Abs(y);
            return absX < absY ? x : y;
        }

        public static Int256 MinMagnitudeNumber(Int256 x, Int256 y) => MinMagnitude(x, y);

        public static Int256 Parse(string s, NumberStyles style, IFormatProvider? provider)
            => TryParse(s.AsSpan(), style, provider ?? CultureInfo.InvariantCulture, out Int256 result)
                ? result
                : throw new FormatException();

        public static Int256 Parse(ReadOnlySpan<char> s, NumberStyles style, IFormatProvider? provider)
            => TryParse(s, style, provider ?? CultureInfo.InvariantCulture, out Int256 result)
                ? result
                : throw new FormatException();

        static Int256 ISpanParsable<Int256>.Parse(ReadOnlySpan<char> s, IFormatProvider? provider)
            => TryParse(s, out Int256 result)
                ? result
                : throw new FormatException();

        static Int256 IParsable<Int256>.Parse(string s, IFormatProvider? provider)
            => TryParse(s, out Int256 result)
                ? result
                : throw new FormatException();

        public static bool TryParse([NotNullWhen(true)] string? s, NumberStyles style, IFormatProvider? provider, out Int256 result)
        {
            if (s is null)
            {
                result = Zero;
                return false;
            }
            return TryParse(s.AsSpan(), style, provider, out result);
        }

        public static bool TryParse(ReadOnlySpan<char> s, NumberStyles style, IFormatProvider? provider, out Int256 result)
        {
            if (BigInteger.TryParse(s, style, provider, out BigInteger big))
            {
                result = new Int256(big);
                return true;
            }
            result = Zero;
            return false;
        }

        public static bool TryParse([NotNullWhen(true)] string? s, out Int256 result)
        {
            if (s is null)
            {
                result = Zero;
                return false;
            }
            return TryParse(s.AsSpan(), out result);
        }

        public static bool TryParse(ReadOnlySpan<char> s, out Int256 result)
        {
            bool isHex = s.StartsWith("0x", StringComparison.OrdinalIgnoreCase);
            var style = isHex ? NumberStyles.HexNumber : NumberStyles.Integer;
            var span = isHex ? s[2..] : s;
            return TryParse(span, style, CultureInfo.InvariantCulture, out result);
        }

        static bool ISpanParsable<Int256>.TryParse(ReadOnlySpan<char> s, IFormatProvider? provider, out Int256 result)
            => TryParse(s, out result);

        static bool IParsable<Int256>.TryParse([NotNullWhen(true)] string? s, IFormatProvider? provider, out Int256 result)
            => TryParse(s, out result);

        static bool INumberBase<Int256>.TryConvertFromChecked<TOther>(TOther value, out Int256 result)
            => TryConvertFromChecked(value, out result);

        static bool INumberBase<Int256>.TryConvertFromSaturating<TOther>(TOther value, out Int256 result)
            => TryConvertFromSaturating(value, out result);

        static bool INumberBase<Int256>.TryConvertFromTruncating<TOther>(TOther value, out Int256 result)
            => TryConvertFromTruncating(value, out result);

        static bool INumberBase<Int256>.TryConvertToChecked<TOther>(Int256 value, [MaybeNullWhen(false)] out TOther result)
            => TryConvertToChecked(value, out result);

        static bool INumberBase<Int256>.TryConvertToSaturating<TOther>(Int256 value, [MaybeNullWhen(false)] out TOther result)
            => TryConvertToSaturating(value, out result);

        static bool INumberBase<Int256>.TryConvertToTruncating<TOther>(Int256 value, [MaybeNullWhen(false)] out TOther result)
            => TryConvertToTruncating(value, out result);

        private static bool TryConvertFromChecked<TOther>(TOther value, out Int256 result) where TOther : INumberBase<TOther>
        {
            if (typeof(TOther) == typeof(BigInteger))
            {
                result = new Int256((BigInteger)(object)value);
                return true;
            }
            if (typeof(TOther) == typeof(long))
            {
                result = (long)(object)value;
                return true;
            }
            if (typeof(TOther) == typeof(int))
            {
                result = (Int256)(int)(object)value;
                return true;
            }
            if (typeof(TOther) == typeof(short))
            {
                result = (Int256)(int)(short)(object)value;
                return true;
            }
            if (typeof(TOther) == typeof(sbyte))
            {
                result = (Int256)(int)(sbyte)(object)value;
                return true;
            }
            if (typeof(TOther) == typeof(nint))
            {
                result = new Int256((nint)(object)value);
                return true;
            }
            if (typeof(TOther) == typeof(Int128))
            {
                var v = (Int128)(object)value;
                Span<byte> bytes = stackalloc byte[16];
                System.Buffers.Binary.BinaryPrimitives.WriteInt128LittleEndian(bytes, v);
                Span<byte> fullBytes = stackalloc byte[32];
                bytes.CopyTo(fullBytes);
                if (v < 0)
                    fullBytes[16..].Fill(0xFF);
                result = new Int256(fullBytes, isBigEndian: false);
                return true;
            }
            if (typeof(TOther) == typeof(ulong))
            {
                result = (Int256)(ulong)(object)value;
                return true;
            }
            if (typeof(TOther) == typeof(uint))
            {
                result = (Int256)(ulong)(uint)(object)value;
                return true;
            }
            if (typeof(TOther) == typeof(ushort))
            {
                result = (Int256)(ulong)(ushort)(object)value;
                return true;
            }
            if (typeof(TOther) == typeof(byte))
            {
                result = (Int256)(ulong)(byte)(object)value;
                return true;
            }
            if (typeof(TOther) == typeof(nuint))
            {
                result = (Int256)(ulong)(nuint)(object)value;
                return true;
            }
            if (typeof(TOther) == typeof(UInt128))
            {
                var v = (UInt128)(object)value;
                result = new Int256(new UInt256((ulong)v, (ulong)(v >> 64), 0, 0));
                return true;
            }
            if (typeof(TOther) == typeof(Half))
            {
                var v = (double)(Half)(object)value;
                result = new Int256(new BigInteger(v));
                return true;
            }
            if (typeof(TOther) == typeof(float))
            {
                var v = (float)(object)value;
                result = new Int256(new BigInteger(v));
                return true;
            }
            if (typeof(TOther) == typeof(double))
            {
                var v = (double)(object)value;
                result = new Int256(new BigInteger(v));
                return true;
            }
            if (typeof(TOther) == typeof(decimal))
            {
                var v = (decimal)(object)value;
                result = new Int256(new BigInteger(v));
                return true;
            }

            result = default;
            return false;
        }

        private static bool TryConvertFromSaturating<TOther>(TOther value, out Int256 result) where TOther : INumberBase<TOther>
        {
            if (typeof(TOther) == typeof(double))
            {
                var v = (double)(object)value;
                if (double.IsNaN(v) || double.IsNegativeInfinity(v))
                {
                    result = Min;
                    return true;
                }
                if (double.IsPositiveInfinity(v))
                {
                    result = Max;
                    return true;
                }
            }
            if (typeof(TOther) == typeof(float))
            {
                var v = (float)(object)value;
                if (float.IsNaN(v) || float.IsNegativeInfinity(v))
                {
                    result = Min;
                    return true;
                }
                if (float.IsPositiveInfinity(v))
                {
                    result = Max;
                    return true;
                }
            }
            if (typeof(TOther) == typeof(Half))
            {
                var v = (Half)(object)value;
                if (Half.IsNaN(v) || Half.IsNegativeInfinity(v))
                {
                    result = Min;
                    return true;
                }
                if (Half.IsPositiveInfinity(v))
                {
                    result = Max;
                    return true;
                }
            }
            return TryConvertFromChecked(value, out result);
        }

        private static bool TryConvertFromTruncating<TOther>(TOther value, out Int256 result) where TOther : INumberBase<TOther>
            => TryConvertFromChecked(value, out result);

        private static bool TryConvertToChecked<TOther>(Int256 value, [MaybeNullWhen(false)] out TOther result) where TOther : INumberBase<TOther>
        {
            if (typeof(TOther) == typeof(BigInteger))
            {
                result = (TOther)(object)(BigInteger)value;
                return true;
            }
            if (typeof(TOther) == typeof(long))
            {
                result = (TOther)(object)value.ToInt64(null);
                return true;
            }
            if (typeof(TOther) == typeof(int))
            {
                result = (TOther)(object)value.ToInt32(null);
                return true;
            }
            if (typeof(TOther) == typeof(short))
            {
                result = (TOther)(object)value.ToInt16(null);
                return true;
            }
            if (typeof(TOther) == typeof(sbyte))
            {
                result = (TOther)(object)value.ToSByte(null);
                return true;
            }
            if (typeof(TOther) == typeof(nint))
            {
                var big = (BigInteger)value;
                if (big < nint.MinValue || big > nint.MaxValue)
                    throw new OverflowException();
                result = (TOther)(object)(nint)big;
                return true;
            }
            if (typeof(TOther) == typeof(Int128))
            {
                var big = (BigInteger)value;
                if (big < (BigInteger)Int128.MinValue || big > (BigInteger)Int128.MaxValue)
                    throw new OverflowException();
                result = (TOther)(object)(Int128)big;
                return true;
            }
            if (typeof(TOther) == typeof(ulong))
            {
                result = (TOther)(object)value.ToUInt64(null);
                return true;
            }
            if (typeof(TOther) == typeof(uint))
            {
                result = (TOther)(object)value.ToUInt32(null);
                return true;
            }
            if (typeof(TOther) == typeof(ushort))
            {
                result = (TOther)(object)value.ToUInt16(null);
                return true;
            }
            if (typeof(TOther) == typeof(byte))
            {
                result = (TOther)(object)value.ToByte(null);
                return true;
            }
            if (typeof(TOther) == typeof(nuint))
            {
                var big = (BigInteger)value;
                if (big < 0 || big > nuint.MaxValue)
                    throw new OverflowException();
                result = (TOther)(object)(nuint)(ulong)big;
                return true;
            }
            if (typeof(TOther) == typeof(UInt128))
            {
                var big = (BigInteger)value;
                if (big < 0 || big > (BigInteger)UInt128.MaxValue)
                    throw new OverflowException();
                result = (TOther)(object)(UInt128)big;
                return true;
            }
            if (typeof(TOther) == typeof(double))
            {
                result = (TOther)(object)value.ToDouble(null);
                return true;
            }
            if (typeof(TOther) == typeof(float))
            {
                result = (TOther)(object)value.ToSingle(null);
                return true;
            }
            if (typeof(TOther) == typeof(Half))
            {
                result = (TOther)(object)(Half)value.ToDouble(null);
                return true;
            }
            if (typeof(TOther) == typeof(decimal))
            {
                result = (TOther)(object)value.ToDecimal(null);
                return true;
            }

            result = default;
            return false;
        }

        private static bool TryConvertToSaturating<TOther>(Int256 value, [MaybeNullWhen(false)] out TOther result) where TOther : INumberBase<TOther>
        {
            if (typeof(TOther) == typeof(byte))
            {
                var big = (BigInteger)value;
                result = (TOther)(object)(big < 0 ? (byte)0 : big > byte.MaxValue ? byte.MaxValue : (byte)big);
                return true;
            }
            if (typeof(TOther) == typeof(ushort))
            {
                var big = (BigInteger)value;
                result = (TOther)(object)(big < 0 ? (ushort)0 : big > ushort.MaxValue ? ushort.MaxValue : (ushort)big);
                return true;
            }
            if (typeof(TOther) == typeof(uint))
            {
                var big = (BigInteger)value;
                result = (TOther)(object)(big < 0 ? 0u : big > uint.MaxValue ? uint.MaxValue : (uint)big);
                return true;
            }
            if (typeof(TOther) == typeof(ulong))
            {
                var big = (BigInteger)value;
                result = (TOther)(object)(big < 0 ? 0ul : big > ulong.MaxValue ? ulong.MaxValue : (ulong)big);
                return true;
            }
            if (typeof(TOther) == typeof(nuint))
            {
                var big = (BigInteger)value;
                result = (TOther)(object)(big < 0 ? (nuint)0 : big > nuint.MaxValue ? nuint.MaxValue : (nuint)(ulong)big);
                return true;
            }
            if (typeof(TOther) == typeof(UInt128))
            {
                if (value.Sign < 0)
                {
                    result = (TOther)(object)UInt128.Zero;
                    return true;
                }
                if ((value._value.u2 | value._value.u3) != 0)
                {
                    result = (TOther)(object)UInt128.MaxValue;
                    return true;
                }
                result = (TOther)(object)new UInt128(value._value.u1, value._value.u0);
                return true;
            }
            if (typeof(TOther) == typeof(sbyte))
            {
                var big = (BigInteger)value;
                result = (TOther)(object)(big < sbyte.MinValue ? sbyte.MinValue : big > sbyte.MaxValue ? sbyte.MaxValue : (sbyte)big);
                return true;
            }
            if (typeof(TOther) == typeof(short))
            {
                var big = (BigInteger)value;
                result = (TOther)(object)(big < short.MinValue ? short.MinValue : big > short.MaxValue ? short.MaxValue : (short)big);
                return true;
            }
            if (typeof(TOther) == typeof(int))
            {
                var big = (BigInteger)value;
                result = (TOther)(object)(big < int.MinValue ? int.MinValue : big > int.MaxValue ? int.MaxValue : (int)big);
                return true;
            }
            if (typeof(TOther) == typeof(long))
            {
                var big = (BigInteger)value;
                result = (TOther)(object)(big < long.MinValue ? long.MinValue : big > long.MaxValue ? long.MaxValue : (long)big);
                return true;
            }
            if (typeof(TOther) == typeof(nint))
            {
                var big = (BigInteger)value;
                result = (TOther)(object)(big < nint.MinValue ? nint.MinValue : big > nint.MaxValue ? nint.MaxValue : (nint)big);
                return true;
            }
            if (typeof(TOther) == typeof(Int128))
            {
                var big = (BigInteger)value;
                result = (TOther)(object)(big < (BigInteger)Int128.MinValue ? Int128.MinValue : big > (BigInteger)Int128.MaxValue ? Int128.MaxValue : (Int128)big);
                return true;
            }
            return TryConvertToChecked(value, out result);
        }

        private static bool TryConvertToTruncating<TOther>(Int256 value, [MaybeNullWhen(false)] out TOther result) where TOther : INumberBase<TOther>
        {
            if (typeof(TOther) == typeof(BigInteger))
            {
                result = (TOther)(object)(BigInteger)value;
                return true;
            }
            if (typeof(TOther) == typeof(long))
            {
                result = (TOther)(object)(long)value._value.u0;
                return true;
            }
            if (typeof(TOther) == typeof(int))
            {
                result = (TOther)(object)(int)value._value.u0;
                return true;
            }
            if (typeof(TOther) == typeof(short))
            {
                result = (TOther)(object)(short)value._value.u0;
                return true;
            }
            if (typeof(TOther) == typeof(sbyte))
            {
                result = (TOther)(object)(sbyte)value._value.u0;
                return true;
            }
            if (typeof(TOther) == typeof(nint))
            {
                result = (TOther)(object)(nint)value._value.u0;
                return true;
            }
            if (typeof(TOther) == typeof(Int128))
            {
                result = (TOther)(object)new Int128(value._value.u1, value._value.u0);
                return true;
            }
            if (typeof(TOther) == typeof(ulong))
            {
                result = (TOther)(object)value._value.u0;
                return true;
            }
            if (typeof(TOther) == typeof(uint))
            {
                result = (TOther)(object)(uint)value._value.u0;
                return true;
            }
            if (typeof(TOther) == typeof(ushort))
            {
                result = (TOther)(object)(ushort)value._value.u0;
                return true;
            }
            if (typeof(TOther) == typeof(byte))
            {
                result = (TOther)(object)(byte)value._value.u0;
                return true;
            }
            if (typeof(TOther) == typeof(nuint))
            {
                result = (TOther)(object)(nuint)value._value.u0;
                return true;
            }
            if (typeof(TOther) == typeof(UInt128))
            {
                result = (TOther)(object)new UInt128(value._value.u1, value._value.u0);
                return true;
            }
            if (typeof(TOther) == typeof(double))
            {
                result = (TOther)(object)value.ToDouble(null);
                return true;
            }
            if (typeof(TOther) == typeof(float))
            {
                result = (TOther)(object)value.ToSingle(null);
                return true;
            }
            if (typeof(TOther) == typeof(Half))
            {
                result = (TOther)(object)(Half)value.ToDouble(null);
                return true;
            }
            if (typeof(TOther) == typeof(decimal))
            {
                result = (TOther)(object)value.ToDecimal(null);
                return true;
            }

            result = default;
            return false;
        }

        #endregion

        #region INumber<Int256> Implementation

        public static Int256 Clamp(Int256 value, Int256 min, Int256 max)
        {
            if (min > max)
                throw new ArgumentException($"'{min}' cannot be greater than '{max}'.");
            if (value < min)
                return min;
            if (value > max)
                return max;
            return value;
        }

        public static Int256 CopySign(Int256 value, Int256 sign)
        {
            var absValue = Abs(value);
            return sign.Sign < 0 ? -absValue : absValue;
        }

        static int INumber<Int256>.Sign(Int256 value) => value.Sign;

        #endregion

        #region IBinaryInteger<Int256> Implementation

        public static (Int256 Quotient, Int256 Remainder) DivRem(Int256 left, Int256 right)
        {
            Divide(in left, in right, out Int256 quotient);
            Mod(in left, in right, out Int256 remainder);
            return (quotient, remainder);
        }

        public static Int256 LeadingZeroCount(Int256 value)
        {
            if (value.Sign < 0)
                return Zero;
            return (Int256)(ulong)UInt256.LeadingZeroCount(value._value);
        }

        public static Int256 PopCount(Int256 value)
            => (Int256)(ulong)UInt256.PopCount(value._value);

        public static Int256 TrailingZeroCount(Int256 value)
            => (Int256)(ulong)UInt256.TrailingZeroCount(value._value);

        public static bool TryReadBigEndian(ReadOnlySpan<byte> source, bool isUnsigned, out Int256 value)
        {
            if (source.Length < 32)
            {
                value = default;
                return false;
            }

            value = new Int256(source[..32], isBigEndian: true);
            return true;
        }

        public static bool TryReadLittleEndian(ReadOnlySpan<byte> source, bool isUnsigned, out Int256 value)
        {
            if (source.Length < 32)
            {
                value = default;
                return false;
            }

            value = new Int256(source[..32], isBigEndian: false);
            return true;
        }

        public int GetByteCount() => 32;

        public int GetShortestBitLength()
        {
            if (Sign >= 0)
                return _value.BitLen;

            Neg(out Int256 abs);
            return abs._value.BitLen + 1;
        }

        public bool TryWriteBigEndian(Span<byte> destination, out int bytesWritten)
        {
            if (destination.Length < 32)
            {
                bytesWritten = 0;
                return false;
            }

            _value.ToBigEndian(destination[..32]);
            bytesWritten = 32;
            return true;
        }

        public bool TryWriteLittleEndian(Span<byte> destination, out int bytesWritten)
        {
            if (destination.Length < 32)
            {
                bytesWritten = 0;
                return false;
            }

            _value.ToLittleEndian(destination[..32]);
            bytesWritten = 32;
            return true;
        }

        static Int256 IBinaryInteger<Int256>.RotateLeft(Int256 value, int rotateAmount)
        {
            rotateAmount &= 255;
            if (rotateAmount == 0) return value;
            LeftShift(in value, rotateAmount, out Int256 left);
            RightShift(in value, 256 - rotateAmount, out Int256 right);
            return left | right;
        }

        static Int256 IBinaryInteger<Int256>.RotateRight(Int256 value, int rotateAmount)
        {
            rotateAmount &= 255;
            if (rotateAmount == 0) return value;
            RightShift(in value, rotateAmount, out Int256 right);
            LeftShift(in value, 256 - rotateAmount, out Int256 left);
            return right | left;
        }

        #endregion

        #region IBinaryNumber<Int256> Implementation

        static bool IBinaryNumber<Int256>.IsPow2(Int256 value)
        {
            if (value.Sign <= 0)
                return false;
            int popCount = BitOperations.PopCount(value._value.u0) +
                          BitOperations.PopCount(value._value.u1) +
                          BitOperations.PopCount(value._value.u2) +
                          BitOperations.PopCount(value._value.u3);
            return popCount == 1;
        }

        static Int256 IBinaryNumber<Int256>.Log2(Int256 value)
        {
            if (value.Sign <= 0)
                throw new ArgumentException("Cannot compute Log2 of zero or negative number");
            return (Int256)(ulong)(255 - (int)(ulong)UInt256.LeadingZeroCount(value._value));
        }

        #endregion

        #region ISignedNumber<Int256> Implementation

        static Int256 ISignedNumber<Int256>.NegativeOne => MinusOne;

        #endregion

        #region IMinMaxValue<Int256> Implementation

        static Int256 IMinMaxValue<Int256>.MinValue => Min;
        static Int256 IMinMaxValue<Int256>.MaxValue => Max;

        #endregion

        #region ISpanFormattable Implementation

        public bool TryFormat(Span<char> destination, out int charsWritten, ReadOnlySpan<char> format, IFormatProvider? provider)
        {
            var bigInt = (BigInteger)this;
            return bigInt.TryFormat(destination, out charsWritten, format, provider);
        }

        public string ToString(string? format, IFormatProvider? formatProvider)
            => ((BigInteger)this).ToString(format, formatProvider);

        #endregion
    }
}
