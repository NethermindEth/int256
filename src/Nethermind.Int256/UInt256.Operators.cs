// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    public static bool operator ==(in UInt256 a, int b) => a.Equals(b);
    public static bool operator ==(int a, in UInt256 b) => b.Equals(a);
    public static bool operator ==(in UInt256 a, uint b) => a.Equals(b);
    public static bool operator ==(uint a, in UInt256 b) => b.Equals(a);
    public static bool operator ==(in UInt256 a, long b) => a.Equals(b);
    public static bool operator ==(long a, in UInt256 b) => b.Equals(a);
    public static bool operator ==(in UInt256 a, ulong b) => a.Equals(b);
    public static bool operator ==(ulong a, in UInt256 b) => b.Equals(a);
    public static bool operator !=(in UInt256 a, int b) => !a.Equals(b);
    public static bool operator !=(int a, in UInt256 b) => !b.Equals(a);
    public static bool operator !=(in UInt256 a, uint b) => !a.Equals(b);
    public static bool operator !=(uint a, in UInt256 b) => !b.Equals(a);
    public static bool operator !=(in UInt256 a, long b) => !a.Equals(b);
    public static bool operator !=(long a, in UInt256 b) => !b.Equals(a);
    public static bool operator !=(in UInt256 a, ulong b) => !a.Equals(b);
    public static bool operator !=(ulong a, in UInt256 b) => !b.Equals(a);
    public static explicit operator UInt256(sbyte a) =>
        a < 0 ? throw new ArgumentException($"Expected a positive number and got {a}", nameof(a)) : new UInt256((ulong)a);

    public static implicit operator UInt256(byte a) => new(a);

    public static explicit operator UInt256(short a) =>
        a < 0 ? throw new ArgumentException($"Expected a positive number and got {a}", nameof(a)) : new UInt256((ulong)a);

    public static implicit operator UInt256(ushort a) => new(a);

    public static explicit operator UInt256(int n) =>
        n < 0 ? throw new ArgumentException("n < 0") : new UInt256((ulong)n);

    public static implicit operator UInt256(uint a) => new(a);

    public static explicit operator UInt256(long a) =>
        a < 0 ? throw new ArgumentException($"Expected a positive number and got {a}", nameof(a)) : new UInt256((ulong)a);

    public static UInt256 operator ^(in UInt256 a, in UInt256 b)
    {
        Xor(a, b, out UInt256 res);
        return res;
    }

    public static UInt256 operator ~(in UInt256 a)
    {
        Not(in a, out UInt256 res);
        return res;
    }

    public static UInt256 operator +(in UInt256 a, in UInt256 b)
    {
        AddOverflow(in a, in b, out UInt256 res);
        return res;
    }

    public static UInt256 operator ++(in UInt256 a)
    {
        AddOverflow(in a, 1, out UInt256 res);
        return res;
    }

    public static UInt256 operator -(in UInt256 a, in UInt256 b)
    {
        if (SubtractUnderflow(in a, in b, out UInt256 c))
        {
            ThrowOverflowException($"Underflow in subtraction {a} - {b}");
        }

        return c;
    }

    public static bool operator ==(in UInt256 a, in UInt256 b) => a.Equals(b);

    public static bool operator !=(in UInt256 a, in UInt256 b) => !(a == b);

    public static implicit operator UInt256(ulong value) => new UInt256(value, 0ul, 0ul, 0ul);

    public static explicit operator UInt256(in BigInteger value)
    {
        byte[] bytes32 = value.ToBytes32(true);
        return new UInt256(bytes32, true);
    }

    public static explicit operator BigInteger(in UInt256 value)
    {
        ReadOnlySpan<byte> bytes = MemoryMarshal.CreateReadOnlySpan(ref Unsafe.As<UInt256, byte>(ref Unsafe.AsRef(in value)), 32);
        return new BigInteger(bytes, true);
    }

    public static explicit operator sbyte(in UInt256 a) =>
        a.u1 > 0 || a.u2 > 0 || a.u3 > 0 || a.u0 > (long)sbyte.MaxValue
            ? throw new OverflowException("Cannot convert UInt256 value to sbyte.")
            : (sbyte)a.u0;

    public static explicit operator byte(in UInt256 a) =>
        a.u1 > 0 || a.u2 > 0 || a.u3 > 0 || a.u0 > byte.MaxValue
            ? throw new OverflowException("Cannot convert UInt256 value to byte.")
            : (byte)a.u0;

    public static explicit operator short(in UInt256 a) =>
        a.u1 > 0 || a.u2 > 0 || a.u3 > 0 || a.u0 > (long)short.MaxValue
            ? throw new OverflowException("Cannot convert UInt256 value to short.")
            : (short)a.u0;

    public static explicit operator ushort(in UInt256 a) =>
        a.u1 > 0 || a.u2 > 0 || a.u3 > 0 || a.u0 > ushort.MaxValue
            ? throw new OverflowException("Cannot convert UInt256 value to ushort.")
            : (ushort)a.u0;

    public static explicit operator int(in UInt256 a) =>
        a.u1 > 0 || a.u2 > 0 || a.u3 > 0 || a.u0 > int.MaxValue
            ? throw new OverflowException("Cannot convert UInt256 value to int.")
            : (int)a.u0;

    public static explicit operator uint(in UInt256 a) =>
        a.u1 > 0 || a.u2 > 0 || a.u3 > 0 || a.u0 > uint.MaxValue
            ? throw new OverflowException("Cannot convert UInt256 value to uint.")
            : (uint)a.u0;

    public static explicit operator long(in UInt256 a) =>
        a.u1 > 0 || a.u2 > 0 || a.u3 > 0 || a.u0 > long.MaxValue
            ? throw new OverflowException("Cannot convert UInt256 value to long.")
            : (long)a.u0;

    public static explicit operator ulong(in UInt256 a) =>
        a.u1 > 0 || a.u2 > 0 || a.u3 > 0
            ? throw new OverflowException("Cannot convert UInt256 value to ulong.")
            : a.u0;

    public static UInt256 operator *(in UInt256 a, uint b)
    {
        UInt256 ub = b;
        Multiply(in a, in ub, out UInt256 c);
        return c;
    }

    public static UInt256 operator *(uint a, in UInt256 b)
    {
        UInt256 ua = a;
        Multiply(in ua, in b, out UInt256 c);
        return c;
    }

    public static UInt256 operator *(in UInt256 a, ulong b)
    {
        UInt256 ub = b;
        Multiply(in a, in ub, out UInt256 c);
        return c;
    }

    public static UInt256 operator *(ulong a, in UInt256 b)
    {
        UInt256 ua = a;
        Multiply(in ua, in b, out UInt256 c);
        return c;
    }

    public static UInt256 operator *(in UInt256 a, in UInt256 b)
    {
        Multiply(in a, in b, out UInt256 c);
        return c;
    }

    public static UInt256 operator /(in UInt256 a, uint b)
    {
        UInt256 ub = b;
        Divide(in a, in ub, out UInt256 c);
        return c;
    }

    public static UInt256 operator /(in UInt256 a, in UInt256 b)
    {
        Divide(in a, in b, out UInt256 c);
        return c;
    }

    public static bool operator <(in UInt256 a, in UInt256 b) => LessThan(in a, in b);
    public static bool operator <(in UInt256 a, int b) => LessThan(in a, b);
    public static bool operator <(int a, in UInt256 b) => LessThan(a, in b);
    public static bool operator <(in UInt256 a, uint b) => LessThan(in a, b);
    public static bool operator <(uint a, in UInt256 b) => LessThan(a, in b);
    public static bool operator <(in UInt256 a, long b) => LessThan(in a, b);
    public static bool operator <(long a, in UInt256 b) => LessThan(a, in b);
    public static bool operator <(in UInt256 a, ulong b) => LessThan(in a, b);
    public static bool operator <(ulong a, in UInt256 b) => LessThan(a, in b);
    public static bool operator <=(in UInt256 a, in UInt256 b) => !LessThan(in b, in a);
    public static bool operator <=(in UInt256 a, int b) => !LessThan(b, in a);
    public static bool operator <=(int a, in UInt256 b) => !LessThan(in b, a);
    public static bool operator <=(in UInt256 a, uint b) => !LessThan(b, in a);
    public static bool operator <=(uint a, in UInt256 b) => !LessThan(in b, a);
    public static bool operator <=(in UInt256 a, long b) => !LessThan(b, in a);
    public static bool operator <=(long a, in UInt256 b) => !LessThan(in b, a);
    public static bool operator <=(in UInt256 a, ulong b) => !LessThan(b, in a);
    public static bool operator <=(ulong a, UInt256 b) => !LessThan(in b, a);
    public static bool operator >(in UInt256 a, in UInt256 b) => LessThan(in b, in a);
    public static bool operator >(in UInt256 a, int b) => LessThan(b, in a);
    public static bool operator >(int a, in UInt256 b) => LessThan(in b, a);
    public static bool operator >(in UInt256 a, uint b) => LessThan(b, in a);
    public static bool operator >(uint a, in UInt256 b) => LessThan(in b, a);
    public static bool operator >(in UInt256 a, long b) => LessThan(b, in a);
    public static bool operator >(long a, in UInt256 b) => LessThan(in b, a);
    public static bool operator >(in UInt256 a, ulong b) => LessThan(b, in a);
    public static bool operator >(ulong a, in UInt256 b) => LessThan(in b, a);
    public static bool operator >=(in UInt256 a, in UInt256 b) => !LessThan(in a, in b);
    public static bool operator >=(in UInt256 a, int b) => !LessThan(in a, b);
    public static bool operator >=(int a, in UInt256 b) => !LessThan(a, in b);
    public static bool operator >=(in UInt256 a, uint b) => !LessThan(in a, b);
    public static bool operator >=(uint a, in UInt256 b) => !LessThan(a, in b);
    public static bool operator >=(in UInt256 a, long b) => !LessThan(in a, b);
    public static bool operator >=(long a, in UInt256 b) => !LessThan(a, in b);
    public static bool operator >=(in UInt256 a, ulong b) => !LessThan(in a, b);
    public static bool operator >=(ulong a, in UInt256 b) => !LessThan(a, in b);

    public static UInt256 operator <<(in UInt256 a, int n)
    {
        a.LeftShift(n, out UInt256 res);
        return res;
    }

    public static UInt256 operator >>(in UInt256 a, int n)
    {
        a.RightShift(n, out UInt256 res);
        return res;
    }

    public static UInt256 operator |(in UInt256 a, in UInt256 b)
    {
        Or(a, b, out UInt256 res);
        return res;
    }

    public static UInt256 operator &(in UInt256 a, in UInt256 b)
    {
        And(a, b, out UInt256 res);
        return res;
    }
    public static explicit operator double(in UInt256 a)
    {
        double multiplier = ulong.MaxValue;
        return (((a.u3 * multiplier) + a.u2) * multiplier + a.u1) * multiplier + a.u0;
    }

    public static explicit operator UInt256(double a)
    {
        UInt256 c;
        bool negate = false;
        if (a < 0)
        {
            negate = true;
            a = -a;
        }

        if (a <= ulong.MaxValue)
        {
            ulong cu0 = (ulong)a;
            ulong cu1 = 0;
            ulong cu2 = 0;
            ulong cu3 = 0;
            c = new UInt256(cu0, cu1, cu2, cu3);
        }
        else
        {
            int shift = Math.Max((int)Math.Ceiling(Math.Log(a, 2)) - 63, 0);
            ulong cu0 = (ulong)(a / Math.Pow(2, shift));
            ulong cu1 = 0;
            ulong cu2 = 0;
            ulong cu3 = 0;
            c = new UInt256(cu0, cu1, cu2, cu3);
            c.LeftShift(shift, out c);
        }

        if (negate)
            Negate(in c);

        return c;
    }

    public static explicit operator decimal(in UInt256 a) => (decimal)(BigInteger)a;

    public static explicit operator UInt256(decimal a)
    {
        int[] bits = decimal.GetBits(decimal.Truncate(a));
        UInt256 c = new((uint)bits[0], (uint)bits[1], (uint)bits[2], 0, 0, 0, 0, 0);
        return a < 0 ? Negate(c) : c;
    }
}
