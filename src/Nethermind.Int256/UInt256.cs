using System;
using System.Buffers.Binary;
using System.Globalization;
using System.Linq;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

[assembly: InternalsVisibleTo("Nethermind.Int256.Test")]

namespace Nethermind.Int256
{
    [StructLayout(LayoutKind.Explicit)]
    public readonly struct UInt256 : IComparable, IComparable<UInt256>, IInteger<UInt256>
    {
        public static readonly UInt256 Zero = 0ul;
        public static readonly UInt256 One = 1ul;
        public static readonly UInt256 MinValue = Zero;
        public static readonly UInt256 MaxValue = ~Zero;
        public static readonly UInt256 UInt128MaxValue = new UInt256(ulong.MaxValue, ulong.MaxValue, 0, 0);

        /* in little endian order so u3 is the most significant ulong */

        [FieldOffset(0)]
        public readonly ulong u0;
        [FieldOffset(8)]
        public readonly ulong u1;
        [FieldOffset(16)]
        public readonly ulong u2;
        [FieldOffset(24)]
        public readonly ulong u3;

        public UInt256(uint r0, uint r1, uint r2, uint r3, uint r4, uint r5, uint r6, uint r7)
        {
            u0 = (ulong)r1 << 32 | r0;
            u1 = (ulong)r3 << 32 | r2;
            u2 = (ulong)r5 << 32 | r4;
            u3 = (ulong)r7 << 32 | r6;
        }

        public UInt256(ulong u0, ulong u1, ulong u2, ulong u3)
        {
            this.u0 = u0;
            this.u1 = u1;
            this.u2 = u2;
            this.u3 = u3;
        }

        public UInt256(ReadOnlySpan<byte> bytes, bool isBigEndian = false)
        {
            if (bytes.Length == 32)
            {
                if (isBigEndian)
                {
                    u3 = BinaryPrimitives.ReadUInt64BigEndian(bytes.Slice(0, 8));
                    u2 = BinaryPrimitives.ReadUInt64BigEndian(bytes.Slice(8, 8));
                    u1 = BinaryPrimitives.ReadUInt64BigEndian(bytes.Slice(16, 8));
                    u0 = BinaryPrimitives.ReadUInt64BigEndian(bytes.Slice(24, 8));
                }
                else
                {
                    u0 = BinaryPrimitives.ReadUInt64LittleEndian(bytes.Slice(0, 8));
                    u1 = BinaryPrimitives.ReadUInt64LittleEndian(bytes.Slice(8, 8));
                    u2 = BinaryPrimitives.ReadUInt64LittleEndian(bytes.Slice(16, 8));
                    u3 = BinaryPrimitives.ReadUInt64LittleEndian(bytes.Slice(24, 8));
                }
            }
            else
            {
                int byteCount = bytes.Length;
                int unalignedBytes = byteCount % 8;
                int dwordCount = byteCount / 8 + (unalignedBytes == 0 ? 0 : 1);

                ulong cs0 = 0;
                ulong cs1 = 0;
                ulong cs2 = 0;
                ulong cs3 = 0;

                if (dwordCount == 0)
                {
                    u0 = u1 = u2 = u3 = 0;
                    return;
                }

                if (dwordCount >= 1)
                {
                    for (int j = 8; j > 0; j--)
                    {
                        cs0 = cs0 << 8;
                        if (j <= byteCount)
                        {
                            cs0 = cs0 | bytes[byteCount - j];
                        }
                    }
                }

                if (dwordCount >= 2)
                {
                    for (int j = 16; j > 8; j--)
                    {
                        cs1 = cs1 << 8;
                        if (j <= byteCount)
                        {
                            cs1 = cs1 | bytes[byteCount - j];
                        }
                    }
                }

                if (dwordCount >= 3)
                {
                    for (int j = 24; j > 16; j--)
                    {
                        cs2 = cs2 << 8;
                        if (j <= byteCount)
                        {
                            cs2 = cs2 | bytes[byteCount - j];
                        }
                    }
                }

                if (dwordCount >= 4)
                {
                    for (int j = 32; j > 24; j--)
                    {
                        cs3 = cs3 << 8;
                        if (j <= byteCount)
                        {
                            cs3 = cs3 | bytes[byteCount - j];
                        }
                    }
                }

                u0 = cs0;
                u1 = cs1;
                u2 = cs2;
                u3 = cs3;
            }
        }

        public UInt256(ReadOnlySpan<ulong> data, bool isBigEndian = false)
        {
            if (isBigEndian)
            {
                u3 = data[0];
                u2 = data[1];
                u1 = data[2];
                u0 = data[3];
            }
            else
            {
                u0 = data[0];
                u1 = data[1];
                u2 = data[2];
                u3 = data[3];
            }
        }

        public UInt256(ulong n) : this(n, 0, 0, 0)
        {
        }

        public static explicit operator double(in UInt256 a)
        {
            if (a.u1 == 0)
                return a.u0;
            return a.u1 * (double)ulong.MaxValue + a.u0;
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

        private uint r0 => (uint)u0;
        private uint r1 => (uint)(u0 >> 32);
        private uint r2 => (uint)u1;
        private uint r3 => (uint)(u1 >> 32);

        public static explicit operator decimal(in UInt256 a)
        {
            if (a.u1 == 0)
                return a.u0;
            var shift = Math.Max(0, 32 - GetBitLength(a.u1));
            Rsh(in a, shift, out UInt256 aShift);
            return new decimal((int)aShift.r0, (int)aShift.r1, (int)aShift.r2, false, (byte)shift);
        }

        public static explicit operator UInt256(decimal a)
        {
            var bits = decimal.GetBits(decimal.Truncate(a));
            UInt256 c = new UInt256((uint)bits[0], (uint)bits[1], (uint)bits[2], 0, 0, 0, 0, 0);
            return a < 0 ? Negate(c) : c;
        }

        private static int GetBitLength(ulong value)
        {
            var r1 = value >> 32;
            if (r1 != 0)
                return GetBitLength((uint)r1) + 32;
            return GetBitLength((uint)value);
        }

        private static int GetBitLength(uint value)
        {
            var tt = value >> 16;
            if (tt != 0)
            {
                var t = tt >> 8;
                if (t != 0)
                    return bitLength[t] + 24;
                return bitLength[tt] + 16;
            }
            else
            {
                var t = value >> 8;
                if (t != 0)
                    return bitLength[t] + 8;
                return bitLength[value];
            }
        }

        // TODO: this is very allocaty / slow
        private static byte[] bitLength = Enumerable.Range(0, byte.MaxValue + 1)
            .Select(value =>
            {
                int count;
                for (count = 0; value != 0; count++)
                    value >>= 1;
                return (byte)count;
            }).ToArray();

        public static UInt256 Negate(in UInt256 a)
        {
            ulong cs0 = 0 - a.u0;
            ulong cs1 = 0 - a.u1;
            ulong cs2 = 0 - a.u2;
            ulong cs3 = 0 - a.u3;
            if (a.u0 > 0)
                cs3--;

            return new UInt256(cs0, cs1, cs2, cs3);
        }

        public (ulong value, bool overflow) UlongWithOverflow => (this.u0, (this.u1 | this.u2 | this.u3) != 0);

        public bool IsZero => (u0 | u1 | u2 | u3) == 0;
        
        public bool IsOne => ((u0 ^ 1UL) | u1 | u2 | u3) == 0;

        public bool IsZeroOrOne => ((u0 >> 1) | u1 | u2 | u3) == 0;

        public UInt256 ZeroValue => Zero;
        
        public UInt256 OneValue => One;

        public UInt256 MaximalValue => MaxValue;

        // Add sets res to the sum a+b
        public static void Add(in UInt256 a, in UInt256 b, out UInt256 res)
        {
            ulong carry = 0ul;
            AddWithCarry(a.u0, b.u0, ref carry, out ulong res1);
            AddWithCarry(a.u1, b.u1, ref carry, out ulong res2);
            AddWithCarry(a.u2, b.u2, ref carry, out ulong res3);
            AddWithCarry(a.u3, b.u3, ref carry, out ulong res4);
            res = new UInt256(res1, res2, res3, res4);
            // #if DEBUG
            //             Debug.Assert((BigInteger)res == ((BigInteger)a + (BigInteger)b) % ((BigInteger)1 << 256));
            // #endif
        }

        public void Add(in UInt256 a, out UInt256 res) => Add(this, a, out res);

        /// <summary>
        /// AddOverflow sets res to the sum a+b, and returns whether overflow occurred
        /// </summary>
        /// <param name="a"></param>
        /// <param name="b"></param>
        /// <param name="res"></param>
        /// <returns></returns>
        public static bool AddOverflow(in UInt256 a, in UInt256 b, out UInt256 res)
        {
            ulong carry = 0ul;
            AddWithCarry(a.u0, b.u0, ref carry, out ulong res1);
            AddWithCarry(a.u1, b.u1, ref carry, out ulong res2);
            AddWithCarry(a.u2, b.u2, ref carry, out ulong res3);
            AddWithCarry(a.u3, b.u3, ref carry, out ulong res4);
            res = new UInt256(res1, res2, res3, res4);
            return carry != 0;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static void AddWithCarry(ulong x, ulong y, ref ulong carry, out ulong sum)
        {
            sum = x + y + carry;
            // both msb bits are 1 or one of them is 1 and we had carry from lower bits
            carry = ((x & y) | ((x | y) & (~sum))) >> 63;
        }

        // AddMod sets res to the sum ( x+y ) mod m.
        // If m == 0, z is set to 0 (OBS: differs from the big.Int)
        public static void AddMod(in UInt256 x, in UInt256 y, in UInt256 m, out UInt256 res)
        {
            if (m.IsZero)
            {
                res = Zero;
                return;
            }

            if (AddOverflow(x, y, out res))
            {
                const int length = 5;
                Span<ulong> sum = stackalloc ulong[length] { res.u0, res.u1, res.u2, res.u3, 1 };
                Span<ulong> quot = stackalloc ulong[length];
                Udivrem(ref MemoryMarshal.GetReference(quot), ref MemoryMarshal.GetReference(sum), length, in m, out res);
            }
            else
            {
                Mod(res, m, out res);
            }
        }

        public void AddMod(in UInt256 a, in UInt256 m, out UInt256 res) => AddMod(this, a, m, out res);

        public byte[] PaddedBytes(int n)
        {
            var b = new byte[n];

            for (int i = 0; i < 32 && i < n; i++)
            {
                b[n - 1 - i] = (byte)(this[i / 8] >> (int)(8 * (i % 8)));
            }

            return b;
        }

        public byte[] ToBigEndian()
        {
            byte[] bytes = new byte[32];
            ToBigEndian(bytes);
            return bytes;
        }

        public byte[] ToLittleEndian()
        {
            byte[] bytes = new byte[32];
            ToLittleEndian(bytes);
            return bytes;
        }

        public void ToBigEndian(Span<byte> target)
        {
            if (target.Length == 32)
            {
                BinaryPrimitives.WriteUInt64BigEndian(target.Slice(0, 8), u3);
                BinaryPrimitives.WriteUInt64BigEndian(target.Slice(8, 8), u2);
                BinaryPrimitives.WriteUInt64BigEndian(target.Slice(16, 8), u1);
                BinaryPrimitives.WriteUInt64BigEndian(target.Slice(24, 8), u0);
            }
            else if (target.Length == 20)
            {
                BinaryPrimitives.WriteUInt32BigEndian(target.Slice(0, 4), (uint)u2);
                BinaryPrimitives.WriteUInt64BigEndian(target.Slice(4, 8), u1);
                BinaryPrimitives.WriteUInt64BigEndian(target.Slice(12, 8), u0);
            }
        }

        public void ToLittleEndian(Span<byte> target)
        {
            if (target.Length == 32)
            {
                BinaryPrimitives.WriteUInt64LittleEndian(target.Slice(0, 8), u3);
                BinaryPrimitives.WriteUInt64LittleEndian(target.Slice(8, 8), u2);
                BinaryPrimitives.WriteUInt64LittleEndian(target.Slice(16, 8), u1);
                BinaryPrimitives.WriteUInt64LittleEndian(target.Slice(24, 8), u0);
            }
            else
            {
                throw new NotSupportedException();
            }
        }

        // Mod sets res to the modulus x%y for y != 0.
        // If y == 0, z is set to 0 (OBS: differs from the big.Int)
        public static void Mod(in UInt256 x, in UInt256 y, out UInt256 res)
        {
            if (x.IsZero || y.IsZeroOrOne)
            {
                res = Zero;
                return;
            }

            switch (x.CompareTo(y))
            {
                case -1:
                    res = x;
                    return;
                case 0:
                    res = Zero;
                    return;
            }
            // At this point:
            // x != 0
            // y != 0
            // x > y

            // Shortcut trivial case
            if (x.IsUint64)
            {
                res = (UInt256)(((ulong)x) % ((ulong)y));
                return;
            }

            const int length = 4;
            Span<ulong> quot = stackalloc ulong[length];
            Udivrem(ref MemoryMarshal.GetReference(quot), ref Unsafe.As<UInt256, ulong>(ref Unsafe.AsRef(in x)), length, y, out res);
        }

        public void Mod(in UInt256 m, out UInt256 res) => Mod(this, m, out res);

        private static readonly byte[] len8tab = new byte[] {
          0x00, 0x01, 0x02, 0x02, 0x03, 0x03, 0x03, 0x03, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04,
          0x05, 0x05, 0x05, 0x05, 0x05, 0x05, 0x05, 0x05, 0x05, 0x05, 0x05, 0x05, 0x05, 0x05, 0x05, 0x05,
          0x06, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06,
          0x06, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06,
          0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07,
          0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07,
          0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07,
          0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07,
          0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08,
          0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08,
          0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08,
          0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08,
          0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08,
          0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08,
          0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08,
          0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08, 0x08,
        };

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public static int Len64(ulong x)
        {
            int n = 0;
            if (x >= (1ul << 32))
            {
                x >>= 32;
                n = 32;
            }
            if (x >= (1ul << 16))
            {
                x >>= 16;
                n += 16;
            }
            if (x >= (1ul << 8))
            {
                x >>= 8;
                n += 8;
            }

            return n + len8tab[x];
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static int LeadingZeros(ulong x) => 64 - Len64(x);

        // It avoids c#'s way of shifting a 64-bit number by 64-bit, i.e. in c# a << 64 == a, in our version a << 64 == 0.
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        internal static ulong Lsh(ulong a, int n)
        {
            var n1 = n >> 1;
            var n2 = n - n1;
            return (a << n1) << n2;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        internal static ulong Rsh(ulong a, int n)
        {
            var n1 = n >> 1;
            var n2 = n - n1;
            return (a >> n1) >> n2;
        }

        // Udivrem divides u by d and produces both quotient and remainder.
        // The quotient is stored in provided quot - len(u)-len(d)+1 words.
        // It loosely follows the Knuth's division algorithm (sometimes referenced as "schoolbook" division) using 64-bit words.
        // See Knuth, Volume 2, section 4.3.1, Algorithm D.
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static void Udivrem(ref ulong quot, ref ulong u, int length, in UInt256 d, out UInt256 rem)
        {
            int dLen = 0;
            int shift = 0;
            if (d.u3 != 0)
            {
                dLen = 4;
                shift = LeadingZeros(d.u3);
            }
            else if (d.u2 != 0)
            {
                dLen = 3;
                shift = LeadingZeros(d.u2);
            }
            else if (d.u1 != 0)
            {
                dLen = 2;
                shift = LeadingZeros(d.u1);
            }
            else if (d.u0 != 0)
            {
                dLen = 1;
                shift = LeadingZeros(d.u0);
            }

            int uLen = 0;
            for (int i = length - 1; i >= 0; i--)
            {
                if (Unsafe.Add(ref u,i) != 0)
                {
                    uLen = i + 1;
                    break;
                }
            }

            Span<ulong> un = stackalloc ulong[uLen + 1];
            un[uLen] = Rsh(Unsafe.Add(ref u, uLen - 1), 64 - shift);
            for (int i = uLen - 1; i > 0; i--)
            {
                un[i] = Lsh(Unsafe.Add(ref u, i), shift) | Rsh(Unsafe.Add(ref u, i - 1), 64 - shift);
            }

            un[0] = Lsh(u, shift);

            // TODO: Skip the highest word of numerator if not significant.

            if (dLen == 1)
            {
                ulong dnn0 = Lsh(d.u0, shift);
                ulong r = UdivremBy1(ref quot, un, dnn0);
                r = Rsh(r, shift);
                rem = (UInt256)r;
                return;
            }

            ulong dn0 = Lsh(d.u0, shift);
            ulong dn1 = 0;
            ulong dn2 = 0;
            ulong dn3 = 0;
            switch (dLen)
            {
                case 4:
                    dn3 = Lsh(d.u3, shift) | Rsh(d.u2, 64 - shift);
                    goto case 3;
                case 3:
                    dn2 = Lsh(d.u2, shift) | Rsh(d.u1, 64 - shift);
                    goto case 2;
                case 2:
                    dn1 = Lsh(d.u1, shift) | Rsh(d.u0, 64 - shift);
                    break;
            }
            Span<ulong> dnS = stackalloc ulong[4] { dn0, dn1, dn2, dn3 };
            dnS = dnS.Slice(0, dLen);

            UdivremKnuth(ref quot, un, dnS);

            ulong rem0 = 0, rem1 = 0, rem2 = 0, rem3 = 0;
            switch (dLen)
            {
                case 1:
                    rem0 = Rsh(un[dLen - 1], shift);
                    goto r0;
                case 2:
                    rem1 = Rsh(un[dLen - 1], shift);
                    goto r1;
                case 3:
                    rem2 = Rsh(un[dLen - 1], shift);
                    goto r2;
                case 4:
                    rem3 = Rsh(un[dLen - 1], shift);
                    goto r3;
            }

            r3:
            rem2 = Rsh(un[2], shift) | Lsh(un[3], 64 - shift);
            r2:
            rem1 = Rsh(un[1], shift) | Lsh(un[2], 64 - shift);
            r1:
            rem0 = Rsh(un[0], shift) | Lsh(un[1], 64 - shift);
            r0:

            rem = new UInt256(rem0, rem1, rem2, rem3);
        }

        // UdivremKnuth implements the division of u by normalized multiple word d from the Knuth's division algorithm.
        // The quotient is stored in provided quot - len(u)-len(d) words.
        // Updates u to contain the remainder - len(d) words.
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static void UdivremKnuth(ref ulong quot, Span<ulong> u, Span<ulong> d)
        {
            var dh = d[d.Length - 1];
            var dl = d[d.Length - 2];
            var reciprocal = Reciprocal2by1(dh);

            for (int j = u.Length - d.Length - 1; j >= 0; j--)
            {
                var u2 = u[j + d.Length];
                var u1 = u[j + d.Length - 1];
                var u0 = u[j + d.Length - 2];

                ulong qhat, rhat;
                if (u2 >= dh)
                {
                    qhat = ~((ulong)0);
                    // TODO: Add "qhat one to big" adjustment (not needed for correctness, but helps avoiding "add back" case).
                }
                else
                {
                    (qhat, rhat) = Udivrem2by1(u2, u1, dh, reciprocal);
                    (ulong ph, ulong pl) = Multiply64(qhat, dl);
                    if (ph > rhat || (ph == rhat && pl > u0))
                    {
                        qhat--;
                        // TODO: Add "qhat one to big" adjustment (not needed for correctness, but helps avoiding "add back" case).
                    }
                }

                // Multiply and subtract.
                var borrow = SubMulTo(u.Slice(j), d, qhat);
                u[j + d.Length] = u2 - borrow;
                if (u2 < borrow)
                {
                    // Too much subtracted, add back.
                    qhat--;
                    u[j + d.Length] += AddTo(u.Slice(j), d);
                }

                Unsafe.Add(ref quot, j) = qhat; // Store quotient digit.
            }
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static ulong SubMulTo(Span<ulong> x, Span<ulong> y, ulong multiplier)
        {
            ulong borrow = 0;
            for (int i = 0; i < y.Length; i++)
            {
                ulong s = 0, borrow1 = 0;
                SubtractWithBorrow(x[i], borrow, ref borrow1, out s);
                (ulong ph, ulong pl) = Multiply64(y[i], multiplier);
                ulong t = 0, borrow2 = 0;
                SubtractWithBorrow(s, pl, ref borrow2, out t);
                x[i] = t;
                borrow = ph + borrow1 + borrow2;
            }

            return borrow;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static ulong AddTo(Span<ulong> x, Span<ulong> y)
        {
            ulong carry = 0;
            for (int i = 0; i < y.Length; i++)
            {
                AddWithCarry(x[i], y[i], ref carry, out x[i]);
            }

            return carry;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static ulong UdivremBy1(ref ulong quot, Span<ulong> u, ulong d)
        {
            var reciprocal = Reciprocal2by1(d);
            ulong rem;
            rem = u[u.Length - 1]; // Set the top word as remainder.
            for (int j = u.Length - 2; j >= 0; j--)
            {
                (Unsafe.Add(ref quot, j), rem) = Udivrem2by1(rem, u[j], d, reciprocal);
            }

            return rem;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static ulong Reciprocal2by1(ulong d)
        {
            var (reciprocal, _) = Div64(~d, ~((ulong)0), d);
            return reciprocal;
        }

        // Udivrem2by1 divides <uh, ul> / d and produces both quotient and remainder.
        // It uses the provided d's reciprocal.
        // Implementation ported from https://github.com/chfast/intx and is based on
        // "Improved division by invariant integers", Algorithm 4.
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static (ulong quot, ulong rem) Udivrem2by1(ulong uh, ulong ul, ulong d, ulong reciprocal)
        {
            (ulong qh, ulong ql) = Multiply64(reciprocal, uh);
            ulong carry = 0;
            AddWithCarry(ql, ul, ref carry, out ql);
            AddWithCarry(qh, uh, ref carry, out qh);
            qh++;

            var r = ul - qh * d;

            if (r > ql)
            {
                qh--;
                r += d;
            }

            if (r >= d)
            {
                qh++;
                r -= d;
            }

            return (qh, r);
        }

        // Subtract sets res to the difference a-b
        public static void Subtract(in UInt256 a, in UInt256 b, out UInt256 res)
        {
            ulong carry = 0ul;
            SubtractWithBorrow(a.u0, b.u0, ref carry, out ulong res0);
            SubtractWithBorrow(a.u1, b.u1, ref carry, out ulong res1);
            SubtractWithBorrow(a.u2, b.u2, ref carry, out ulong res2);
            SubtractWithBorrow(a.u3, b.u3, ref carry, out ulong res3);
            res = new UInt256(res0, res1, res2, res3);

            // #if DEBUG
            //             Debug.Assert((BigInteger)res == ((BigInteger)a - (BigInteger)b + ((BigInteger)1 << 256)) % ((BigInteger)1 << 256));
            // #endif
        }

        public void Subtract(in UInt256 b, out UInt256 res) => Subtract(this, b, out res);

        public static void SubtractMod(in UInt256 a, in UInt256 b, in UInt256 m, out UInt256 res)
        {
            if (SubtractUnderflow(a, b, out res))
            {
                Subtract(b, a, out res);
            }

            Mod(res, m, out res);
        }

        public void SubtractMod(in UInt256 a, in UInt256 m, out UInt256 res) => SubtractMod(this, a, m, out res);

        // SubtractUnderflow sets res to the difference a-b and returns true if the operation underflowed
        public static bool SubtractUnderflow(in UInt256 a, in UInt256 b, out UInt256 res)
        {
            ulong borrow = 0;
            SubtractWithBorrow(a[0], b[0], ref borrow, out ulong z0);
            SubtractWithBorrow(a[1], b[1], ref borrow, out ulong z1);
            SubtractWithBorrow(a[2], b[2], ref borrow, out ulong z2);
            SubtractWithBorrow(a[3], b[3], ref borrow, out ulong z3);
            res = new UInt256(z0, z1, z2, z3);
            return borrow != 0;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static void SubtractWithBorrow(ulong a, ulong b, ref ulong borrow, out ulong res)
        {
            res = a - b - borrow;
            borrow = (((~a) & b) | (~(a ^ b)) & res) >> 63;
        }

        // Multiply sets res to the product x*y
        public static void Multiply(in UInt256 x, in UInt256 y, out UInt256 res)
        {
            ref ulong rx = ref Unsafe.As<UInt256, ulong>(ref Unsafe.AsRef(in x));
            ref ulong ry = ref Unsafe.As<UInt256, ulong>(ref Unsafe.AsRef(in y));

            ulong carry;
            ulong res1, res2, res3, r0, r1, r2, r3;

            (carry, r0) = Multiply64(rx, ry);
            UmulHop(carry, Unsafe.Add(ref rx, 1), ry, out carry, out res1);
            UmulHop(carry, Unsafe.Add(ref rx, 2), ry, out carry, out res2);
            res3 = Unsafe.Add(ref rx, 3) * ry + carry;

            UmulHop(res1, rx, Unsafe.Add(ref ry, 1), out carry, out r1);
            UmulStep(res2, Unsafe.Add(ref rx, 1), Unsafe.Add(ref ry, 1), carry, out carry, out res2);
            res3 = res3 + Unsafe.Add(ref rx, 2) * Unsafe.Add(ref ry, 1) + carry;

            UmulHop(res2, rx, Unsafe.Add(ref ry, 2), out carry, out r2);
            res3 = res3 + Unsafe.Add(ref rx, 1) * Unsafe.Add(ref ry, 2) + carry;

            r3 = res3 + rx * Unsafe.Add(ref ry, 3);

            res = new UInt256(r0, r1, r2, r3);
        }

        public void Multiply(in UInt256 a, out UInt256 res) => Multiply(this, a, out res);

        public static bool MultiplyOverflow(in UInt256 x, in UInt256 y, out UInt256 res)
        {
            Span<ulong> p = stackalloc ulong[8];
            Umul(x, y, out res, out UInt256 high);
            return !high.IsZero;
        }

        public int BitLen
        {
            get
            {
                if (u3 != 0)
                {
                    return 192 + Len64(u3);
                }

                if (u2 != 0)
                {
                    return 128 + Len64(u2);
                }

                if (u1 != 0)
                {
                    return 64 + Len64(u1);
                }

                return Len64(u0);
            }
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private void Squared(out UInt256 result)
        {
            var z = this;
            Span<ulong> res = stackalloc ulong[4];
            ulong carry0, carry1, carry2;
            ulong res1, res2;

            (carry0, res[0]) = Multiply64(z.u0, z.u0);
            (carry0, res1) = UmulHopi(carry0, z.u0, z.u1);
            (carry0, res2) = UmulHopi(carry0, z.u0, z.u2);

            (carry1, res[1]) = UmulHopi(res1, z.u0, z.u1);
            (carry1, res2) = UmulStepi(res2, z.u1, z.u1, carry1);

            (carry2, res[2]) = UmulHopi(res2, z.u0, z.u2);

            res[3] = 2 * (z.u0 * z.u3 + z.u1 * z.u2) + carry0 + carry1 + carry2;
            result = new UInt256(res);
        }

        public static void Exp(in UInt256 b, in UInt256 e, out UInt256 result)
        {
            result = One;
            UInt256 bs = b;
            var len = e.BitLen;
            for (var i = 0; i < len; i++)
            {
                if (e.Bit(i))
                {
                    Multiply(result, bs, out result);
                }
                bs.Squared(out bs);
            }
        }

        public void Exp(in UInt256 exp, out UInt256 res) => Exp(this, exp, out res);

        public static void ExpMod(in UInt256 b, in UInt256 e, in UInt256 m, out UInt256 result)
        {
            if (m.IsOne)
            {
                result = Zero;
                return;
            }
            result = One;
            UInt256 bs = b;
            var len = e.BitLen;
            for (var i = 0; i < len; i++)
            {
                if (e.Bit(i))
                {
                    MultiplyMod(result, bs, m, out result);
                }
                MultiplyMod(bs, bs, m, out bs);
            }
        }

        public void ExpMod(in UInt256 exp, in UInt256 m, out UInt256 res) => ExpMod(this, exp, m, out res);

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private void ToSpan(ref Span<ulong> res)
        {
            res[0] = u0;
            res[1] = u1;
            res[2] = u2;
            res[3] = u3;
        }

        // MulMod calculates the modulo-m multiplication of x and y and
        // sets res to its result.
        public static void MultiplyMod(in UInt256 x, in UInt256 y, in UInt256 m, out UInt256 res)
        {
            Umul(x, y, out UInt256 pl, out UInt256 ph);

            // If the multiplication is within 256 bits use Mod().
            if (ph.IsZero)
            {
                Mod(in pl, in m, out res);
                return;
            }

            const int length = 8;
            Span<ulong> p = stackalloc ulong[length];
            var pLow = p.Slice(0, 4);
            pl.ToSpan(ref pLow);
            var pHigh = p.Slice(4, 4);
            ph.ToSpan(ref pHigh);
            Span<ulong> quot = stackalloc ulong[length];
            Udivrem(ref MemoryMarshal.GetReference(quot), ref MemoryMarshal.GetReference(p), length, m, out res);
        }

        public void MultiplyMod(in UInt256 a, in UInt256 m, out UInt256 res) => MultiplyMod(this, a, m, out res);

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static void Umul(in UInt256 x, in UInt256 y, out UInt256 low, out UInt256 high)
        {
            ulong carry, carry4, carry5, carry6;
            ulong res1, res2, res3, res4, res5;
            ulong l0, l1, l2, l3;
            ulong h0, h1, h2, h3;

            (carry, l0) = Multiply64(x.u0, y.u0);
            (carry, res1) = UmulHopi(carry, x.u1, y.u0);
            (carry, res2) = UmulHopi(carry, x.u2, y.u0);
            (carry4, res3) = UmulHopi(carry, x.u3, y.u0);

            (carry, l1) = UmulHopi(res1, x.u0, y.u1);
            (carry, res2) = UmulStepi(res2, x.u1, y.u1, carry);
            (carry, res3) = UmulStepi(res3, x.u2, y.u1, carry);
            (carry5, res4) = UmulStepi(carry4, x.u3, y.u1, carry);

            (carry, l2) = UmulHopi(res2, x.u0, y.u2);
            (carry, res3) = UmulStepi(res3, x.u1, y.u2, carry);
            (carry, res4) = UmulStepi(res4, x.u2, y.u2, carry);
            (carry6, res5) = UmulStepi(carry5, x.u3, y.u2, carry);

            (carry, l3) = UmulHopi(res3, x.u0, y.u3);
            (carry, h0) = UmulStepi(res4, x.u1, y.u3, carry);
            (carry, h1) = UmulStepi(res5, x.u2, y.u3, carry);
            (h3, h2) = UmulStepi(carry6, x.u3, y.u3, carry);
            low = new UInt256(l0, l1, l2, l3);
            high = new UInt256(h0, h1, h2, h3);
        }

        // UmulStep computes (hi * 2^64 + lo) = z + (x * y) + carry.
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static void UmulStep(ulong z, ulong x, ulong y, ulong carry, out ulong high, out ulong low)
        {
            (high, low) = Multiply64(x, y);
            ulong c = 0;
            AddWithCarry(low, carry, ref c, out low);
            AddWithCarry(high, 0, ref c, out high);
            c = 0;
            AddWithCarry(low, z, ref c, out low);
            AddWithCarry(high, 0, ref c, out high);
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static (ulong hi, ulong lo) UmulStepi(ulong z, ulong x, ulong y, ulong carry)
        {
            ulong hi, lo;
            UmulStep(z, x, y, carry, out hi, out lo);
            return (hi, lo);
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static (ulong hi, ulong low) UmulHopi(ulong z, ulong x, ulong y)
        {
            ulong hi, lo;
            UmulHop(z, x, y, out hi, out lo);
            return (hi, lo);
        }

        // UmulHop computes (hi * 2^64 + lo) = z + (x * y)
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static void UmulHop(ulong z, ulong x, ulong y, out ulong high, out ulong low)
        {
            (high, low) = Multiply64(x, y);
            ulong carry = 0ul;
            AddWithCarry(low, z, ref carry, out low);
            AddWithCarry(high, 0, ref carry, out high);
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        internal static (ulong high, ulong low) Multiply64(ulong a, ulong b)
        {
            ulong high = Math.BigMul(a, b, out ulong low);
            return (high, low);
        }

        // Divide sets res to the quotient x/y.
        // If y == 0, z is set to 0
        public static void Divide(in UInt256 x, in UInt256 y, out UInt256 res)
        {
            if (y.IsZero || y > x)
            {
                res = Zero;
                return;
            }

            if (x == y)
            {
                res = One;
                return;
            }

            // Shortcut some cases
            if (x.IsUint64)
            {
                res = (UInt256)(((ulong)x) / (ulong)y);
                return;
            }

            // At this point, we know
            // x/y ; x > y > 0

            res = default; // initialize with zeros
            const int length = 4;
            Udivrem(ref Unsafe.As<UInt256, ulong>(ref res), ref Unsafe.As<UInt256, ulong>(ref Unsafe.AsRef(in x)), length, y, out UInt256 _);
        }

        public void Divide(in UInt256 a, out UInt256 res) => Divide(this, a, out res);

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        internal static (ulong quo, ulong rem) Div64(ulong hi, ulong lo, ulong y)
        {
            const ulong two32 = ((ulong)1) << 32;
            const ulong mask32 = two32 - 1;
            if (y == 0)
            {
                throw new DivideByZeroException("y == 0");
            }

            if (y <= hi)
            {
                throw new OverflowException("y <= hi");
            }

            var s = LeadingZeros(y);
            y <<= s;

            ulong yn1 = y >> 32;
            ulong yn0 = y & mask32;
            ulong un32 = Lsh(hi, s) | Rsh(lo, (64 - s));
            ulong un10 = Lsh(lo, s);
            ulong un1 = un10 >> 32;
            ulong un0 = un10 & mask32;
            ulong q1 = un32 / yn1;
            ulong rhat = un32 - q1 * yn1;

            for (; q1 >= two32 || q1 * yn0 > two32 * rhat + un1;)
            {
                q1--;
                rhat += yn1;
                if (rhat >= two32)
                {
                    break;
                }
            }

            ulong un21 = un32 * two32 + un1 - q1 * y;
            ulong q0 = un21 / yn1;
            rhat = un21 - q0 * yn1;

            for (; q0 >= two32 || q0 * yn0 > two32 * rhat + un0;)
            {
                q0--;
                rhat += yn1;
                if (rhat >= two32)
                {
                    break;
                }
            }

            return (q1 * two32 + q0, Rsh((un21 * two32 + un0 - q0 * y), s));
        }

        public static void Lsh(in UInt256 x, int n, out UInt256 res)
        {
            if ((n % 64) == 0)
            {
                switch (n)
                {
                    case 0:
                        res = x;
                        return;
                    case 64:
                        x.Lsh64(out res);
                        return;
                    case 128:
                        x.Lsh128(out res);
                        return;
                    case 192:
                        x.Lsh192(out res);
                        return;
                    default:
                        res = Zero;
                        return;
                }
            }

            res = Zero;
            ulong z0 = res.u0, z1 = res.u1, z2 = res.u2, z3 = res.u3;
            ulong a = 0, b = 0;
            // Big swaps first
            if (n > 192)
            {
                if (n > 256)
                {
                    res = Zero;
                    return;
                }

                x.Lsh192(out res);
                n -= 192;
                goto sh192;
            }
            else if (n > 128)
            {
                x.Lsh128(out res);
                n -= 128;
                goto sh128;
            }
            else if (n > 64)
            {
                x.Lsh64(out res);
                n -= 64;
                goto sh64;
            }
            else
            {
                res = x;
            }

            // remaining shifts
            a = Rsh(res.u0, 64 - n);
            z0 = Lsh(res.u0, n);

            sh64:
            b = Rsh(res.u1, 64 - n);
            z1 = Lsh(res.u1, n) | a;

            sh128:
            a = Rsh(res.u2, 64 - n);
            z2 = Lsh(res.u2, n) | b;

            sh192:
            z3 = Lsh(res.u3, n) | a;

            res = new UInt256(z0, z1, z2, z3);
        }

        public void LeftShift(int n, out UInt256 res)
        {
            Lsh(this, n, out res);
        }

        public static UInt256 operator <<(UInt256 a, int n)
        {
            a.LeftShift(n, out UInt256 res);
            return res;
        }

        public bool Bit(int n)
        {
            var bucket = (n / 64) % 4;
            var position = n % 64;
            return (this[bucket] & ((ulong)1 << position)) != 0;
        }

        public static void Rsh(in UInt256 x, int n, out UInt256 res)
        {
            // n % 64 == 0
            if ((n & 0x3f) == 0)
            {
                switch (n)
                {
                    case 0:
                        res = x;
                        return;
                    case 64:
                        x.Rsh64(out res);
                        return;
                    case 128:
                        x.Rsh128(out res);
                        return;
                    case 192:
                        x.Rsh192(out res);
                        return;
                    default:
                        res = Zero;
                        return;
                }
            }

            res = Zero;
            ulong z0 = res.u0, z1 = res.u1, z2 = res.u2, z3 = res.u3;
            ulong a = 0, b = 0;
            // Big swaps first
            if (n > 192)
            {
                if (n > 256)
                {
                    res = Zero;
                    return;
                }

                x.Rsh192(out res);
                z0 = res.u0;
                z1 = res.u1;
                z2 = res.u2;
                z3 = res.u3;
                n -= 192;
                goto sh192;
            }
            else if (n > 128)
            {
                x.Rsh128(out res);
                z0 = res.u0;
                z1 = res.u1;
                z2 = res.u2;
                z3 = res.u3;
                n -= 128;
                goto sh128;
            }
            else if (n > 64)
            {
                x.Rsh64(out res);
                z0 = res.u0;
                z1 = res.u1;
                z2 = res.u2;
                z3 = res.u3;
                n -= 64;
                goto sh64;
            }
            else
            {
                res = x;
                z0 = res.u0;
                z1 = res.u1;
                z2 = res.u2;
                z3 = res.u3;
            }

            // remaining shifts
            a = Lsh(res.u3, 64 - n);
            z3 = Rsh(res.u3, n);

            sh64:
            b = Lsh(res.u2, 64 - n);
            z2 = Rsh(res.u2, n) | a;

            sh128:
            a = Lsh(res.u1, 64 - n);
            z1 = Rsh(res.u1, n) | b;

            sh192:
            z0 = Rsh(res.u0, n) | a;

            res = new UInt256(z0, z1, z2, z3);
        }

        public void RightShift(int n, out UInt256 res) => Rsh(this, n, out res);

        public static UInt256 operator >>(UInt256 a, int n)
        {
            a.RightShift(n, out UInt256 res);
            return res;
        }

        internal void Lsh64(out UInt256 res)
        {
            res = new UInt256(0, this.u0, this.u1, this.u2);
        }

        internal void Lsh128(out UInt256 res)
        {
            res = new UInt256(0, 0, this.u0, this.u1);
        }

        internal void Lsh192(out UInt256 res)
        {
            res = new UInt256(0, 0, 0, this.u0);
        }

        internal void Rsh64(out UInt256 res)
        {
            res = new UInt256(this.u1, this.u2, this.u3, 0);
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private void Rsh128(out UInt256 res)
        {
            res = new UInt256(this.u2, this.u3, 0, 0);
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private void Rsh192(out UInt256 res)
        {
            res = new UInt256(this.u3, 0, 0, 0);
        }

        public static void Not(in UInt256 a, out UInt256 res)
        {
            ulong u0 = ~a.u0;
            ulong u1 = ~a.u1;
            ulong u2 = ~a.u2;
            ulong u3 = ~a.u3;
            res = new UInt256(u0, u1, u2, u3);
        }

        public static void Or(in UInt256 a, in UInt256 b, out UInt256 res)
        {
            res = new UInt256(a.u0 | b.u0, a.u1 | b.u1, a.u2 | b.u2, a.u3 | b.u3);
        }

        public static UInt256 operator |(in UInt256 a, in UInt256 b)
        {
            Or(a, b, out UInt256 res);
            return res;
        }

        public static void And(in UInt256 a, in UInt256 b, out UInt256 res)
        {
            res = new UInt256(a.u0 & b.u0, a.u1 & b.u1, a.u2 & b.u2, a.u3 & b.u3);
        }

        public static UInt256 operator &(in UInt256 a, in UInt256 b)
        {
            And(a, b, out UInt256 res);
            return res;
        }

        public static void Xor(in UInt256 a, in UInt256 b, out UInt256 res)
        {
            res = new UInt256(a.u0 ^ b.u0, a.u1 ^ b.u1, a.u2 ^ b.u2, a.u3 ^ b.u3);
        }

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
            Add(in a, in b, out UInt256 res);
            return res;
        }

        public static UInt256 operator ++(UInt256 a)
        {
            Add(in a, 1, out UInt256 res);
            return res;
        }

        public static UInt256 operator -(in UInt256 a, in UInt256 b)
        {
            if (SubtractUnderflow(in a, in b, out UInt256 c))
            {
                throw new ArithmeticException($"Underflow in subtraction {a} - {b}");
            }

            return c;
        }

        public static bool operator ==(in UInt256 a, in UInt256 b) => a.Equals(b);

        public static bool operator !=(in UInt256 a, in UInt256 b) => !(a == b);

        public static implicit operator UInt256(ulong value) => new UInt256(value, 0ul, 0ul, 0ul);

        public static explicit operator UInt256(BigInteger value)
        {
            byte[] bytes32 = value.ToBytes32(true);
            return new UInt256(bytes32, true);
        }

        public static explicit operator BigInteger(UInt256 value)
        {
            Span<byte> bytes = stackalloc byte[32];
            BinaryPrimitives.WriteUInt64LittleEndian(bytes.Slice(0, 8), value.u0);
            BinaryPrimitives.WriteUInt64LittleEndian(bytes.Slice(8, 8), value.u1);
            BinaryPrimitives.WriteUInt64LittleEndian(bytes.Slice(16, 8), value.u2);
            BinaryPrimitives.WriteUInt64LittleEndian(bytes.Slice(24, 8), value.u3);
            return new BigInteger(bytes, true);
        }

        public static explicit operator sbyte(UInt256 a)
        {
            if (a.u1 > 0 || a.u2 > 0 || a.u3 > 0 || a.u0 > (long)sbyte.MaxValue)
            {
                throw new OverflowException("Cannot convert UInt256 value to sbyte.");
            }
            return (sbyte)a.u0;
        }

        public static explicit operator byte(UInt256 a)
        {
            if (a.u1 > 0 || a.u2 > 0 || a.u3 > 0 || a.u0 > byte.MaxValue)
            {
                throw new OverflowException("Cannot convert UInt256 value to byte.");
            }

            return (byte)a.u0;
        }

        public static explicit operator short(UInt256 a)
        {
            if (a.u1 > 0 || a.u2 > 0 || a.u3 > 0 || a.u0 > (long)short.MaxValue)
            {
                throw new OverflowException("Cannot convert UInt256 value to short.");
            }

            return (short)a.u0;
        }

        public static explicit operator ushort(UInt256 a)
        {
            if (a.u1 > 0 || a.u2 > 0 || a.u3 > 0 || a.u0 > ushort.MaxValue)
            {
                throw new OverflowException("Cannot convert UInt256 value to ushort.");
            }

            return (ushort)a.u0;
        }

        public static explicit operator int(UInt256 a)
        {
            if (a.u1 > 0 || a.u2 > 0 || a.u3 > 0 || a.u0 > int.MaxValue)
            {
                throw new OverflowException("Cannot convert UInt256 value to int.");
            }

            return (int)a.u0;
        }

        public static explicit operator uint(UInt256 a)
        {
            if (a.u1 > 0 || a.u2 > 0 || a.u3 > 0 || a.u0 > uint.MaxValue)
            {
                throw new OverflowException("Cannot convert UInt256 value to uint.");
            }

            return (uint)a.u0;
        }

        public static explicit operator long(UInt256 a)
        {
            if (a.u1 > 0 || a.u2 > 0 || a.u3 > 0 || a.u0 > long.MaxValue)
            {
                throw new OverflowException("Cannot convert UInt256 value to long.");
            }

            return (long)a.u0;
        }

        public static explicit operator ulong(UInt256 a)
        {
            if (a.u1 > 0 || a.u2 > 0 || a.u3 > 0)
            {
                throw new OverflowException("Cannot convert UInt256 value to ulong.");
            }

            return a.u0;
        }

        public static UInt256 operator *(UInt256 a, uint b)
        {
            UInt256 ub = b;
            Multiply(in a, in ub, out UInt256 c);
            return c;
        }

        public static UInt256 operator *(uint a, UInt256 b)
        {
            UInt256 ua = a;
            Multiply(in ua, in b, out UInt256 c);
            return c;
        }

        public static UInt256 operator *(UInt256 a, ulong b)
        {
            UInt256 ub = b;
            Multiply(in a, in ub, out UInt256 c);
            return c;
        }

        public static UInt256 operator *(ulong a, UInt256 b)
        {
            UInt256 ua = a;
            Multiply(in ua, in b, out UInt256 c);
            return c;
        }

        public static UInt256 operator *(UInt256 a, UInt256 b)
        {
            Multiply(in a, in b, out UInt256 c);
            return c;
        }

        public static UInt256 operator /(UInt256 a, uint b)
        {
            UInt256 ub = b;
            Divide(in a, in ub, out UInt256 c);
            return c;
        }

        public static UInt256 operator /(UInt256 a, UInt256 b)
        {
            Divide(in a, in b, out UInt256 c);
            return c;
        }

        public static bool operator <(in UInt256 a, in UInt256 b)
        {
            return LessThan(in a, in b);
        }

        public static bool operator <(in UInt256 a, int b)
        {
            return LessThan(in a, b);
        }

        public static bool operator <(int a, in UInt256 b)
        {
            return LessThan(a, in b);
        }

        public static bool operator <(in UInt256 a, uint b)
        {
            return LessThan(in a, b);
        }

        public static bool operator <(uint a, in UInt256 b)
        {
            return LessThan(a, in b);
        }

        public static bool operator <(in UInt256 a, long b)
        {
            return LessThan(in a, b);
        }

        public static bool operator <(long a, in UInt256 b)
        {
            return LessThan(a, in b);
        }

        public static bool operator <(in UInt256 a, ulong b)
        {
            return LessThan(in a, b);
        }

        public static bool operator <(ulong a, in UInt256 b)
        {
            return LessThan(a, in b);
        }

        public static bool operator <=(in UInt256 a, in UInt256 b)
        {
            return !LessThan(in b, in a);
        }

        public static bool operator <=(in UInt256 a, int b)
        {
            return !LessThan(b, in a);
        }

        public static bool operator <=(int a, in UInt256 b)
        {
            return !LessThan(in b, a);
        }

        public static bool operator <=(in UInt256 a, uint b)
        {
            return !LessThan(b, in a);
        }

        public static bool operator <=(uint a, in UInt256 b)
        {
            return !LessThan(in b, a);
        }

        public static bool operator <=(in UInt256 a, long b)
        {
            return !LessThan(b, in a);
        }

        public static bool operator <=(long a, in UInt256 b)
        {
            return !LessThan(in b, a);
        }

        public static bool operator <=(in UInt256 a, ulong b)
        {
            return !LessThan(b, in a);
        }

        public static bool operator <=(ulong a, UInt256 b)
        {
            return !LessThan(in b, a);
        }

        public static bool operator >(in UInt256 a, in UInt256 b)
        {
            return LessThan(in b, in a);
        }

        public static bool operator >(in UInt256 a, int b)
        {
            return LessThan(b, in a);
        }

        public static bool operator >(int a, in UInt256 b)
        {
            return LessThan(in b, a);
        }

        public static bool operator >(in UInt256 a, uint b)
        {
            return LessThan(b, in a);
        }

        public static bool operator >(uint a, in UInt256 b)
        {
            return LessThan(in b, a);
        }

        public static bool operator >(in UInt256 a, long b)
        {
            return LessThan(b, in a);
        }

        public static bool operator >(long a, in UInt256 b)
        {
            return LessThan(in b, a);
        }

        public static bool operator >(in UInt256 a, ulong b)
        {
            return LessThan(b, in a);
        }

        public static bool operator >(ulong a, in UInt256 b)
        {
            return LessThan(in b, a);
        }

        public static bool operator >=(in UInt256 a, in UInt256 b)
        {
            return !LessThan(in a, in b);
        }

        public static bool operator >=(in UInt256 a, int b)
        {
            return !LessThan(in a, b);
        }

        public static bool operator >=(int a, in UInt256 b)
        {
            return !LessThan(a, in b);
        }

        public static bool operator >=(in UInt256 a, uint b)
        {
            return !LessThan(in a, b);
        }

        public static bool operator >=(uint a, in UInt256 b)
        {
            return !LessThan(a, in b);
        }

        public static bool operator >=(in UInt256 a, long b)
        {
            return !LessThan(in a, b);
        }

        public static bool operator >=(long a, in UInt256 b)
        {
            return !LessThan(a, in b);
        }

        public static bool operator >=(in UInt256 a, ulong b)
        {
            return !LessThan(in a, b);
        }

        public static bool operator >=(ulong a, in UInt256 b)
        {
            return !LessThan(a, in b);
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static bool LessThan(in UInt256 a, long b)
        {
            return b >= 0 && a.u3 == 0 && a.u2 == 0 && a.u1 == 0 && a.u0 < (ulong)b;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static bool LessThan(long a, in UInt256 b)
        {
            return a < 0 || b.u1 != 0 || b.u2 != 0 || b.u3 != 0 || (ulong)a < b.u0;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static bool LessThan(in UInt256 a, ulong b)
        {
            return a.u3 == 0 && a.u2 == 0 && a.u1 == 0 && a.u0 < b;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static bool LessThan(ulong a, in UInt256 b)
        {
            return b.u3 != 0 || b.u2 != 0 || b.u1 != 0 || a < b.u0;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static bool LessThan(in UInt256 a, in UInt256 b)
        {
            if (a.u3 != b.u3)
                return a.u3 < b.u3;
            if (a.u2 != b.u2)
                return a.u2 < b.u2;
            if (a.u1 != b.u1)
                return a.u1 < b.u1;
            return a.u0 < b.u0;
        }

        public static bool operator ==(in UInt256 a, int b)
        {
            return a.Equals(b);
        }

        public static bool operator ==(int a, in UInt256 b)
        {
            return b.Equals(a);
        }

        public static bool operator ==(in UInt256 a, uint b)
        {
            return a.Equals(b);
        }

        public static bool operator ==(uint a, in UInt256 b)
        {
            return b.Equals(a);
        }

        public static bool operator ==(in UInt256 a, long b)
        {
            return a.Equals(b);
        }

        public static bool operator ==(long a, in UInt256 b)
        {
            return b.Equals(a);
        }

        public static bool operator ==(in UInt256 a, ulong b)
        {
            return a.Equals(b);
        }

        public static bool operator ==(ulong a, in UInt256 b)
        {
            return b.Equals(a);
        }

        public static bool operator !=(in UInt256 a, int b)
        {
            return !a.Equals(b);
        }

        public static bool operator !=(int a, in UInt256 b)
        {
            return !b.Equals(a);
        }

        public static bool operator !=(in UInt256 a, uint b)
        {
            return !a.Equals(b);
        }

        public static bool operator !=(uint a, in UInt256 b)
        {
            return !b.Equals(a);
        }

        public static bool operator !=(in UInt256 a, long b)
        {
            return !a.Equals(b);
        }

        public static bool operator !=(long a, in UInt256 b)
        {
            return !b.Equals(a);
        }

        public static bool operator !=(in UInt256 a, ulong b)
        {
            return !a.Equals(b);
        }

        public static bool operator !=(ulong a, in UInt256 b)
        {
            return !b.Equals(a);
        }

        public static explicit operator UInt256(sbyte a)
        {
            if (a < 0)
            {
                throw new ArgumentException($"Expected a positive number and got {a}", nameof(a));
            }

            return new UInt256((ulong)a);
        }

        public static implicit operator UInt256(byte a)
        {
            return new UInt256(a);
        }

        public static explicit operator UInt256(short a)
        {
            if (a < 0)
            {
                throw new ArgumentException($"Expected a positive number and got {a}", nameof(a));
            }

            return new UInt256((ulong)a);
        }

        public static implicit operator UInt256(ushort a)
        {
            return new UInt256(a);
        }

        public static explicit operator UInt256(int n)
        {
            if (n < 0)
            {
                throw new ArgumentException("n < 0");
            }

            return new UInt256((ulong)n, 0, 0, 0);
        }

        public static implicit operator UInt256(uint a)
        {
            return new UInt256(a);
        }

        public static explicit operator UInt256(long a)
        {
            if (a < 0)
            {
                throw new ArgumentException($"Expected a positive number and got {a}", nameof(a));
            }

            return new UInt256((ulong)a);
        }

        public override string ToString() => ((BigInteger)this).ToString();

        public int CompareTo(object? obj)
        {
            if (!(obj is UInt256))
            {
                throw new InvalidOperationException();
            }

            return CompareTo((UInt256)obj);
        }

        public string ToString(string format)
        {
            return ((BigInteger)this).ToString(format);
        }

        public bool IsUint64 => (this.u1 | this.u2 | this.u3) == 0;

        public bool Equals(UInt256 other)
        {
            return u0 == other.u0 && u1 == other.u1 && u2 == other.u2 && u3 == other.u3;
        }

        public bool Equals(int other)
        {
            return other >= 0 && u0 == (uint)other && u1 == 0 && u2 == 0 && u3 == 0;
        }

        public bool Equals(uint other)
        {
            return u0 == other && u1 == 0 && u2 == 0 && u3 == 0;
        }

        public bool Equals(long other)
        {
            return other >= 0 && u0 == (ulong)other && u1 == 0 && u2 == 0 && u3 == 0;
        }

        public bool Equals(ulong other)
        {
            return u0 == other && u1 == 0 && u2 == 0 && u3 == 0;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private bool Equals(in UInt256 other)
        {
            return u0 == other.u0 &&
                   u1 == other.u1 &&
                   u2 == other.u2 &&
                   u3 == other.u3;
        }

        public int CompareTo(UInt256 b)
        {
            if (this < b)
            {
                return -1;
            }

            if (this.Equals(b))
            {
                return 0;
            }

            return 1;
        }

        public override bool Equals(object? obj)
        {
            return obj is UInt256 other && Equals(other);
        }

        public override int GetHashCode() => HashCode.Combine(u0, u1, u2, u3);

        public ulong this[int index]
        {
            get
            {
                switch (index)
                {
                    case 0:
                        return this.u0;
                    case 1:
                        return this.u1;
                    case 2:
                        return this.u2;
                    case 3:
                        return this.u3;
                }

                throw new IndexOutOfRangeException();
            }
        }

        public static UInt256 Max(UInt256 a, UInt256 b)
        {
            if (LessThan(in b, in a))
                return a;
            return b;
        }

        public static UInt256 Min(UInt256 a, UInt256 b)
        {
            if (LessThan(in b, in a))
                return b;
            return a;
        }

        public const int Len = 4;

        public void Convert(out BigInteger big)
        {
            big = (BigInteger)this;
        }

        public static UInt256 Parse(string value)
        {
            if (!TryParse(value, out UInt256 c))
                throw new FormatException();
            return c;
        }

        public static UInt256 Parse(ReadOnlySpan<char> value, NumberStyles numberStyles)
        {
            if (!TryParse(value, numberStyles, CultureInfo.InvariantCulture, out UInt256 c))
                throw new FormatException();
            return c;
        }

        public static bool TryParse(string value, out UInt256 result)
        {
            return TryParse(value, NumberStyles.Integer, CultureInfo.InvariantCulture, out result);
        }

        public static bool TryParse(ReadOnlySpan<char> value, out UInt256 result)
        {
            return TryParse(value, NumberStyles.Integer, CultureInfo.InvariantCulture, out result);
        }

        public static bool TryParse(string value, NumberStyles style, IFormatProvider provider, out UInt256 result)
        {
            return TryParse(value.AsSpan(), style, provider, out result);
        }

        public static bool TryParse(ReadOnlySpan<char> value, NumberStyles style, IFormatProvider provider, out UInt256 result)
        {
            BigInteger a;
            bool bigParsedProperly;
            if ((style & NumberStyles.HexNumber) == NumberStyles.HexNumber && value[0] != 0)
            {
                Span<char> fixedHexValue = stackalloc char[value.Length + 1];
                fixedHexValue[0] = '0';
                value.CopyTo(fixedHexValue.Slice(1));
                bigParsedProperly = BigInteger.TryParse(fixedHexValue, style, provider, out a);
            }
            else
            {
                Span<char> fixedHexValue = stackalloc char[value.Length];
                value.CopyTo(fixedHexValue);
                bigParsedProperly = BigInteger.TryParse(fixedHexValue, style, provider, out a);
            }

            if (!bigParsedProperly)
            {
                result = Zero;
                return false;
            }


            result = (UInt256)a;
            return true;
        }
    }
}
