using System;
using System.Buffers.Binary;
using System.Diagnostics;
using System.Numerics;
using System.Runtime.CompilerServices;

[assembly:InternalsVisibleTo("Nethermind.Int256.Test")]
namespace Nethermind.Int256
{
    public readonly struct UInt256
    {
        public static readonly UInt256 Zero = (UInt256) 0ul;
        public static readonly UInt256 One = (UInt256) 1ul;
        public static readonly UInt256 MinValue = Zero;
        public static readonly UInt256 MaxValue = ~Zero;

        /* in little endian order so u4 is the most significant ulong */
        private readonly ulong u0;
        private readonly ulong u1;
        private readonly ulong u2;
        private readonly ulong u3;

        private UInt256(ulong u0, ulong u1, ulong u2, ulong u3)
        {
            this.u0 = u0;
            this.u1 = u1;
            this.u2 = u2;
            this.u3 = u3;
        }

        public UInt256(ReadOnlySpan<byte> bytes, bool isBigEndian)
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

        public bool IsZero => this == Zero;
        
        public bool IsOne => this == One;

        public static void Add(in UInt256 a, in UInt256 b, out UInt256 res, bool checkOverflow = false)
        {
            ulong carry = 0ul;
            AddWithCarry(a.u0, b.u0, ref carry, out ulong res1);
            AddWithCarry(a.u1, b.u1, ref carry, out ulong res2);
            AddWithCarry(a.u2, b.u2, ref carry, out ulong res3);
            AddWithCarry(a.u3, b.u3, ref carry, out ulong res4);
            res = new UInt256(res1, res2, res3, res4);

            if (checkOverflow && (res.u3 < a.u3 || res.u3 < b.u3))
            {
                throw new OverflowException("UInt256 add operation resulted in an overflow");
            }
            
#if DEBUG
            Debug.Assert((BigInteger) res == ((BigInteger) a + (BigInteger) b) % ((BigInteger) 1 << 256));
#endif
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static void AddWithCarry(ulong a, ulong b, ref ulong carry, out ulong res)
        {
            // can we use intrinsics
            res = a + b;
            if (res < a)
            {
                res = res + carry;
                carry = 1;
            }
            else
            {
                res = res + carry;
                carry = res == 0 ? carry : 0;
            }
        }

        public static void Subtract(in UInt256 a, in UInt256 b, out UInt256 res)
        {
            ulong carry = 0ul;
            SubtractWithCarry(a.u0, b.u0, ref carry, out ulong res1);
            SubtractWithCarry(a.u1, b.u1, ref carry, out ulong res2);
            SubtractWithCarry(a.u2, b.u2, ref carry, out ulong res3);
            SubtractWithCarry(a.u3, b.u3, ref carry, out ulong res4);
            res = new UInt256(res1, res2, res3, res4);

            Debug.Assert((BigInteger) res == ((BigInteger) a - (BigInteger) b + ((BigInteger) 1 << 256)) % ((BigInteger) 1 << 256));
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static void SubtractWithCarry(ulong a, ulong b, ref ulong carry, out ulong res)
        {
            if (a >= b)
            {
                res = a - b - carry;
                carry = res == ulong.MaxValue ? carry : 0ul;
            }
            else
            {
                res = ulong.MaxValue - (b + carry - a) + 1;
                carry = 1ul;
            }
        }
        
        public static void Multiply(in UInt256 a, in UInt256 b, out UInt256 res)
        {
            throw new NotImplementedException();
        }
        
        internal static void Multiply64(ulong a, ulong b, out ulong high, out ulong low)
        {
            ulong a0 = (uint)a;
            ulong a1 = a >> 32;
            ulong b0 = (uint)b;
            ulong b1 = b >> 32;
            ulong carry = a0 * b0;
            uint r0 = (uint)carry;
            carry = (carry >> 32) + a0 * b1;
            ulong r2 = carry >> 32;
            carry = (uint)carry + a1 * b0;
            high = carry << 32 | r0;
            low = (carry >> 32) + r2 + a1 * b1;
            Debug.Assert((BigInteger)(high << 32) + low == (BigInteger)a * b);
        }
        
        internal static void Multiply64(ulong a, ulong b, ulong c, out ulong high, out ulong low)
        {
            ulong a0 = (uint)a;
            ulong a1 = a >> 32;
            ulong b0 = (uint)b;
            ulong b1 = b >> 32;
            ulong carry = a0 * b0 + (uint)c;
            uint r0 = (uint)carry;
            carry = (carry >> 32) + a0 * b1 + (c >> 32);
            ulong r2 = carry >> 32;
            carry = (uint)carry + a1 * b0;
            high = carry << 32 | r0;
            low = (carry >> 32) + r2 + a1 * b1;
            Debug.Assert((BigInteger)(high << 32) + low == (BigInteger)(a * b + c));
        }

        public static void Not(in UInt256 a, out UInt256 res)
        {
            ulong u0 = ~a.u0;
            ulong u1 = ~a.u1;
            ulong u2 = ~a.u2;
            ulong u3 = ~a.u3;
            res = new UInt256(u0, u1, u2, u3);
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

        public static bool operator ==(in UInt256 a, in UInt256 b)
        {
            return a.Equals(b);
        }

        public static bool operator !=(in UInt256 a, in UInt256 b)
        {
            return !(a == b);
        }

        public static explicit operator UInt256(ulong value)
        {
            return new UInt256(value, 0ul, 0ul, 0ul);
        }

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

        public override string ToString()
        {
            return ((BigInteger) this).ToString();
        }

        private bool Equals(in UInt256 other)
        {
            return u0 == other.u0 &&
                   u1 == other.u1 &&
                   u2 == other.u2 &&
                   u3 == other.u3;
        }
        
        public override bool Equals(object obj)
        {
            return obj is UInt256 other && Equals(other);
        }

        public override int GetHashCode()
        {
            return HashCode.Combine(u0, u1, u2, u3);
        }
    }
}