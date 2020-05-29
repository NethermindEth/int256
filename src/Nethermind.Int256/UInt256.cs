using System;
using System.Buffers.Binary;
using System.Numerics;
using System.Runtime.CompilerServices;

namespace Nethermind.Int256
{
    public readonly struct UInt256
    {
        /* in little endian order u4 is the most significant ulong */
        private readonly ulong u1;
        private readonly ulong u2;
        private readonly ulong u3;
        private readonly ulong u4;

        private UInt256(ulong u1, ulong u2, ulong u3, ulong u4)
        {
            this.u1 = u1;
            this.u2 = u2;
            this.u3 = u3;
            this.u4 = u4;
        }
        
        public UInt256(ReadOnlySpan<byte> bytes, bool isBigEndian)
        {
            if (isBigEndian)
            {
                u4 = BinaryPrimitives.ReadUInt64BigEndian(bytes.Slice(0, 8));
                u3 = BinaryPrimitives.ReadUInt64BigEndian(bytes.Slice(8, 8));
                u2 = BinaryPrimitives.ReadUInt64BigEndian(bytes.Slice(16, 8));
                u1 = BinaryPrimitives.ReadUInt64BigEndian(bytes.Slice(24, 8));
            }
            else
            {
                u1 = BinaryPrimitives.ReadUInt64LittleEndian(bytes.Slice(0, 8));
                u2 = BinaryPrimitives.ReadUInt64LittleEndian(bytes.Slice(8, 8));
                u3 = BinaryPrimitives.ReadUInt64LittleEndian(bytes.Slice(16, 8));
                u4 = BinaryPrimitives.ReadUInt64LittleEndian(bytes.Slice(24, 8));
            }
        }

        public static void Add(in UInt256 a, in UInt256 b, out UInt256 res, bool checkOverflow = false)
        {
            ulong carry = 0ul;
            AddWithCarry(a.u1, b.u1, ref carry, out ulong res1); 
            AddWithCarry(a.u2, b.u2, ref carry, out ulong res2);
            AddWithCarry(a.u3, b.u3, ref carry, out ulong res3);
            AddWithCarry(a.u4, b.u4, ref carry, out ulong res4);
            res = new UInt256(res1, res2, res3, res4);

            if (checkOverflow && (res.u4 < a.u4 || res.u4 < b.u4))
            {
                throw new OverflowException("UInt256 add operation resulted in an overflow");
            }
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
            SubtractWithCarry(a.u1, b.u1, ref carry, out ulong res1); 
            SubtractWithCarry(a.u2, b.u2, ref carry, out ulong res2);
            SubtractWithCarry(a.u3, b.u3, ref carry, out ulong res3);
            SubtractWithCarry(a.u4, b.u4, ref carry, out ulong res4);
            res = new UInt256(res1, res2, res3, res4);
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

        public static explicit operator UInt256(BigInteger value)
        {
            byte[] bytes32 = value.ToBytes32(true);
            return new UInt256(bytes32, true);
        }
        
        public static explicit operator BigInteger(UInt256 value)
        {
            Span<byte> bytes = stackalloc byte[32];
            BinaryPrimitives.WriteUInt64LittleEndian(bytes.Slice(0, 8), value.u1);
            BinaryPrimitives.WriteUInt64LittleEndian(bytes.Slice(8, 8), value.u2);
            BinaryPrimitives.WriteUInt64LittleEndian(bytes.Slice(16, 8), value.u3);
            BinaryPrimitives.WriteUInt64LittleEndian(bytes.Slice(24, 8), value.u4);
            return new BigInteger(bytes, true);
        }

        public override string ToString()
        {
            return ((BigInteger)this).ToString();
        }
    }
}