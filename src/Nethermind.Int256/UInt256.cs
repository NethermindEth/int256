using System;
using System.Buffers.Binary;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Globalization;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.Arm;
using System.Runtime.Intrinsics.X86;

[assembly: InternalsVisibleTo("Nethermind.Int256.Tests")]

namespace Nethermind.Int256
{
    [StructLayout(LayoutKind.Explicit)]
    public readonly struct UInt256 : IEquatable<UInt256>, IComparable, IComparable<UInt256>, IInteger<UInt256>, IConvertible
    {
        // Ensure that hashes are different for every run of the node and every node, so if are any hash collisions on
        // one node they will not be the same on another node or across a restart so hash collision cannot be used to degrade
        // the performance of the network as a whole.
        private static readonly uint s_instanceRandom = (uint)System.Security.Cryptography.RandomNumberGenerator.GetInt32(int.MinValue, int.MaxValue);

        public static readonly UInt256 Zero = 0ul;
        public static readonly UInt256 One = 1ul;
        public static readonly UInt256 MinValue = Zero;
        public static readonly UInt256 MaxValue = ~Zero;
        public static readonly UInt256 UInt128MaxValue = new(ulong.MaxValue, ulong.MaxValue);

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
            if (Vector256.IsHardwareAccelerated)
            {
                Unsafe.SkipInit(out this.u0);
                Unsafe.SkipInit(out this.u1);
                Unsafe.SkipInit(out this.u2);
                Unsafe.SkipInit(out this.u3);
                Unsafe.As<ulong, Vector256<uint>>(ref this.u0) = Vector256.Create(r0, r1, r2, r3, r4, r5, r6, r7);
            }
            else
            {
                u0 = (ulong)r1 << 32 | r0;
                u1 = (ulong)r3 << 32 | r2;
                u2 = (ulong)r5 << 32 | r4;
                u3 = (ulong)r7 << 32 | r6;
            }
        }

        public UInt256(ulong u0 = 0, ulong u1 = 0, ulong u2 = 0, ulong u3 = 0)
        {
            if (Vector256.IsHardwareAccelerated)
            {
                Unsafe.SkipInit(out this.u0);
                Unsafe.SkipInit(out this.u1);
                Unsafe.SkipInit(out this.u2);
                Unsafe.SkipInit(out this.u3);
                Unsafe.As<ulong, Vector256<ulong>>(ref this.u0) = Vector256.Create(u0, u1, u2, u3);
            }
            else
            {
                this.u0 = u0;
                this.u1 = u1;
                this.u2 = u2;
                this.u3 = u3;
            }
        }

        public UInt256(in ReadOnlySpan<byte> bytes, bool isBigEndian = false)
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
                    if (Vector256.IsHardwareAccelerated)
                    {
                        Unsafe.SkipInit(out this.u0);
                        Unsafe.SkipInit(out this.u1);
                        Unsafe.SkipInit(out this.u2);
                        Unsafe.SkipInit(out this.u3);
                        Unsafe.As<ulong, Vector256<byte>>(ref this.u0) = Vector256.Create<byte>(bytes);
                    }
                    else
                    {
                        u0 = BinaryPrimitives.ReadUInt64LittleEndian(bytes.Slice(0, 8));
                        u1 = BinaryPrimitives.ReadUInt64LittleEndian(bytes.Slice(8, 8));
                        u2 = BinaryPrimitives.ReadUInt64LittleEndian(bytes.Slice(16, 8));
                        u3 = BinaryPrimitives.ReadUInt64LittleEndian(bytes.Slice(24, 8));
                    }
                }
            }
            else
            {
                Create(bytes, out u0, out u1, out u2, out u3);
            }
        }

        private static void Create(in ReadOnlySpan<byte> bytes, out ulong u0, out ulong u1, out ulong u2, out ulong u3)
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
                    cs0 <<= 8;
                    if (j <= byteCount)
                    {
                        cs0 |= bytes[byteCount - j];
                    }
                }
            }

            if (dwordCount >= 2)
            {
                for (int j = 16; j > 8; j--)
                {
                    cs1 <<= 8;
                    if (j <= byteCount)
                    {
                        cs1 |= bytes[byteCount - j];
                    }
                }
            }

            if (dwordCount >= 3)
            {
                for (int j = 24; j > 16; j--)
                {
                    cs2 <<= 8;
                    if (j <= byteCount)
                    {
                        cs2 |= bytes[byteCount - j];
                    }
                }
            }

            if (dwordCount >= 4)
            {
                for (int j = 32; j > 24; j--)
                {
                    cs3 <<= 8;
                    if (j <= byteCount)
                    {
                        cs3 |= bytes[byteCount - j];
                    }
                }
            }

            u0 = cs0;
            u1 = cs1;
            u2 = cs2;
            u3 = cs3;
        }

        public UInt256(in ReadOnlySpan<ulong> data, bool isBigEndian = false)
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
                if (Vector256.IsHardwareAccelerated)
                {
                    Unsafe.SkipInit(out this.u0);
                    Unsafe.SkipInit(out this.u1);
                    Unsafe.SkipInit(out this.u2);
                    Unsafe.SkipInit(out this.u3);
                    Unsafe.As<ulong, Vector256<ulong>>(ref this.u0) = Vector256.Create<ulong>(data);
                }
                else
                {
                    u0 = data[0];
                    u1 = data[1];
                    u2 = data[2];
                    u3 = data[3];
                }
            }
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

        public (ulong value, bool overflow) UlongWithOverflow => (u0, (u1 | u2 | u3) != 0);

        public bool IsZero
        {
            get
            {
                if (Vector256.IsHardwareAccelerated)
                {
                    var v = Unsafe.As<ulong, Vector256<ulong>>(ref Unsafe.AsRef(in u0));
                    return v == default;
                }
                else
                {
                    return (u0 | u1 | u2 | u3) == 0;
                }
            }
        }

        public bool IsOne
        {
            get
            {
                if (Vector256.IsHardwareAccelerated)
                {
                    var v = Unsafe.As<ulong, Vector256<ulong>>(ref Unsafe.AsRef(in u0));
                    return v == Vector256.CreateScalar(1UL);
                }
                else
                {
                    return ((u0 ^ 1UL) | u1 | u2 | u3) == 0;
                }
            }
        }

        public bool IsZeroOrOne => ((u0 >> 1) | u1 | u2 | u3) == 0;

        public UInt256 ZeroValue => Zero;

        public UInt256 OneValue => One;

        public UInt256 MaximalValue => MaxValue;

        private static ReadOnlySpan<byte> s_broadcastLookup =>
        [
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,

            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,

            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,

            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,

            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,

            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,

            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,

            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,

            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,

            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,

            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,

            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,

            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,

            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,

            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,

            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ];

        /// <summary>
        /// Sets <paramref name="res" /> to the sum of <paramref name="a" /> and <paramref name="b" />.
        /// </summary>
        /// <param name="a">The first value to add.</param>
        /// <param name="b">The second value to add.</param>
        /// <param name="res">When this method returns, contains the sum of <paramref name="a" /> and <paramref name="b" />.</param>
        /// <remarks>
        /// This method does not report whether the addition overflows the range of <see cref="UInt256"/>.
        /// Use <see cref="AddOverflow(in UInt256, in UInt256, out UInt256)"/> if you need to detect overflow.
        /// </remarks>
        public static void Add(in UInt256 a, in UInt256 b, out UInt256 res)
            => AddOverflow(in a, in b, out res);

        /// <summary>
        /// AddOverflow sets res to the sum a+b, and returns whether overflow occurred
        /// </summary>
        /// <param name="a">The first value to add.</param>
        /// <param name="b">The second value to add.</param>
        /// <param name="res">When this method returns, contains the sum of <paramref name="a" /> and <paramref name="b" />.</param>
        /// <returns><see langword="true"/> if the addition overflows the range of <see cref="UInt256"/>; otherwise, <see langword="false"/>.</returns>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public static bool AddOverflow(in UInt256 a, in UInt256 b, out UInt256 res)
        {
            if (!Avx2.IsSupported && !Vector256.IsHardwareAccelerated)
            {
                return AddScalar(in a, in b, out res);
            }

            return Avx2.IsSupported ?
                AddAvx2(in a, in b, out res) :
                AddVector256(in a, in b, out res);
        }

        private static bool AddScalar(in UInt256 a, in UInt256 b, out UInt256 res)
        {
            ulong a0 = a.u0;
            ulong b0 = b.u0;
            if ((a.u1 | a.u2 | a.u3 | b.u1 | b.u2 | b.u3) == 0)
            {
                // Fast add for numbers less than 2^64 (18,446,744,073,709,551,615)
                ulong u0 = a0 + b0;
                // Assignment to res after in case is used as input for a or b (by ref aliasing)
                res = default;
                Unsafe.AsRef(in res.u0) = u0;
                if (u0 < a0)
                {
                    Unsafe.AsRef(in res.u1) = 1;
                }
                // Never overflows UInt256
                return false;
            }

            ulong c = 0;
            AddWithCarry(a0, b0, ref c, out ulong r0);
            AddWithCarry(a.u1, b.u1, ref c, out ulong r1);
            AddWithCarry(a.u2, b.u2, ref c, out ulong r2);
            AddWithCarry(a.u3, b.u3, ref c, out ulong r3);
            res = new UInt256(r0, r1, r2, r3);
            return c != 0;
        }

        private static bool AddAvx2(in UInt256 a, in UInt256 b, out UInt256 res)
        {
            Vector256<ulong> av = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in a));
            Vector256<ulong> bv = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in b));

            Vector256<ulong> result = Avx2.Add(av, bv);
            Vector256<ulong> vCarry;
            if (Avx512F.VL.IsSupported)
            {
                vCarry = Avx512F.VL.CompareLessThan(result, av);
            }
            else
            {
                // Work around for missing Vector256.CompareLessThan
                Vector256<ulong> carryFromBothHighBits = Avx2.And(av, bv);
                Vector256<ulong> eitherHighBit = Avx2.Or(av, bv);
                Vector256<ulong> highBitNotInResult = Avx2.AndNot(result, eitherHighBit);

                // Set high bits where carry occurs
                vCarry = Avx2.Or(carryFromBothHighBits, highBitNotInResult);
            }
            // Move carry from Vector space to uint
            uint carry = (uint)(Avx512DQ.IsSupported ?
                Avx512DQ.MoveMask(vCarry) :
                Avx.MoveMask(vCarry.AsDouble()));

            // All bits set will cascade another carry when carry is added to it
            Vector256<ulong> vCascade = Avx2.CompareEqual(result, Vector256<ulong>.AllBitsSet);
            // Move cascade from Vector space to uint
            uint cascade = (uint)(Avx512DQ.IsSupported ?
                Avx512DQ.MoveMask(vCascade) :
                Avx.MoveMask(Unsafe.As<Vector256<ulong>, Vector256<double>>(ref vCascade)));

            // Use ints to work out the Vector cross lane cascades
            // Move carry to next bit and add cascade
            carry = cascade + 2 * carry; // lea
            // Remove cascades not affected by carry
            cascade ^= carry;
            // Choice of 16 vectors
            cascade &= 0x0f;

            // Lookup the carries to broadcast to the Vectors
            Vector256<ulong> cascadedCarries = Unsafe.Add(ref Unsafe.As<byte, Vector256<ulong>>(ref MemoryMarshal.GetReference(s_broadcastLookup)), cascade);

            // Mark res as initialized so we can use it as left side of ref assignment
            Unsafe.SkipInit(out res);
            // Add the cascadedCarries to the result
            Unsafe.As<UInt256, Vector256<ulong>>(ref res) = Avx2.Add(result, cascadedCarries);

            return (carry & 0b1_0000) != 0;
        }

        private static bool AddVector256(in UInt256 a, in UInt256 b, out UInt256 res)
        {
            Vector256<ulong> av = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in a));
            Vector256<ulong> bv = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in b));

            Vector256<ulong> result = Vector256.Add(av, bv);
            Vector256<ulong> vCarry = Vector256.LessThan(result, av);

            uint carry = Vector256.ExtractMostSignificantBits(vCarry);

            // All bits set will cascade another carry when carry is added to it
            Vector256<ulong> vCascade = Vector256.Equals(result, Vector256<ulong>.AllBitsSet);
            // Move cascade from Vector space to uint
            uint cascade = Vector256.ExtractMostSignificantBits(vCascade);

            // Use ints to work out the Vector cross lane cascades
            // Move carry to next bit and add cascade
            carry = cascade + 2 * carry; // lea
            // Remove cascades not affected by carry
            cascade ^= carry;
            // Choice of 16 vectors
            cascade &= 0x0f;

            // Lookup the carries to broadcast to the Vectors
            Vector256<ulong> cascadedCarries = Unsafe.Add(ref Unsafe.As<byte, Vector256<ulong>>(ref MemoryMarshal.GetReference(s_broadcastLookup)), cascade);

            // Mark res as initialized so we can use it as left side of ref assignment
            Unsafe.SkipInit(out res);
            // Add the cascadedCarries to the result
            Unsafe.As<UInt256, Vector256<ulong>>(ref res) = Vector256.Add(result, cascadedCarries);

            return (carry & 0b1_0000) != 0;
        }

        public void Add(in UInt256 a, out UInt256 res) => AddOverflow(this, a, out res);

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
            if (m.IsZero || m.IsOne)
            {
                res = default;
                return;
            }

            // 1) Compute 257-bit sum S = x + y as 5 limbs (s0..s3, s4=carry)
            bool overflow = AddOverflow(in x, in y, out UInt256 sum);
            ulong s4 = !overflow ? 0UL : 1UL;

            // 2) If modulus fits in 64 bits, do direct remainder of the 5-limb value.
            if (m.IsUint64)
            {
                ulong r0 = Rem5ByU64(in sum, s4, m.u0);
                res = default;
                Unsafe.AsRef(in res.u0) = r0;
                return;
            }

            // 3) Fast path: if x < m and y < m then S < 2m, so one subtract is enough (carry-aware).
            // (Branchy compare is fine - the fallback is much more expensive anyway.)
            if (LessThanBoth(in x, in y, in m))
            {
                res = ReduceSumAssumingLT2m(in sum, s4, in m);
                return;
            }

            // No overflow - sum is the exact x+y, so normal mod is correct.
            if (!overflow)
            {
                Mod(in sum, in m, out res);
                return;
            }
            // 4) General fallback: reduce the 257-bit sum directly: res = S % m
            res = RemSum257ByMod(in sum, s4, in m);
        }


        // ----------------------------
        // Fast reduction when S < 2m (eg x<m,y<m).
        // Uses carry-aware single subtract.
        // ----------------------------
        private static UInt256 ReduceSumAssumingLT2m(in UInt256 sum, ulong carry, in UInt256 m)
        {
            // diff = sum - m
            ulong borrow = !SubtractUnderflow(in sum, in m, out UInt256 d) ? 0UL : 1UL;

            // Need subtract if (carry==1) || (sum>=m)
            // sum>=m <=> borrow==0
            ulong needSub = carry | (borrow ^ 1UL);
            ulong mask = 0UL - needSub;

            if (mask == 0)
            {
                return sum;
            }
            else if (mask == ulong.MaxValue)
            {
                return d;
            }
            else
            {
                var mask256 = new UInt256(mask, mask, mask, mask);
                return (d & mask256) | (sum & ~mask256);
            }
        }

        // ----------------------------
        // Remainder of 5-limb value by 64-bit modulus (fast, fixes your test).
        // Computes ((a4..a0 base 2^64) % d).
        // ----------------------------
        [MethodImpl(MethodImplOptions.NoInlining)]
        private static ulong Rem5ByU64(in UInt256 a, ulong a4, ulong d)
        {
            // d != 0 assumed by caller
            int s = BitOperations.LeadingZeroCount(d);
            ulong dn = (s != 0) ? (d << s) : d;       // normalised (msb set) if s>0
            ulong recip = Reciprocal2By1(dn);

            // Normalise dividend (we treat it as 6 limbs with top limb 0)
            ulong u0, u1, u2, u3, u4, u5;
            if (s == 0)
            {
                u0 = a.u0;
                u1 = a.u1;
                u2 = a.u2;
                u3 = a.u3;
                u4 = a4;
                u5 = 0;
            }
            else
            {
                int rs = 64 - s;
                u0 = a.u0 << s;
                u1 = (a.u1 << s) | (a.u0 >> rs);
                u2 = (a.u2 << s) | (a.u1 >> rs);
                u3 = (a.u3 << s) | (a.u2 >> rs);
                u4 = (a4 << s) | (a.u3 >> rs);
                u5 = (a4 >> rs); // top limb (a5=0)
            }

            // Horner-like remainder using exact 2-by-1 divisions:
            // r = (((((u5*b + u4)*b + u3)*b + u2)*b + u1)*b + u0) % dn
            ulong r = 0;
            _ = UDivRem2By1(r, recip, dn, u5, out r);
            _ = UDivRem2By1(r, recip, dn, u4, out r);
            _ = UDivRem2By1(r, recip, dn, u3, out r);
            _ = UDivRem2By1(r, recip, dn, u2, out r);
            _ = UDivRem2By1(r, recip, dn, u1, out r);
            _ = UDivRem2By1(r, recip, dn, u0, out r);

            return (s == 0) ? r : (r >> s);
        }

        // ----------------------------
        // General remainder: (257-bit sum) % m, where sum is 5 limbs and m is up to 4 limbs.
        // Uses Knuth D specialised, operating on a 6-limb u (top limb is 0).
        // ----------------------------
        private static UInt256 RemSum257ByMod(in UInt256 a, ulong a4, in UInt256 m)
        {
            // divisor limb count n in 2..4 (caller ensured m doesn't fit in 64 bits)
            int n = (m.u3 != 0) ? 4 : (m.u2 != 0) ? 3 : 2;

            // Normalise divisor
            ulong vHi = (n == 4) ? m.u3 : (n == 3) ? m.u2 : m.u1;
            int sh = BitOperations.LeadingZeroCount(vHi);

            UInt256 v = ShiftLeftSmall(in m, sh);

            ulong vnHi = (n == 4) ? v.u3 : (n == 3) ? v.u2 : v.u1;
            ulong recip = Reciprocal2By1(vnHi);

            // Normalise dividend: u is 6 limbs (a0..a4 plus a5=0), shifted left by sh.
            ulong u0, u1, u2, u3, u4, u5;
            if (sh == 0)
            {
                u0 = a.u0;
                u1 = a.u1;
                u2 = a.u2;
                u3 = a.u3;
                u4 = a4;
                u5 = 0;
            }
            else
            {
                int rs = 64 - sh;
                u0 = a.u0 << sh;
                u1 = (a.u1 << sh) | (a.u0 >> rs);
                u2 = (a.u2 << sh) | (a.u1 >> rs);
                u3 = (a.u3 << sh) | (a.u2 >> rs);
                u4 = (a4 << sh) | (a.u3 >> rs);
                u5 = (a4 >> rs); // a5=0
            }

            // Run Knuth steps for dividendLen=5 (plus leading u5) and divisorLen=n.
            if (n == 2)
            {
                // m = 5-n = 3, j = 3..0
                _ = DivStep2(ref u3, ref u4, ref u5, v.u0, v.u1, recip);
                _ = DivStep2(ref u2, ref u3, ref u4, v.u0, v.u1, recip);
                _ = DivStep2(ref u1, ref u2, ref u3, v.u0, v.u1, recip);
                _ = DivStep2(ref u0, ref u1, ref u2, v.u0, v.u1, recip);

                UInt256 remN = Create(u0, u1, 0, 0);
                return (sh == 0) ? remN : ShiftRightSmall(remN, sh);
            }
            else if (n == 3)
            {
                // m = 2, j = 2..0
                _ = DivStep3(ref u2, ref u3, ref u4, ref u5, v.u0, v.u1, v.u2, recip);
                _ = DivStep3(ref u1, ref u2, ref u3, ref u4, v.u0, v.u1, v.u2, recip);
                _ = DivStep3(ref u0, ref u1, ref u2, ref u3, v.u0, v.u1, v.u2, recip);

                UInt256 remN = Create(u0, u1, u2, 0);
                return (sh == 0) ? remN : ShiftRightSmall(remN, sh);
            }
            else
            {
                // n == 4, m = 1, j = 1..0
                _ = DivStep4(ref u1, ref u2, ref u3, ref u4, ref u5, in v, recip);
                _ = DivStep4(ref u0, ref u1, ref u2, ref u3, ref u4, in v, recip);

                UInt256 remN = Create(u0, u1, u2, u3);
                return (sh == 0) ? remN : ShiftRightSmall(remN, sh);
            }
        }

        public void AddMod(in UInt256 a, in UInt256 m, out UInt256 res) => AddMod(this, a, m, out res);

        public byte[] PaddedBytes(int n)
        {
            byte[] b = new byte[n];

            for (int i = 0; i < 32 && i < n; i++)
            {
                b[n - 1 - i] = (byte)(this[i / 8] >> (8 * (i % 8)));
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
                if (Avx.IsSupported)
                {
                    Unsafe.As<byte, Vector256<ulong>>(ref MemoryMarshal.GetReference(target)) = Unsafe.As<ulong, Vector256<ulong>>(ref Unsafe.AsRef(in u0));
                }
                else
                {
                    BinaryPrimitives.WriteUInt64LittleEndian(target.Slice(0, 8), u0);
                    BinaryPrimitives.WriteUInt64LittleEndian(target.Slice(8, 8), u1);
                    BinaryPrimitives.WriteUInt64LittleEndian(target.Slice(16, 8), u2);
                    BinaryPrimitives.WriteUInt64LittleEndian(target.Slice(24, 8), u3);
                }
            }
            else
            {
                ThrowNotSupportedException();
            }
        }

        // Mod sets res to the modulus x%y for y != 0.
        // If y == 0, z is set to 0 (OBS: differs from the big.Int)
        public static void Mod(in UInt256 x, in UInt256 y, out UInt256 res)
        {
            if (x.IsZero || y.IsZeroOrOne)
            {
                res = default;
                return;
            }

            switch (x.CompareTo(y))
            {
                case -1:
                    res = x;
                    return;
                case 0:
                    res = default;
                    return;
            }
            // At this point:
            // x != 0
            // y != 0
            // x > y

            if (x.IsUint64)
            {
                // If y > x it has already be handled by caller
                ulong quot = x.u0 / y.u0;
                ulong rem = x.u0 - (quot * y.u0);
                res = Create(rem, 0, 0, 0);
                return;
            }

            DivideImpl(x, y, out _, out res);
        }

        public void Mod(in UInt256 m, out UInt256 res) => Mod(this, m, out res);

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public static int Len64(ulong x) => 64 - BitOperations.LeadingZeroCount(x);

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static int LeadingZeros(ulong x) => BitOperations.LeadingZeroCount(x);

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

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        internal static ulong NativeLsh(ulong a, int n)
        {
            Debug.Assert(n < 64);
            return a << n;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        internal static ulong NativeRsh(ulong a, int n)
        {
            Debug.Assert(n < 64);
            return a >> n;
        }

        // Udivrem divides u by d and produces both quotient and remainder.
        // Throws if d is zero.
        // The quotient is stored in provided quot - len(u)-len(d)+1 words.
        // It loosely follows the Knuth's division algorithm (sometimes referenced as "schoolbook" division) using 64-bit words.
        // See Knuth, Volume 2, section 4.3.1, Algorithm D.
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static void Udivrem(ref ulong quot, ref ulong u, int length, in UInt256 d, out UInt256 rem)
        {
            Unsafe.SkipInit(out int dLen);
            Unsafe.SkipInit(out int shift);

            if (Vector256.IsHardwareAccelerated)
            {
                // Use the fact that u0, u1, u2, u3 can be loaded as a vector
                Vector256<ulong> v = Vector256.LoadUnsafe(in d.u0);

                // Check which ulongs are zero
                var isZero = Vector256.IsZero(v);

                const int ulongCount = 4;
                const uint mask = (1 << ulongCount) - 1;

                // The nth most significant bit is 1 if a nth ulong is 0. Negate and mask with 4 bits to find the most significant set.
                var nonZeroUlongBits = ~isZero.ExtractMostSignificantBits() & mask;
                dLen = 32 - BitOperations.LeadingZeroCount(nonZeroUlongBits);
                shift = LeadingZeros(Unsafe.Add(ref Unsafe.AsRef(in d.u0), dLen - 1));
            }
            else
            {
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
            }

            if (dLen == 0)
            {
                ThrowDivideByZeroException();
            }

            int uLen = 0;
            for (int i = length - 1; i >= 0; i--)
            {
                if (Unsafe.Add(ref u, i) != 0)
                {
                    uLen = i + 1;
                    break;
                }
            }

            Span<ulong> un = stackalloc ulong[uLen + 1];
            un[uLen] = Rsh(Unsafe.Add(ref u, uLen - 1), 64 - shift);
            for (int i = uLen - 1; i > 0; i--)
            {
                un[i] = NativeLsh(Unsafe.Add(ref u, i), shift) | Rsh(Unsafe.Add(ref u, i - 1), 64 - shift);
            }

            un[0] = NativeLsh(u, shift);

            // TODO: Skip the highest word of numerator if not significant.

            if (dLen == 1)
            {
                ulong dnn0 = NativeLsh(d.u0, shift);
                ulong r = UdivremBy1(ref quot, un, dnn0);
                r = NativeRsh(r, shift);
                rem = (UInt256)r;
                return;
            }

            ulong dn0 = NativeLsh(d.u0, shift);
            ulong dn1 = 0;
            ulong dn2 = 0;
            ulong dn3 = 0;
            switch (dLen)
            {
                case 4:
                    dn3 = NativeLsh(d.u3, shift) | Rsh(d.u2, 64 - shift);
                    goto case 3;
                case 3:
                    dn2 = NativeLsh(d.u2, shift) | Rsh(d.u1, 64 - shift);
                    goto case 2;
                case 2:
                    dn1 = NativeLsh(d.u1, shift) | Rsh(d.u0, 64 - shift);
                    break;
            }
            Span<ulong> dnS = stackalloc ulong[4] { dn0, dn1, dn2, dn3 };
            dnS = dnS.Slice(0, dLen);

            UdivremKnuth(ref quot, un, dnS);

            ulong rem0 = 0, rem1 = 0, rem2 = 0, rem3 = 0;
            switch (dLen)
            {
                case 1:
                    rem0 = NativeRsh(un[dLen - 1], shift);
                    goto r0;
                case 2:
                    rem1 = NativeRsh(un[dLen - 1], shift);
                    goto r1;
                case 3:
                    rem2 = NativeRsh(un[dLen - 1], shift);
                    goto r2;
                case 4:
                    rem3 = NativeRsh(un[dLen - 1], shift);
                    goto r3;
            }

        r3:
            rem2 = NativeRsh(un[2], shift) | Lsh(un[3], 64 - shift);
        r2:
            rem1 = NativeRsh(un[1], shift) | Lsh(un[2], 64 - shift);
        r1:
            rem0 = NativeRsh(un[0], shift) | Lsh(un[1], 64 - shift);
        r0:

            rem = new UInt256(rem0, rem1, rem2, rem3);
        }

        // UdivremKnuth implements the division of u by normalized multiple word d from the Knuth's division algorithm.
        // The quotient is stored in provided quot - len(u)-len(d) words.
        // Updates u to contain the remainder - len(d) words.
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static void UdivremKnuth(ref ulong quot, Span<ulong> u, in Span<ulong> d)
        {
            var dh = d[^1];
            var dl = d[^2];
            var reciprocal = Reciprocal2By1(dh);

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
                    ulong ph = Multiply64(qhat, dl, out ulong pl);
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
        private static ulong SubMulTo(Span<ulong> x, in Span<ulong> y, ulong multiplier)
        {
            ulong borrow = 0;
            for (int i = 0; i < y.Length; i++)
            {
                ulong borrow1 = 0;
                SubtractWithBorrow(x[i], borrow, ref borrow1, out ulong s);
                ulong ph = Multiply64(y[i], multiplier, out ulong pl);
                ulong borrow2 = 0;
                SubtractWithBorrow(s, pl, ref borrow2, out ulong t);
                x[i] = t;
                borrow = ph + borrow1 + borrow2;
            }

            return borrow;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static ulong AddTo(Span<ulong> x, in Span<ulong> y)
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
            ulong reciprocal = Reciprocal2By1(d);
            ulong rem = u[^1];
            for (int j = u.Length - 2; j >= 0; j--)
            {
                (Unsafe.Add(ref quot, j), rem) = Udivrem2by1(rem, u[j], d, reciprocal);
            }

            return rem;
        }

        [SkipLocalsInit]
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static ulong Reciprocal2By1(ulong d)
        {
            // Precondition: d is normalised (bit 63 set).

            // For normalised d: (d >> 55) is in [256..511], so subtracting 256 yields [0..255].
            // This form stays identical for valid inputs, but is more obviously "byte range" to humans and JITs.
            int idx = (int)((d >> 55) - 256UL);

            ulong v0 = ReciprocalSeedTable[idx];

            ulong d40 = (d >> 24) + 1UL;

            // Keep the original algebra - all ops are modulo 2^64, so reassociation is safe.
            ulong v1 = (v0 << 11) - ((v0 * v0 * d40) >> 40) - 1UL;

            ulong v2 = (v1 << 13) + ((v1 * (0x1000_0000_0000_0000UL - v1 * d40)) >> 47);

            ulong d0 = d & 1UL;
            ulong d63 = (d >> 1) + d0;

            ulong e = ((v2 >> 1) & (0UL - d0)) - (v2 * d63);

            ulong v3 = (MulHigh(v2, e) >> 1) + (v2 << 31);

            // v4 = v3 - high(v3*d + d) - d
            ulong prodHi = Multiply64(v3, d, out ulong prodLo);

            prodHi += (prodLo > ~d) ? 1UL : 0UL;

            return v3 - prodHi - d;
        }

        // Your 256-entry ushort table (512 bytes) from earlier:
        private static ReadOnlySpan<uint> ReciprocalSeedTable =>
        [
            0x07FD, 0x07F5, 0x07ED, 0x07E5, 0x07DD, 0x07D5, 0x07CE, 0x07C6,
            0x07BF, 0x07B7, 0x07B0, 0x07A8, 0x07A1, 0x079A, 0x0792, 0x078B,
            0x0784, 0x077D, 0x0776, 0x076F, 0x0768, 0x0761, 0x075B, 0x0754,
            0x074D, 0x0747, 0x0740, 0x0739, 0x0733, 0x072C, 0x0726, 0x0720,
            0x0719, 0x0713, 0x070D, 0x0707, 0x0700, 0x06FA, 0x06F4, 0x06EE,
            0x06E8, 0x06E2, 0x06DC, 0x06D6, 0x06D1, 0x06CB, 0x06C5, 0x06BF,
            0x06BA, 0x06B4, 0x06AE, 0x06A9, 0x06A3, 0x069E, 0x0698, 0x0693,
            0x068D, 0x0688, 0x0683, 0x067D, 0x0678, 0x0673, 0x066E, 0x0669,
            0x0664, 0x065E, 0x0659, 0x0654, 0x064F, 0x064A, 0x0645, 0x0640,
            0x063C, 0x0637, 0x0632, 0x062D, 0x0628, 0x0624, 0x061F, 0x061A,
            0x0616, 0x0611, 0x060C, 0x0608, 0x0603, 0x05FF, 0x05FA, 0x05F6,
            0x05F1, 0x05ED, 0x05E9, 0x05E4, 0x05E0, 0x05DC, 0x05D7, 0x05D3,
            0x05CF, 0x05CB, 0x05C6, 0x05C2, 0x05BE, 0x05BA, 0x05B6, 0x05B2,
            0x05AE, 0x05AA, 0x05A6, 0x05A2, 0x059E, 0x059A, 0x0596, 0x0592,
            0x058E, 0x058A, 0x0586, 0x0583, 0x057F, 0x057B, 0x0577, 0x0574,
            0x0570, 0x056C, 0x0568, 0x0565, 0x0561, 0x055E, 0x055A, 0x0556,
            0x0553, 0x054F, 0x054C, 0x0548, 0x0545, 0x0541, 0x053E, 0x053A,
            0x0537, 0x0534, 0x0530, 0x052D, 0x052A, 0x0526, 0x0523, 0x0520,
            0x051C, 0x0519, 0x0516, 0x0513, 0x050F, 0x050C, 0x0509, 0x0506,
            0x0503, 0x0500, 0x04FC, 0x04F9, 0x04F6, 0x04F3, 0x04F0, 0x04ED,
            0x04EA, 0x04E7, 0x04E4, 0x04E1, 0x04DE, 0x04DB, 0x04D8, 0x04D5,
            0x04D2, 0x04CF, 0x04CC, 0x04CA, 0x04C7, 0x04C4, 0x04C1, 0x04BE,
            0x04BB, 0x04B9, 0x04B6, 0x04B3, 0x04B0, 0x04AD, 0x04AB, 0x04A8,
            0x04A5, 0x04A3, 0x04A0, 0x049D, 0x049B, 0x0498, 0x0495, 0x0493,
            0x0490, 0x048D, 0x048B, 0x0488, 0x0486, 0x0483, 0x0481, 0x047E,
            0x047C, 0x0479, 0x0477, 0x0474, 0x0472, 0x046F, 0x046D, 0x046A,
            0x0468, 0x0465, 0x0463, 0x0461, 0x045E, 0x045C, 0x0459, 0x0457,
            0x0455, 0x0452, 0x0450, 0x044E, 0x044B, 0x0449, 0x0447, 0x0444,
            0x0442, 0x0440, 0x043E, 0x043B, 0x0439, 0x0437, 0x0435, 0x0432,
            0x0430, 0x042E, 0x042C, 0x042A, 0x0428, 0x0425, 0x0423, 0x0421,
            0x041F, 0x041D, 0x041B, 0x0419, 0x0417, 0x0414, 0x0412, 0x0410,
            0x040E, 0x040C, 0x040A, 0x0408, 0x0406, 0x0404, 0x0402, 0x0400,
        ];

        // Udivrem2by1 divides <uh, ul> / d and produces both quotient and remainder.
        // It uses the provided d's reciprocal.
        // Implementation ported from https://github.com/chfast/intx and is based on
        // "Improved division by invariant integers", Algorithm 4.
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static (ulong quot, ulong rem) Udivrem2by1(ulong uh, ulong ul, ulong d, ulong reciprocal)
        {
            ulong qh = Multiply64(reciprocal, uh, out ulong ql);
            ulong carry = 0;
            AddWithCarry(ql, ul, ref carry, out ql);
            AddWithCarry(qh, uh, ref carry, out qh);
            qh++;

            ulong r = ul - qh * d;

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
            SubtractImpl(in a, in b, out res);
        }

        // Subtract sets res to the difference a-b
        private static bool SubtractImpl(in UInt256 a, in UInt256 b, out UInt256 res)
        {
            if (Avx2.IsSupported)
            {
                Vector256<ulong> av = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in a));
                Vector256<ulong> bv = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in b));

                Vector256<ulong> result = Avx2.Subtract(av, bv);
                Vector256<ulong> vBorrow;
                if (Avx512F.VL.IsSupported)
                {
                    vBorrow = Avx512F.VL.CompareGreaterThan(result, av);
                }
                else
                {
                    // Invert top bits as Avx2.CompareGreaterThan is only available for longs, not unsigned
                    Vector256<ulong> signFlip = Vector256.Create(0x8000_0000_0000_0000UL);
                    Vector256<ulong> resultSigned = Avx2.Xor(result, signFlip);
                    Vector256<ulong> avSigned = Avx2.Xor(av, signFlip);

                    // Which vectors need to borrow from the next
                    vBorrow = Avx2.CompareGreaterThan(resultSigned.AsInt64(), avSigned.AsInt64()).AsUInt64();
                }
                // Move borrow from Vector space to int
                int borrow = Avx.MoveMask(vBorrow.AsDouble());

                // All zeros will cascade another borrow when borrow is subtracted from it
                Vector256<ulong> vCascade = Avx2.CompareEqual(result, Vector256<ulong>.Zero);
                // Move cascade from Vector space to int
                int cascade = Avx.MoveMask(vCascade.AsDouble());

                // Use ints to work out the Vector cross lane cascades
                // Move borrow to next bit and add cascade
                borrow = cascade + 2 * borrow; // lea
                // Remove cascades not effected by borrow
                cascade ^= borrow;
                // Choice of 16 vectors
                cascade &= 0x0f;

                // Lookup the borrows to broadcast to the Vectors
                Vector256<ulong> cascadedBorrows = Unsafe.Add(ref Unsafe.As<byte, Vector256<ulong>>(ref MemoryMarshal.GetReference(s_broadcastLookup)), cascade);

                // Mark res as initialized so we can use it as left said of ref assignment
                Unsafe.SkipInit(out res);
                // Subtract the cascadedBorrows from the result
                Unsafe.As<UInt256, Vector256<ulong>>(ref res) = Avx2.Subtract(result, cascadedBorrows);
                return (borrow & 0b1_0000) != 0;
            }
            else
            {
                ulong borrow = 0ul;
                SubtractWithBorrow(a.u0, b.u0, ref borrow, out ulong res0);
                SubtractWithBorrow(a.u1, b.u1, ref borrow, out ulong res1);
                SubtractWithBorrow(a.u2, b.u2, ref borrow, out ulong res2);
                SubtractWithBorrow(a.u3, b.u3, ref borrow, out ulong res3);
                res = new UInt256(res0, res1, res2, res3);
                return borrow != 0;
            }
            // #if DEBUG
            //             Debug.Assert((BigInteger)res == ((BigInteger)a - (BigInteger)b + ((BigInteger)1 << 256)) % ((BigInteger)1 << 256));
            // #endif
        }

        public void Subtract(in UInt256 b, out UInt256 res) => Subtract(this, b, out res);

        public static void SubtractMod(in UInt256 a, in UInt256 b, in UInt256 m, out UInt256 res)
        {
            if (SubtractUnderflow(a, b, out UInt256 intermediate))
            {
                Subtract(b, a, out intermediate);
                Mod(intermediate, m, out intermediate);
                if (!intermediate.IsZero)
                {
                    Subtract(m, intermediate, out intermediate);
                }
            }
            else
            {
                Mod(intermediate, m, out intermediate);
            }

            res = intermediate;
        }

        public void SubtractMod(in UInt256 a, in UInt256 m, out UInt256 res) => SubtractMod(this, a, m, out res);

        // SubtractUnderflow sets res to the difference a-b and returns true if the operation underflowed
        public static bool SubtractUnderflow(in UInt256 a, in UInt256 b, out UInt256 res)
        {
            return SubtractImpl(a, b, out res);
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static void SubtractWithBorrow(ulong a, ulong b, ref ulong borrow, out ulong res)
        {
            res = a - b - borrow;
            borrow = (((~a) & b) | (~(a ^ b)) & res) >> 63;
        }

        /// <summary>
        /// Multiplies two 256‑bit unsigned integers (<paramref name="x"/> and <paramref name="y"/>) and
        /// writes the 256‑bit product to <paramref name="res"/>.
        /// </summary>
        /// <param name="x">The first 256‑bit unsigned integer.</param>
        /// <param name="y">The second 256‑bit unsigned integer.</param>
        /// <param name="res">When this method returns, contains the 256‑bit product of x and y.</param>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public static void Multiply(in UInt256 x, in UInt256 y, out UInt256 res)
        {
            if (y.IsZero || x.IsZero)
            {
                res = default;
                return;
            }
            if (y.IsOne || x.IsOne)
            {
                res = x;
                return;
            }

            // If both inputs fit in 64 bits, use a simple multiplication routine.
            if (x.IsUint64 && y.IsUint64)
            {
                // Fast multiply for numbers less than 2^64 (18,446,744,073,709,551,615)
                ulong high = Multiply64(x.u0, y.u0, out ulong low);
                // Assignment to res after multiply in case is used as input for x or y (by ref aliasing)
                res = default;
                Unsafe.AsRef(in res.u0) = low;
                Unsafe.AsRef(in res.u1) = high;
                return;
            }

            if (!Avx512F.IsSupported || !Avx512DQ.IsSupported || !Avx512DQ.VL.IsSupported)
            {
                MultiplyScalar(in x, in y, out res);
            }
            else
            {
                MultiplyAvx512F(in x, in y, out res);
            }
        }

        [SkipLocalsInit]
        private static void MultiplyScalar(in UInt256 x, in UInt256 y, out UInt256 res)
        {
            ref ulong rx = ref Unsafe.As<UInt256, ulong>(ref Unsafe.AsRef(in x));
            ref ulong ry = ref Unsafe.As<UInt256, ulong>(ref Unsafe.AsRef(in y));

            ulong carry = Multiply64(rx, ry, out ulong r0);
            UmulHop(carry, Unsafe.Add(ref rx, 1), ry, out carry, out ulong res1);
            UmulHop(carry, Unsafe.Add(ref rx, 2), ry, out carry, out ulong res2);
            ulong res3 = Unsafe.Add(ref rx, 3) * ry + carry;

            UmulHop(res1, rx, Unsafe.Add(ref ry, 1), out carry, out ulong r1);
            UmulStep(res2, Unsafe.Add(ref rx, 1), Unsafe.Add(ref ry, 1), carry, out carry, out res2);
            res3 = res3 + Unsafe.Add(ref rx, 2) * Unsafe.Add(ref ry, 1) + carry;

            UmulHop(res2, rx, Unsafe.Add(ref ry, 2), out carry, out ulong r2);
            res3 = res3 + Unsafe.Add(ref rx, 1) * Unsafe.Add(ref ry, 2) + carry;

            ulong r3 = res3 + rx * Unsafe.Add(ref ry, 3);

            Unsafe.SkipInit(out res);
            ref ulong pr = ref Unsafe.As<UInt256, ulong>(ref res);
            pr = r0;
            Unsafe.Add(ref pr, 1) = r1;
            Unsafe.Add(ref pr, 2) = r2;
            Unsafe.Add(ref pr, 3) = r3;
        }

        [SkipLocalsInit]
        private static void MultiplyAvx512F(in UInt256 x, in UInt256 y, out UInt256 res)
        {
            Vector256<ulong> vecX = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in x));
            Vector256<ulong> vecY = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in y));

            // Load the inputs and prepare the mask constant.
            Vector512<ulong> mask32 = Vector512.Create(0xFFFFFFFFUL);

            // Indices that reproduce the layout:
            // xRearranged = [ x0, x0, x1, x0,  x1, x2, x0, x1 ]
            // yRearranged = [ y0, y1, y0, y2,  y1, y0, y3, y2 ]
            Vector512<ulong> idxX = Vector512.Create(0UL, 0UL, 1UL, 0UL, 1UL, 2UL, 0UL, 1UL);
            Vector512<ulong> idxY = Vector512.Create(0UL, 1UL, 0UL, 2UL, 1UL, 0UL, 3UL, 2UL);

            // Lane setup - pure shuffle work.
            // Replace 4x Permute4x64 (ymm) + 4x InsertVector256 (zmm) with:
            // 2x InsertVector256 (just put vecX/vecY in low half) + 2x PermuteVar8x64 (zmm).

            Vector512<ulong> z = Vector512<ulong>.Zero;

            // Put vecX/vecY into the low 256 bits only.
            // Upper 256 bits remain zero, which is fine because we only index 0..3.
            Vector512<ulong> xRearranged = Avx512F.InsertVector256(z, vecX, 0);
            Vector512<ulong> yRearranged = Avx512F.InsertVector256(z, vecY, 0);
            xRearranged = Avx512F.PermuteVar8x64(xRearranged, idxX);
            yRearranged = Avx512F.PermuteVar8x64(yRearranged, idxY);

            // "Side multiplies" - independent of the 32x32 widening multiplies.
            // Low-only products we need for limb3 later: p21_lo and p30_lo.
            Vector128<ulong> xHigh = Avx2.ExtractVector128(vecX, 1);  // [x2, x3]

            // yRearranged elements 4..5 are [y1, y0] -> 128-bit lane index 2
            Vector128<ulong> yLow = Avx512F.ExtractVector128(yRearranged, 2); // [y1, y0]

            Vector128<ulong> finalProdLow = Avx512DQ.VL.MultiplyLow(xHigh, yLow); // [p21_lo, p30_lo]

            // 32x32 widening multiplies. This block is the "main event"
            // everything around it should try to overlap with it.
            Vector512<ulong> xUpperParts = Avx512F.ShiftRightLogical(xRearranged, 32);
            Vector512<ulong> yUpperParts = Avx512F.ShiftRightLogical(yRearranged, 32);

            Vector512<ulong> prodLL = Avx512F.Multiply(xRearranged.AsUInt32(), yRearranged.AsUInt32()); // low(x)  * low(y)
            Vector512<ulong> prodHL = Avx512F.Multiply(xUpperParts.AsUInt32(), yRearranged.AsUInt32()); // high(x) * low(y)
            Vector512<ulong> prodHH = Avx512F.Multiply(xUpperParts.AsUInt32(), yUpperParts.AsUInt32()); // high(x) * high(y)
            Vector512<ulong> prodLH = Avx512F.Multiply(xRearranged.AsUInt32(), yUpperParts.AsUInt32()); // low(x)  * high(y)

            // 64x64 reconstruction.
            // Mostly ALU ops (vpaddq/vpsrlq/vpsllq) - lower pressure than shuffles.
            Vector512<ulong> prodLL_hi = Avx512F.ShiftRightLogical(prodLL, 32);
            Vector512<ulong> prodLH_lo = Avx512F.And(prodLH, mask32);
            Vector512<ulong> prodHL_lo = Avx512F.And(prodHL, mask32);
            Vector512<ulong> termT = Avx512F.Add(prodLL_hi, Avx512F.Add(prodLH_lo, prodHL_lo));

            Vector512<ulong> shiftedT = Avx512F.ShiftLeftLogical(termT, 32);

            // lowerPartial uses vpternlog - typically a throughput win over separate and/or.
            Vector512<ulong> lowerPartial = Avx512F.TernaryLogic(prodLL, mask32, shiftedT, 0xEA);

            // higherPartial is add-heavy - so we can use an add-tree
            Vector512<ulong> hiA = Avx512F.Add(prodHH, Avx512F.ShiftRightLogical(prodLH, 32));
            Vector512<ulong> hiB = Avx512F.Add(Avx512F.ShiftRightLogical(prodHL, 32),
                                               Avx512F.ShiftRightLogical(termT, 32));
            Vector512<ulong> higherPartial = Avx512F.Add(hiA, hiB);

            // Interleave lo/hi into [lo,hi] pairs per product.
            // These unpacks are shuffle-port work; JIT likes to keep them early.

            Vector512<ulong> productLow = Avx512F.UnpackLow(lowerPartial, higherPartial);
            Vector512<ulong> productHi = Avx512F.UnpackHigh(lowerPartial, higherPartial);

            // Hoist common "views" of the product vectors now.
            // This is intentionally earlier than point-of-use - it gives OoO a longer window
            // to overlap shuffle latency with the later ALU+compare chain.
            Vector512<ulong> productLow_r2 = Avx512F.AlignRight64(productLow, productLow, 2);
            Vector512<ulong> product1High = Avx512BW.IsSupported ?
                Avx512BW.ShiftRightLogical128BitLane(productHi.AsByte(), 8).AsUInt64() :
                Avx512F.AlignRight64(productHi, productHi, 1);
            Vector512<ulong> productHi_r2 = Avx512F.AlignRight64(productHi, productHi, 2);

            // Also hoist this extract even though its used late - it is independent work.
            Vector128<ulong> extraLow = Avx512F.ExtractVector128(lowerPartial, 3);

            // Carry-emulated 128-bit adds inside each 128-bit chunk.
            // Cost centres here are:
            // - vpcmpltuq + vpmovm2q (mask materialisation tax)
            // - shuffle ops (valignq/vpslldq) feeding the carry path

            Vector512<ulong> crossAndGroup2Sum = Add128(productHi, productLow_r2);
            Vector512<ulong> crossSumHigh = Avx512BW.IsSupported ?
                Avx512BW.ShiftRightLogical128BitLane(crossAndGroup2Sum.AsByte(), 8).AsUInt64() :
                Avx512F.AlignRight64(crossAndGroup2Sum, crossAndGroup2Sum, 1);

            // Perform the group 1 cross-term addition (in 512-bit form, then extract only the final 128-bit lane).
            Vector512<ulong> crossAddMask = Avx512BW.IsSupported ?
                Avx512BW.ShiftLeftLogical128BitLane(crossAndGroup2Sum.AsByte(), 8).AsUInt64() :
                Avx512F.UnpackLow(Vector512<ulong>.Zero, crossAndGroup2Sum);
            Vector512<ulong> updatedProduct0Vec = Avx512F.Add(productLow, crossAddMask);

            // Carry-out for updatedProduct0Vec = productLow + crossAddMask (0/1 per lane, no k-masks).
            Vector512<ulong> carryMaskVec = Avx512F.ShiftRightLogical(
                Avx512F.TernaryLogic(productLow, crossAddMask, updatedProduct0Vec, 0xD4), 63);

            // Move the carry from each 128-bit chunk’s high lane into its low lane (where crossSumHigh lives).
            Vector512<ulong> carryMaskToHigh = Avx512BW.IsSupported ?
                Avx512BW.ShiftRightLogical128BitLane(carryMaskVec.AsByte(), 8).AsUInt64() :
                Avx512F.AlignRight64(carryMaskVec, carryMaskVec, 1);

            Vector512<ulong> limb2Vec = Avx512F.Add(crossSumHigh, carryMaskToHigh);

            // Carry-out for limb2Vec = crossSumHigh + carryMaskToHigh (0/1 per lane, no k-masks).
            Vector512<ulong> limb2CarryMask = Avx512F.ShiftRightLogical(
                Avx512F.TernaryLogic(carryMaskToHigh, crossSumHigh, limb2Vec, 0xD4), 63);

            // limb3 = (product1High > crossSumHigh) ? 1 : 0
            Vector512<ulong> limb3Mask = Avx512F.CompareGreaterThan(product1High, crossSumHigh);
            Vector512<ulong> limb3Vec = Avx512F.ShiftRightLogical(limb3Mask, 63);

            // propagate overflow from (crossSumHigh + carryFlag) into limb3
            limb3Vec = Avx512F.Add(limb3Vec, limb2CarryMask);

            Vector512<ulong> upperIntermediateVec = Avx512F.UnpackLow(limb2Vec, limb3Vec);

            // Combine group 2 partial results (still in 512-bit form).
            // totalGroup2 = group2Sum + product5
            Vector512<ulong> totalGroup2Vec = Add128(crossAndGroup2Sum, productHi_r2);

            // Move totalGroup2 (lane1) down into lane0, then newHalf = upperIntermediate + totalGroup2.
            Vector512<ulong> totalGroup2ToLow = Avx512F.AlignRight64(totalGroup2Vec, totalGroup2Vec, 2);
            Vector512<ulong> newHalfVec = Add128(upperIntermediateVec, totalGroup2ToLow);

            // Extract the two 128-bit results that form the final 256-bit product.
            Vector128<ulong> updatedProduct0 = Avx512F.ExtractVector128(updatedProduct0Vec, 0);
            Vector128<ulong> newHalf = Avx512F.ExtractVector128(newHalfVec, 0);

            // Process group 3 cross-terms.
            finalProdLow = Sse2.Add(finalProdLow, extraLow);
            // swap qwords via pshufd imm=0x4E
            Vector128<ulong> swapped = Sse2.Shuffle(finalProdLow.AsInt32(), 0x4E).AsUInt64();
            // sum both lanes => [a0+a1, a1+a0]
            Vector128<ulong> sum = Sse2.Add(finalProdLow, swapped);
            // keep only the high-qword in the high lane: shift-left by 8 => [0, a0+a1]
            Vector128<ulong> hiOnly = Sse2.ShiftLeftLogical128BitLane(sum.AsByte(), 8).AsUInt64();
            newHalf = Sse2.Add(newHalf, hiOnly);

            // Combine the results into the final 256-bit value.
            Vector256<ulong> finalResult = Vector256.Create(updatedProduct0, newHalf);
            Unsafe.SkipInit(out res);
            Unsafe.As<UInt256, Vector256<ulong>>(ref res) = finalResult;

            /// <summary>
            /// Adds two 512-bit vectors that conceptually contain four independent 128-bit unsigned integers.
            /// Within each 128-bit chunk, propagates an overflow (carry) from the lower 64-bit lane to the higher lane.
            /// </summary>
            /// <param name="left">The first 512-bit vector operand.</param>
            /// <param name="right">The second 512-bit vector operand.</param>
            /// <returns>
            /// The sum of <paramref name="left"/> and <paramref name="right"/>, with carries propagated within each 128-bit chunk.
            /// </returns>
            [MethodImpl(MethodImplOptions.AggressiveInlining)]
            static Vector512<ulong> Add128(Vector512<ulong> left, Vector512<ulong> right)
            {
                // Compute the raw lane-wise sum; carries between 64-bit lanes within a 128-bit chunk
                // are not yet propagated and will be handled by the carry logic below.
                Vector512<ulong> sum = Avx512F.Add(left, right);

                if (Avx512BW.IsSupported)
                {
                    // carryBits = (left & right) | (~sum & (left | right))  (imm8 = 0xD4)
                    Vector512<ulong> carryBits = Avx512F.TernaryLogic(left, right, sum, 0xD4);
                    // carryOut (0 or 1 in each 64-bit lane)
                    Vector512<ulong> carry01 = Avx512F.ShiftRightLogical(carryBits, 63);
                    // Promote carry from lane0->lane1, lane2->lane3, ... within each 128-bit chunk
                    Vector512<ulong> promoted = Avx512BW.ShiftLeftLogical128BitLane(carry01.AsByte(), 8).AsUInt64();
                    // Finalise
                    return Avx512F.Add(sum, promoted);
                }
                else
                {
                    Vector512<ulong> overflowMask = Avx512F.CompareLessThan(sum, left);
                    // Promote carry from each 128-bit chunk’s low lane into its high lane:
                    // lanes: [0, mask0, 0, mask2, 0, mask4, 0, mask6] where mask is 0 or 0xFFFF..FFFF
                    Vector512<ulong> promotedCarryAllOnes = Avx512F.UnpackLow(Vector512<ulong>.Zero, overflowMask);
                    // Subtracting 0xFFFF..FFFF is identical to adding 1 (mod 2^64)
                    return Avx512F.Subtract(sum, promotedCarryAllOnes);
                }
            }
        }

        public void Multiply(in UInt256 a, out UInt256 res) => Multiply(this, a, out res);

        public static bool MultiplyOverflow(in UInt256 x, in UInt256 y, out UInt256 res)
        {
            Umul(x, y, out res, out UInt256 high);
            return !high.IsZero;
        }

        public int BitLen =>
            u3 != 0
                ? 192 + Len64(u3)
                : u2 != 0
                    ? 128 + Len64(u2)
                    : u1 != 0
                        ? 64 + Len64(u1)
                        : Len64(u0);

        [SkipLocalsInit]
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private void Squared(out UInt256 result)
        {
            ulong carry0 = Multiply64(u0, u0, out ulong res0);
            (carry0, ulong temp1) = UmulHopi(carry0, u0, u1);
            (carry0, ulong temp2) = UmulHopi(carry0, u0, u2);

            (ulong carry1, ulong res1) = UmulHopi(temp1, u0, u1);
            (carry1, temp2) = UmulStepi(temp2, u1, u1, carry1);

            (ulong carry2, ulong res2) = UmulHopi(temp2, u0, u2);

            // Don't care about carry here
            ulong res3 = 2 * (u0 * u3 + u1 * u2) + carry0 + carry1 + carry2;

            Unsafe.SkipInit(out result);
            Unsafe.As<ulong, Vector256<ulong>>(ref Unsafe.AsRef(in result.u0)) = Vector256.Create(res0, res1, res2, res3);
        }

        public static void Exp(in UInt256 b, in UInt256 e, out UInt256 result)
        {
            result = One;
            UInt256 bs = b;
            int len = e.BitLen;
            for (int i = 0; i < len; i++)
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
            UInt256 intermediate = One;
            UInt256 bs = b;
            int len = e.BitLen;
            for (int i = 0; i < len; i++)
            {
                if (e.Bit(i))
                {
                    MultiplyMod(intermediate, bs, m, out intermediate);
                }
                MultiplyMod(bs, bs, m, out bs);
            }

            result = intermediate;
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
            Span<ulong> pLow = p.Slice(0, 4);
            pl.ToSpan(ref pLow);
            Span<ulong> pHigh = p.Slice(4, 4);
            ph.ToSpan(ref pHigh);
            Span<ulong> quot = stackalloc ulong[length];
            Udivrem(ref MemoryMarshal.GetReference(quot), ref MemoryMarshal.GetReference(p), length, m, out res);
        }

        public void MultiplyMod(in UInt256 a, in UInt256 m, out UInt256 res) => MultiplyMod(this, a, m, out res);

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static void Umul(in UInt256 x, in UInt256 y, out UInt256 low, out UInt256 high)
        {
            if ((x.u1 | x.u2 | x.u3 | y.u1 | y.u2 | y.u3) == 0)
            {
                // Fast multiply for numbers less than 2^64 (18,446,744,073,709,551,615)
                ulong highUL = Multiply64(x.u0, y.u0, out ulong lowUL);
                // Assignment to high, low after multiply in case either is used as input for x or y (by ref aliasing)
                high = default;
                low = default;
                Unsafe.AsRef(in low.u0) = lowUL;
                Unsafe.AsRef(in low.u1) = highUL;
                return;
            }

            ulong carry = Multiply64(x.u0, y.u0, out ulong l0);
            (carry, ulong res1) = UmulHopi(carry, x.u1, y.u0);
            (carry, ulong res2) = UmulHopi(carry, x.u2, y.u0);
            (ulong carry4, ulong res3) = UmulHopi(carry, x.u3, y.u0);

            (carry, ulong l1) = UmulHopi(res1, x.u0, y.u1);
            (carry, res2) = UmulStepi(res2, x.u1, y.u1, carry);
            (carry, res3) = UmulStepi(res3, x.u2, y.u1, carry);
            (ulong carry5, ulong res4) = UmulStepi(carry4, x.u3, y.u1, carry);

            (carry, ulong l2) = UmulHopi(res2, x.u0, y.u2);
            (carry, res3) = UmulStepi(res3, x.u1, y.u2, carry);
            (carry, res4) = UmulStepi(res4, x.u2, y.u2, carry);
            (ulong carry6, ulong res5) = UmulStepi(carry5, x.u3, y.u2, carry);

            (carry, ulong l3) = UmulHopi(res3, x.u0, y.u3);
            (carry, ulong h0) = UmulStepi(res4, x.u1, y.u3, carry);
            (carry, ulong h1) = UmulStepi(res5, x.u2, y.u3, carry);
            (ulong h3, ulong h2) = UmulStepi(carry6, x.u3, y.u3, carry);
            low = new UInt256(l0, l1, l2, l3);
            high = new UInt256(h0, h1, h2, h3);
        }

        // UmulStep computes (hi * 2^64 + lo) = z + (x * y) + carry.
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static void UmulStep(ulong z, ulong x, ulong y, ulong carry, out ulong high, out ulong low)
        {
            high = Multiply64(x, y, out low);
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
            UmulStep(z, x, y, carry, out ulong hi, out ulong lo);
            return (hi, lo);
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static (ulong hi, ulong low) UmulHopi(ulong z, ulong x, ulong y)
        {
            UmulHop(z, x, y, out ulong hi, out ulong lo);
            return (hi, lo);
        }

        // UmulHop computes (hi * 2^64 + lo) = z + (x * y)
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static void UmulHop(ulong z, ulong x, ulong y, out ulong high, out ulong low)
        {
            high = Multiply64(x, y, out low);
            ulong carry = 0ul;
            AddWithCarry(low, z, ref carry, out low);
            AddWithCarry(high, 0, ref carry, out high);
        }

        // Divide sets res to the quotient x/y.
        // If y == 0, z is set to 0
        public static void Divide(in UInt256 x, in UInt256 y, out UInt256 res)
        {
            if (y.IsZero || y > x)
            {
                res = default;
                return;
            }
            if (y.IsOne)
            {
                res = x;
                return;
            }

            if (x == y)
            {
                res = One;
                return;
            }

            // At this point, we know
            // x/y ; x > y > 0

            if (x.IsUint64)
            {
                ulong quot = x.u0 / y.u0;
                res = Create(quot, 0, 0, 0);
                return;
            }

            DivideImpl(x, y, out res, out _);
        }

        public void Divide(in UInt256 a, out UInt256 res) => Divide(this, a, out res);

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

            ulong z0 = 0, z1 = 0, z2 = 0;
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
            a = NativeRsh(res.u0, 64 - n);
            z0 = NativeLsh(res.u0, n);

        sh64:
            b = NativeRsh(res.u1, 64 - n);
            z1 = NativeLsh(res.u1, n) | a;

        sh128:
            a = NativeRsh(res.u2, 64 - n);
            z2 = NativeLsh(res.u2, n) | b;
            ulong z3;
        sh192:
            z3 = NativeLsh(res.u3, n) | a;

            res = new UInt256(z0, z1, z2, z3);
        }

        public void LeftShift(int n, out UInt256 res)
        {
            Lsh(this, n, out res);
        }

        public static UInt256 operator <<(in UInt256 a, int n)
        {
            a.LeftShift(n, out UInt256 res);
            return res;
        }

        public bool Bit(int n)
        {
            int bucket = (n / 64) % 4;
            int position = n % 64;
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

            ulong a = 0, b = 0;
            ulong z3;
            ulong z2;
            ulong z1;

            ulong z0;
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
            a = NativeLsh(res.u3, 64 - n);
            z3 = NativeRsh(res.u3, n);

        sh64:
            b = NativeLsh(res.u2, 64 - n);
            z2 = NativeRsh(res.u2, n) | a;

        sh128:
            a = NativeLsh(res.u1, 64 - n);
            z1 = NativeRsh(res.u1, n) | b;

        sh192:
            z0 = NativeRsh(res.u0, n) | a;

            res = new UInt256(z0, z1, z2, z3);
        }

        public void RightShift(int n, out UInt256 res) => Rsh(this, n, out res);

        public static UInt256 operator >>(in UInt256 a, int n)
        {
            a.RightShift(n, out UInt256 res);
            return res;
        }

        internal void Lsh64(out UInt256 res)
        {
            res = new UInt256(0, u0, u1, u2);
        }

        internal void Lsh128(out UInt256 res)
        {
            res = new UInt256(0, 0, u0, u1);
        }

        internal void Lsh192(out UInt256 res)
        {
            res = new UInt256(0, 0, 0, u0);
        }

        internal void Rsh64(out UInt256 res)
        {
            res = new UInt256(u1, u2, u3);
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private void Rsh128(out UInt256 res)
        {
            res = new UInt256(u2, u3);
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private void Rsh192(out UInt256 res)
        {
            res = new UInt256(u3);
        }

        public static void Not(in UInt256 a, out UInt256 res)
        {
            if (Vector256.IsHardwareAccelerated)
            {
                var av = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in a));
                // Mark res as initalized so we can use it as left said of ref assignment
                Unsafe.SkipInit(out res);
                Unsafe.As<UInt256, Vector256<ulong>>(ref res) = Vector256.Xor(av, Vector256<ulong>.AllBitsSet);
            }
            else
            {
                ulong u0 = ~a.u0;
                ulong u1 = ~a.u1;
                ulong u2 = ~a.u2;
                ulong u3 = ~a.u3;
                res = new UInt256(u0, u1, u2, u3);
            }
        }

        public static void Or(in UInt256 a, in UInt256 b, out UInt256 res)
        {
            if (Vector256.IsHardwareAccelerated)
            {
                var av = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in a));
                var bv = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in b));
                // Mark res as initalized so we can use it as left said of ref assignment
                Unsafe.SkipInit(out res);
                Unsafe.As<UInt256, Vector256<ulong>>(ref res) = Vector256.BitwiseOr(av, bv);
            }
            else
            {
                res = new UInt256(a.u0 | b.u0, a.u1 | b.u1, a.u2 | b.u2, a.u3 | b.u3);
            }
        }

        public static UInt256 operator |(in UInt256 a, in UInt256 b)
        {
            Or(a, b, out UInt256 res);
            return res;
        }

        public static void And(in UInt256 a, in UInt256 b, out UInt256 res)
        {
            if (Vector256.IsHardwareAccelerated)
            {
                var av = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in a));
                var bv = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in b));
                // Mark res as initalized so we can use it as left said of ref assignment
                Unsafe.SkipInit(out res);
                Unsafe.As<UInt256, Vector256<ulong>>(ref res) = Vector256.BitwiseAnd(av, bv);
            }
            else
            {
                res = new UInt256(a.u0 & b.u0, a.u1 & b.u1, a.u2 & b.u2, a.u3 & b.u3);
            }
        }

        public static UInt256 operator &(in UInt256 a, in UInt256 b)
        {
            And(a, b, out UInt256 res);
            return res;
        }

        public static void Xor(in UInt256 a, in UInt256 b, out UInt256 res)
        {
            if (Vector256.IsHardwareAccelerated)
            {
                var av = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in a));
                var bv = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in b));
                // Mark res as initalized so we can use it as left said of ref assignment
                Unsafe.SkipInit(out res);
                Unsafe.As<UInt256, Vector256<ulong>>(ref res) = Vector256.Xor(av, bv);
            }
            else
            {
                res = new UInt256(a.u0 ^ b.u0, a.u1 ^ b.u1, a.u2 ^ b.u2, a.u3 ^ b.u3);
            }
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

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static bool LessThan(in UInt256 a, long b) => b >= 0 && a.u3 == 0 && a.u2 == 0 && a.u1 == 0 && a.u0 < (ulong)b;

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static bool LessThan(long a, in UInt256 b) => a < 0 || b.u1 != 0 || b.u2 != 0 || b.u3 != 0 || (ulong)a < b.u0;

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static bool LessThan(in UInt256 a, ulong b) => a.u3 == 0 && a.u2 == 0 && a.u1 == 0 && a.u0 < b;

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static bool LessThan(ulong a, in UInt256 b) => b.u3 != 0 || b.u2 != 0 || b.u1 != 0 || a < b.u0;

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static bool LessThan(in UInt256 a, in UInt256 b)
        {
            if (!Avx2.IsSupported && !Vector256.IsHardwareAccelerated)
            {
                return LessThanScalar(in a, in b);
            }

            return Avx2.IsSupported ?
                LessThanAvx2(in a, in b) :
                LessThanVector256(in a, in b);
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static bool LessThanScalar(in UInt256 a, in UInt256 b)
        {
            if (a.u3 != b.u3)
                return a.u3 < b.u3;
            if (a.u2 != b.u2)
                return a.u2 < b.u2;
            if (a.u1 != b.u1)
                return a.u1 < b.u1;
            return a.u0 < b.u0;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static bool LessThanAvx2(in UInt256 a, in UInt256 b)
        {
            // Load the four 64-bit words into a 256-bit register.
            Vector256<ulong> vecL = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in a));
            Vector256<ulong> vecR = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in b));

            uint eqMask;
            uint ltMask;
            if (Avx512F.VL.IsSupported && Avx512DQ.IsSupported)
            {
                // Best case: AVX-512 compare produces k-mask; MoveMask uses KMOVB.
                // Avx512DQ.MoveMask is documented as KMOVB r32,k1.
                eqMask = (uint)Avx512DQ.MoveMask(Avx512F.VL.CompareEqual(vecL, vecR));     // VPCMPUQ + KMOVB
                ltMask = (uint)Avx512DQ.MoveMask(Avx512F.VL.CompareLessThan(vecL, vecR));  // VPCMPUQ + KMOVB
            }
            else
            {
                // Equality mask - AVX2 compare -> movmskpd
                eqMask = (uint)Avx.MoveMask(Avx2.CompareEqual(vecL, vecR).AsDouble());
                // AVX2 unsigned-compare trick (flip sign bit, signed compare)
                var signFlip = Vector256.Create(0x8000_0000_0000_0000UL);
                Vector256<long> sL = Avx2.Xor(vecL, signFlip).AsInt64();
                Vector256<long> sR = Avx2.Xor(vecR, signFlip).AsInt64();
                ltMask = (uint)Avx.MoveMask(Avx2.CompareGreaterThan(sR, sL).AsDouble());
            }

            uint diff = eqMask ^ 0xFu;
            if (diff == 0) return false;

            // Slightly nicer than BitOperations.Log2 here:
            // diff != 0 and diff <= 0xF => LZCNT in [28..31] => (31 - lzcnt) == (31 ^ lzcnt)
            int idx = BitOperations.LeadingZeroCount(diff) ^ 31;
            return ((ltMask >> idx) & 1u) != 0;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static bool LessThanVector256(in UInt256 a, in UInt256 b)
        {
            // Load the four 64-bit words into a 256-bit register.
            Vector256<ulong> vecL = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in a));
            Vector256<ulong> vecR = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in b));

            uint eqMask = Vector256.ExtractMostSignificantBits(Vector256.Equals(vecL, vecR));
            uint ltMask = Vector256.ExtractMostSignificantBits(Vector256.LessThan(vecL, vecR));

            uint diff = eqMask ^ 0xFu;
            if (diff == 0) return false;

            // Slightly nicer than BitOperations.Log2 here:
            // diff != 0 and diff <= 0xF => LZCNT in [28..31] => (31 - lzcnt) == (31 ^ lzcnt)
            int idx = BitOperations.LeadingZeroCount(diff) ^ 31;
            return ((ltMask >> idx) & 1u) != 0;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static bool LessThanBoth(in UInt256 x, in UInt256 y, in UInt256 m)
        {
            if (!Avx2.IsSupported && !Vector256.IsHardwareAccelerated)
            {
                return LessThanScalar(in x, in m) && LessThanScalar(in y, in m);
            }

            return Avx512F.VL.IsSupported && Avx512DQ.IsSupported ?
                LessThanBothAvx512(in x, in y, in m) :
                Avx2.IsSupported ?
                    LessThanBothAvx2(in x, in y, in m) :
                    LessThanBothVector256(in x, in y, in m);
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static bool LessThanBothAvx512(in UInt256 x, in UInt256 y, in UInt256 m)
        {
            Vector256<ulong> vx = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in x));
            Vector256<ulong> vy = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in y));
            Vector256<ulong> vm = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in m));

            Vector512<ulong> vxy = Vector512.Create(vx, vy);
            Vector512<ulong> vmm = Vector512.Create(vm, vm); // can be improved to vbroadcasti64x4 - see below

            uint eq8 = (uint)Avx512DQ.MoveMask(Avx512F.CompareEqual(vxy, vmm)) & 0xFFu;
            uint lt8 = (uint)Avx512DQ.MoveMask(Avx512F.CompareLessThan(vxy, vmm)) & 0xFFu;

            // d has 1s where lanes differ, in both nibbles
            uint d = (eq8 ^ 0xFFu);

            // saturate within each nibble (no cross-nibble bleed)
            d |= (d >> 1) & 0x77u;
            d |= (d >> 2) & 0x33u;

            // isolate the top mismatch bit in each nibble
            uint msb = d & ~((d >> 1) & 0x77u);

            // pick lt at that mismatch bit (still per nibble)
            uint chosen = lt8 & msb;

            // low nibble -> x, high nibble -> y
            return ((chosen & 0x0Fu) != 0) & ((chosen & 0xF0u) != 0);
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static bool LessThanBothAvx2(in UInt256 x, in UInt256 y, in UInt256 m)
        {
            Vector256<ulong> vecM = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in m));

            var signFlip = Vector256.Create(0x8000_0000_0000_0000UL);
            var low32Mask = Vector256.Create(0x0000_0000_FFFF_FFFFUL);

            Vector256<long> sM = Avx2.Xor(vecM, signFlip).AsInt64();

            Vector256<ulong> vecX2 = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in x));
            Vector256<ulong> vecY2 = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in y));

            // All compares first (lets the core overlap work before any movemask/LZCNT).
            Vector256<ulong> eqXv = Avx2.CompareEqual(vecX2, vecM);
            Vector256<ulong> eqYv = Avx2.CompareEqual(vecY2, vecM);

            Vector256<long> sX = Avx2.Xor(vecX2, signFlip).AsInt64();
            Vector256<long> sY = Avx2.Xor(vecY2, signFlip).AsInt64();

            Vector256<ulong> ltXv = Avx2.CompareGreaterThan(sM, sX).AsUInt64();
            Vector256<ulong> ltYv = Avx2.CompareGreaterThan(sM, sY).AsUInt64();

            // Pack eq(low dword) + lt(high dword) so one movmskps yields both.
            Vector256<ulong> packedX = Avx2.Or(Avx2.And(eqXv, low32Mask), Avx2.AndNot(low32Mask, ltXv));
            Vector256<ulong> packedY = Avx2.Or(Avx2.And(eqYv, low32Mask), Avx2.AndNot(low32Mask, ltYv));

            uint maskX = (uint)Avx.MoveMask(packedX.AsSingle());
            uint maskY = (uint)Avx.MoveMask(packedY.AsSingle());

            return LessThanFromPackedMask8(maskX) & LessThanFromPackedMask8(maskY);
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static bool LessThanBothFromEqLt8(uint eq8, uint lt8)
        {
            // eq8/lt8 are 0..255 (low 8 bits used)
            uint d = (eq8 ^ 0xFFu);           // mismatch bits (1 where not equal), per nibble

            // saturate within each nibble (prevent bit4 spilling into bit3 etc)
            d |= (d >> 1) & 0x77u;
            d |= (d >> 2) & 0x33u;

            // isolate most-significant mismatch bit in each nibble
            uint msb = d & ~((d >> 1) & 0x77u);

            // pick lt bit at that msb position for each nibble
            uint chosen = lt8 & msb;

            // low nibble -> x decision, high nibble -> y decision
            return ((chosen & 0x0Fu) != 0) & ((chosen & 0xF0u) != 0);
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static bool LessThanFromPackedMask8(uint mask8)
        {
            // even bits are eq, odd bits are lt
            uint mismatchEven = (~mask8) & 0x55u;
            if (mismatchEven == 0) return false; // all words equal => not less

            int pos = BitOperations.LeadingZeroCount(mismatchEven) ^ 31; // highest mismatching even bit
            return ((mask8 >> (pos + 1)) & 1u) != 0; // corresponding lt bit
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static bool LessThanBothVector256(in UInt256 x, in UInt256 y, in UInt256 m)
        {
            Vector256<ulong> vecM = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in m));

            // x < m
            Vector256<ulong> vecX = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in x));
            uint eqMaskX = Vector256.ExtractMostSignificantBits(Vector256.Equals(vecX, vecM));
            uint ltMaskX = Vector256.ExtractMostSignificantBits(Vector256.LessThan(vecX, vecM));
            if (!LessThanBothFromEqLt8(eqMaskX, ltMaskX))
                return false;

            // y < m
            Vector256<ulong> vecY = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in y));
            uint eqMaskY = Vector256.ExtractMostSignificantBits(Vector256.Equals(vecY, vecM));
            uint ltMaskY = Vector256.ExtractMostSignificantBits(Vector256.LessThan(vecY, vecM));
            return LessThanBothFromEqLt8(eqMaskY, ltMaskY);
        }

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

        public override string ToString() => ((BigInteger)this).ToString();

        public int CompareTo(object? obj) => obj is not UInt256 int256 ? throw new InvalidOperationException() : CompareTo(int256);

        public string ToString(string format)
        {
            return ((BigInteger)this).ToString(format);
        }

        public bool IsUint64 => (u1 | u2 | u3) == 0;

        public bool Equals(int other)
        {
            return other >= 0 && Equals((uint)other);
        }

        public bool Equals(uint other)
        {
            if (Vector256.IsHardwareAccelerated)
            {
                var v = Unsafe.As<ulong, Vector256<uint>>(ref Unsafe.AsRef(in u0));
                return v == Vector256.CreateScalar(other);
            }
            else
            {
                return u0 == other && u1 == 0 && u2 == 0 && u3 == 0;
            }
        }

        public bool Equals(long other) => other >= 0 && Equals((ulong)other);

        public bool Equals(ulong other)
        {
            if (Vector256.IsHardwareAccelerated)
            {
                var v = Unsafe.As<ulong, Vector256<ulong>>(ref Unsafe.AsRef(in u0));
                return v == Vector256.CreateScalar(other);
            }
            else
            {
                return u0 == other && u1 == 0 && u2 == 0 && u3 == 0;
            }
        }

        [OverloadResolutionPriority(1)]
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        public bool Equals(in UInt256 other)
        {
            var v1 = Unsafe.As<ulong, Vector256<ulong>>(ref Unsafe.AsRef(in u0));
            var v2 = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in other));
            return v1 == v2;
        }

        public bool Equals(UInt256 other)
        {
            var v1 = Unsafe.As<ulong, Vector256<ulong>>(ref Unsafe.AsRef(in u0));
            var v2 = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in other));
            return v1 == v2;
        }

        public int CompareTo(UInt256 b) => this < b ? -1 : Equals(b) ? 0 : 1;

        public override bool Equals(object? obj) => obj is UInt256 other && Equals(other);

        [SkipLocalsInit]
        public override int GetHashCode()
        {
            // Very fast hardware accelerated non-cryptographic hash function

            // Start with instance random, length and first ulong as seed
            uint hash = BitOperations.Crc32C(s_instanceRandom, u0);

            // Crc32C is 3 cycle latency, 1 cycle throughput
            // So we use same initial 3 times to not create a dependency chain
            uint hash0 = BitOperations.Crc32C(hash, u1);
            uint hash1 = BitOperations.Crc32C(hash, u2);
            uint hash2 = BitOperations.Crc32C(hash, u3);
            // Combine the 3 hashes; performing the shift on first crc to calculate
            return (int)BitOperations.Crc32C(hash1, ((ulong)hash0 << (sizeof(uint) * 8)) | hash2);
        }

        public ulong this[int index] => index switch
        {
            0 => u0,
            1 => u1,
            2 => u2,
            3 => u3,
            _ => ThrowIndexOutOfRangeException(),
        };


        public static UInt256 Max(in UInt256 a, in UInt256 b) => LessThan(in b, in a) ? a : b;

        public static UInt256 Min(in UInt256 a, in UInt256 b) => LessThan(in b, in a) ? b : a;

        public const int Len = 4;

        public void Convert(out BigInteger big)
        {
            big = (BigInteger)this;
        }

        public static UInt256 Parse(string value) => !TryParse(value, out UInt256 c) ? throw new FormatException() : c;

        public static UInt256 Parse(in ReadOnlySpan<char> value, NumberStyles numberStyles) => !TryParse(value, numberStyles, CultureInfo.InvariantCulture, out UInt256 c) ? throw new FormatException() : c;

        public static bool TryParse(string value, out UInt256 result) => TryParse(value.AsSpan(), out result);

        public static bool TryParse(ReadOnlySpan<char> value, out UInt256 result) => value.StartsWith("0x", StringComparison.OrdinalIgnoreCase)
            ? TryParse(value.Slice(2), NumberStyles.HexNumber, CultureInfo.InvariantCulture, out result)
            : TryParse(value, NumberStyles.Integer, CultureInfo.InvariantCulture, out result);

        public static bool TryParse(string value, NumberStyles style, IFormatProvider provider, out UInt256 result) => TryParse(value.AsSpan(), style, provider, out result);

        public static bool TryParse(in ReadOnlySpan<char> value, NumberStyles style, IFormatProvider provider, out UInt256 result)
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

        public TypeCode GetTypeCode() => TypeCode.Object;
        public bool ToBoolean(IFormatProvider? provider) => !IsZero;
        public byte ToByte(IFormatProvider? provider) => System.Convert.ToByte(ToDecimal(provider), provider);
        public char ToChar(IFormatProvider? provider) => System.Convert.ToChar(ToDecimal(provider), provider);
        public DateTime ToDateTime(IFormatProvider? provider) => System.Convert.ToDateTime(ToDecimal(provider), provider);
        public decimal ToDecimal(IFormatProvider? provider) => (decimal)this;
        public double ToDouble(IFormatProvider? provider) => (double)this;
        public short ToInt16(IFormatProvider? provider) => System.Convert.ToInt16(ToDecimal(provider), provider);
        public int ToInt32(IFormatProvider? provider) => System.Convert.ToInt32(ToDecimal(provider), provider);
        public long ToInt64(IFormatProvider? provider) => System.Convert.ToInt64(ToDecimal(provider), provider);
        public sbyte ToSByte(IFormatProvider? provider) => System.Convert.ToSByte(ToDecimal(provider), provider);
        public float ToSingle(IFormatProvider? provider) => System.Convert.ToSingle(ToDouble(provider), provider);
        public string ToString(IFormatProvider? provider) => ((BigInteger)this).ToString(provider);
        public object ToType(Type conversionType, IFormatProvider? provider) =>
            conversionType == typeof(BigInteger)
                ? (BigInteger)this
                : System.Convert.ChangeType(ToDecimal(provider), conversionType, provider);

        public ushort ToUInt16(IFormatProvider? provider) => System.Convert.ToUInt16(ToDecimal(provider), provider);
        public uint ToUInt32(IFormatProvider? provider) => System.Convert.ToUInt32(ToDecimal(provider), provider);
        public ulong ToUInt64(IFormatProvider? provider) => System.Convert.ToUInt64(ToDecimal(provider), provider);

        [DoesNotReturn]
        private static void ThrowDivideByZeroException() => throw new DivideByZeroException();

        [DoesNotReturn]
        private static void ThrowOverflowException(string message) => throw new OverflowException(message);

        [DoesNotReturn]
        private static void ThrowNotSupportedException() => throw new NotSupportedException();

        [DoesNotReturn]
        private static ulong ThrowIndexOutOfRangeException() => throw new IndexOutOfRangeException();

        // Preconditions (enforced by public Divide wrapper):
        // - y != 0
        // - x > y
        // - x != y
        // - x is not uint64-only
        //
        // This implementation returns quotient only (fastest for Divide()).
        // If you need remainder too, keep the same core but unnormalise the final u-limbs.
        [SkipLocalsInit]
        private static void DivideImpl(in UInt256 x, in UInt256 y, out UInt256 quotient, out UInt256 remainder)
        {
            if (y.u3 != 0)
            {
                DivideBy256Bits(in x, in y, out quotient, out remainder);
            }
            else if (y.u2 != 0)
            {
                DivideBy192Bits(in x, in y, out quotient, out remainder);
            }
            else if (y.u1 != 0)
            {
                //if (Avx512F.IsSupported) DivideBy128BitsAvx512(in x, in y, out quotient, out remainder);
                //else
                if (X86Base.X64.IsSupported)
                {
                    DivideBy128BitsX86Base(in x, in y, out quotient, out remainder);
                }
                else
                {
                    DivideBy128Bits(in x, in y, out quotient, out remainder);
                }
            }
            else
            {
                if (X86Base.X64.IsSupported)
                {
                    DivideBy64BitsX86Base(in x, y.u0, out quotient, out remainder);
                }
                else
                {
                    DivideBy64Bits(in x, y.u0, out quotient, out remainder);
                }
            }
        }

        [SkipLocalsInit]
        [MethodImpl(MethodImplOptions.NoInlining)]
        private static void DivideBy64BitsX86Base(in UInt256 x, ulong divisor, out UInt256 q, out UInt256 remainder)
        {
#pragma warning disable SYSLIB5004 // DivRem is [Experimental] as of net10 docs
            ulong rem = 0;
            ulong q3 = 0;
            ulong u3 = x.u3;
            if (u3 != 0)
            {
                (q3, rem) = X86Base.X64.DivRem(lower: u3, upper: rem, divisor);
            }
            ulong u2 = x.u2;
            ulong q2 = 0;
            if ((u2 | rem) != 0)
            {
                (q2, rem) = X86Base.X64.DivRem(lower: u2, upper: rem, divisor);
            }
            ulong u1 = x.u1;
            ulong q1 = 0;
            if ((u1 | rem) != 0)
            {
                (q1, rem) = X86Base.X64.DivRem(lower: u1, upper: rem, divisor);
            }
            ulong u0 = x.u0;
            ulong q0 = 0;
            if ((u0 | rem) != 0)
            {
                (q0, rem) = X86Base.X64.DivRem(lower: u0, upper: rem, divisor);
            }

            q = Create(q0, q1, q2, q3);
            remainder = Create(rem, 0, 0, 0);
#pragma warning restore SYSLIB5004
        }

        [SkipLocalsInit]
        [MethodImpl(MethodImplOptions.NoInlining)]
        private static void DivideBy64Bits(in UInt256 x, ulong divisor, out UInt256 q, out UInt256 remainder)
        {
            int s = BitOperations.LeadingZeroCount(divisor);
            ulong dn = divisor << s; // normalised divisor (msb set if s>0)
            // Normalise dividend into 5 limbs
            ulong u0n = x.u0;
            ulong u1n = x.u1;
            ulong u2n = x.u2;
            ulong u3n = x.u3;
            ulong rem = 0;
            if (s > 0)
            {
                int rs = 64 - s;
                rem = (u3n >> rs);
                u3n = (u3n << s) | (u2n >> rs);
                u2n = (u2n << s) | (u1n >> rs);
                u1n = (u1n << s) | (u0n >> rs);
                u0n <<= s;
            }

            ulong recip = Reciprocal2By1(dn);
            ulong q3 = ((rem | u3n) == 0) ? 0 : UDivRem2By1(rem, recip, dn, u3n, out rem);
            ulong q2 = ((rem | u2n) == 0) ? 0 : UDivRem2By1(rem, recip, dn, u2n, out rem);
            ulong q1 = ((rem | u1n) == 0) ? 0 : UDivRem2By1(rem, recip, dn, u1n, out rem);
            ulong q0 = ((rem | u0n) == 0) ? 0 : UDivRem2By1(rem, recip, dn, u0n, out rem);
            q = Create(q0, q1, q2, q3);

            // Unnormalise remainder (single limb)
            ulong r0 = rem >> s;
            remainder = Create(r0, 0, 0, 0);
        }

        // Preconditions:
        // - d normalised (msb set)
        // - u1 < d
        [SkipLocalsInit]
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static ulong UDivRem2By1(ulong u1, ulong recip, ulong d, ulong u0, out ulong rem)
        {
            ulong hi = Multiply64(recip, u1, out ulong low);

            low += u0;
            ulong q = hi + u1 + 1UL;
            if (low < u0)
            {
                q++;
            }

            ulong r1 = u0 - (q * d);

            if (r1 > low) { q--; r1 += d; }
            if (r1 >= d) { q++; r1 -= d; }

            rem = r1;
            return q;
        }

        [SkipLocalsInit]
        [MethodImpl(MethodImplOptions.NoInlining)]
        private static void DivideBy192Bits(in UInt256 x, in UInt256 y, out UInt256 q, out UInt256 remainder)
        {
            // ------------------------------------------------------------
            // n >= 2: Knuth D (specialised) with reciprocal qhat
            // ------------------------------------------------------------

            int shift = BitOperations.LeadingZeroCount(y.u2);

            // Normalise divisor v = y << shift
            ulong v0, v1n, v2n;
            if (shift == 0)
            {
                v0 = y.u0; v1n = y.u1; v2n = y.u2;
            }
            else
            {
                int rs = 64 - shift;
                v0 = y.u0 << shift;
                v1n = (y.u1 << shift) | (y.u0 >> rs);
                v2n = (y.u2 << shift) | (y.u1 >> rs);
            }

            // Normalise dividend u = x << shift into 5 limbs
            ulong u0n2, u1d, u2d, u3d, u4d;
            if (shift == 0)
            {
                u0n2 = x.u0; u1d = x.u1; u2d = x.u2; u3d = x.u3; u4d = 0;
            }
            else
            {
                int rs = 64 - shift;
                u0n2 = x.u0 << shift;
                u1d = (x.u1 << shift) | (x.u0 >> rs);
                u2d = (x.u2 << shift) | (x.u1 >> rs);
                u3d = (x.u3 << shift) | (x.u2 >> rs);
                u4d = (x.u3 >> rs);
            }

            ulong vRecip = Reciprocal2By1(v2n);
            ulong q1 = DivStep3(ref u1d, ref u2d, ref u3d, ref u4d, v0, v1n, v2n, vRecip);
            ulong q0 = DivStep3(ref u0n2, ref u1d, ref u2d, ref u3d, v0, v1n, v2n, vRecip);

            q = Create(q0, q1, 0, 0);

            // Remainder is u0..u2
            UInt256 remN = Create(u0n2, u1d, u2d, 0);
            remainder = (shift == 0) ? remN : ShiftRightSmall(remN, shift);
            return;
        }

        [SkipLocalsInit]
        [MethodImpl(MethodImplOptions.NoInlining)]
        private static void DivideBy256Bits(in UInt256 x, in UInt256 y, out UInt256 q, out UInt256 remainder)
        {
            // ------------------------------------------------------------
            // n >= 2: Knuth D (specialised) with reciprocal qhat
            // ------------------------------------------------------------

            int shift = BitOperations.LeadingZeroCount(y.u3);

            // Normalise divisor v = y << shift
            UInt256 u = ShiftLeftSmall(in x, shift);
            UInt256 v = ShiftLeftSmall(in y, shift);
            // Normalise dividend u = x << shift into 5 limbs
            ulong u4d;
            if (shift == 0)
            {
                u4d = 0;
            }
            else
            {
                int rs = 64 - shift;
                u4d = (x.u3 >> rs);
            }

            ulong vRecip = Reciprocal2By1(v.u3);
            ulong q0 = DivStep4(in u, ref u4d, in v, vRecip, out UInt256 rem);

            q = Create(q0, 0, 0, 0);

            // Remainder is u0..u3
            remainder = (shift == 0) ? rem : ShiftRightSmall(rem, shift);
            return;
        }

        // Shift-right by 0..63 (used to unnormalise remainder)
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static UInt256 ShiftLeftSmall(in UInt256 v, int sh)
        {
            if (!Avx2.IsSupported)
            {
                ulong a0 = v.u0;
                ulong a1 = v.u1;
                ulong a2 = v.u2;
                ulong a3 = v.u3;

                int rs = 64 - sh;

                Unsafe.SkipInit(out UInt256 r);
                Unsafe.AsRef(in r.u0) = a0 << sh;
                Unsafe.AsRef(in r.u1) = (a1 << sh) | (a0 >> rs);
                Unsafe.AsRef(in r.u2) = (a2 << sh) | (a1 >> rs);
                Unsafe.AsRef(in r.u3) = (a3 << sh) | (a2 >> rs);

                return r;
            }
            else
            {
                Vector256<ulong> x = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in v));
                Vector128<ulong> cL = Vector128.CreateScalarUnsafe((ulong)(uint)sh);
                Vector128<ulong> cR = Vector128.CreateScalarUnsafe(64uL - (ulong)(uint)sh);

                Vector256<ulong> left = Avx2.ShiftLeftLogical(x, cL);
                Vector256<ulong> y;
                if (Avx512F.VL.IsSupported)
                {
                    Vector256<ulong> prev = Avx512F.VL.AlignRight64(x, default, 3);
                    Vector256<ulong> right = Avx2.ShiftRightLogical(prev, cR);
                    y = Avx2.Or(left, right);
                }
                else
                {
                    Vector256<ulong> right = Avx2.ShiftRightLogical(x, cR);
                    Vector256<ulong> carry = Avx2.Permute4x64(right, 0x90);
                    carry = Avx2.And(carry, Vector256.Create(0UL, ulong.MaxValue, ulong.MaxValue, ulong.MaxValue));
                    y = Avx2.Or(left, carry);
                }

                Unsafe.SkipInit(out UInt256 r);
                Unsafe.As<UInt256, Vector256<ulong>>(ref r) = y;
                return r;
            }
        }

        // Shift-right by 0..63 (used to unnormalise remainder)
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static UInt256 ShiftRightSmall(in UInt256 v, int sh)
        {
            if (!Avx2.IsSupported)
            {
                ulong a0 = v.u0;
                ulong a1 = v.u1;
                ulong a2 = v.u2;
                ulong a3 = v.u3;

                // C# shifts mask the count (64 -> 0), so sh == 64 needs an explicit path.
                if (sh == 64)
                {
                    Unsafe.SkipInit(out UInt256 r);
                    Unsafe.AsRef(in r.u0) = a1;
                    Unsafe.AsRef(in r.u1) = a2;
                    Unsafe.AsRef(in r.u2) = a3;
                    Unsafe.AsRef(in r.u3) = 0;
                    return r;
                }

                int rs = 64 - sh;

                Unsafe.SkipInit(out UInt256 result);
                Unsafe.AsRef(in result.u0) = (a0 >> sh) | (a1 << rs);
                Unsafe.AsRef(in result.u1) = (a1 >> sh) | (a2 << rs);
                Unsafe.AsRef(in result.u2) = (a2 >> sh) | (a3 << rs);
                Unsafe.AsRef(in result.u3) = (a3 >> sh);
                return result;
            }
            else
            {
                Vector256<ulong> x = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in v));

                // right = x >> sh
                Vector128<ulong> cR = Vector128.CreateScalarUnsafe((ulong)sh);
                Vector256<ulong> right = Avx2.ShiftRightLogical(x, cR);

                // carry = (next limb) << (64 - sh)
                Vector128<ulong> cL = Vector128.CreateScalarUnsafe((ulong)(64 - sh));

                Vector256<ulong> y;
                if (Avx512F.VL.IsSupported)
                {
                    // next = [a1, a2, a3, 0]
                    Vector256<ulong> next = Avx512F.VL.AlignRight64(default, x, 1);
                    Vector256<ulong> carry = Avx2.ShiftLeftLogical(next, cL);
                    y = Avx2.Or(right, carry);
                }
                else
                {
                    Vector256<ulong> left = Avx2.ShiftLeftLogical(x, cL);
                    // carry lanes: [a1<<rs, a2<<rs, a3<<rs, a0<<rs] then zero the last lane
                    Vector256<ulong> carry = Avx2.Permute4x64(left, 0x39);
                    carry = Avx2.And(carry, Vector256.Create(ulong.MaxValue, ulong.MaxValue, ulong.MaxValue, 0UL));
                    y = Avx2.Or(right, carry);
                }

                Unsafe.SkipInit(out UInt256 r);
                Unsafe.As<UInt256, Vector256<ulong>>(ref r) = y;
                return r;
            }
        }

        private static void DivideBy128BitsX86Base(in UInt256 x, in UInt256 y, out UInt256 q, out UInt256 remainder)
        {
            // ------------------------------------------------------------
            // n >= 2: Knuth D (specialised) with reciprocal qhat
            // ------------------------------------------------------------
            Debug.Assert(y.u1 != 0 && y.u2 == 0 && y.u3 == 0);

            // -------------------------
            // Normalise divisor (2 limbs)
            // -------------------------
            ulong y0 = y.u0;
            ulong y1 = y.u1;

            int shift = BitOperations.LeadingZeroCount(y1);

            ulong v0, v1n;
            if (shift != 0)
            {
                int rs = 64 - shift;
                v0 = y0 << shift;
                v1n = (y1 << shift) | (y0 >> rs);
            }
            else
            {
                v0 = y0;
                v1n = y1;
            }

            // -------------------------
            // Normalise dividend (5 limbs)
            // -------------------------
            ulong u0 = x.u0;
            ulong u1 = x.u1;
            ulong u2 = x.u2;
            ulong u3 = x.u3;
            ulong u4;

            if (shift != 0)
            {
                int rs = 64 - shift;

                u4 = u3 >> rs;
                u3 = (u3 << shift) | (u2 >> rs);
                u2 = (u2 << shift) | (u1 >> rs);
                u1 = (u1 << shift) | (u0 >> rs);
                u0 <<= shift;
            }
            else
            {
                u4 = 0;
            }

            Unsafe.SkipInit(out q);

            // ------------------------------------------------------------
            // Step j=2: q2 from (u4:u3:u2)
            // ------------------------------------------------------------
            {
                ulong rhat;
                bool rcarry;
                ulong qhat;
                // This special-case is REQUIRED for hardware div safety:
                // if uHi == v1n then the true quotient is >= 2^64, so DIV would #DE.
                if (u4 == v1n)
                {
                    rhat = u3 + v1n;
                    rcarry = rhat < u3;
                    qhat = ulong.MaxValue;
                }
                else
                {
                    rcarry = false;

#pragma warning disable SYSLIB5004 // X86Base.X64.DivRem is marked Experimental/preview
                    (ulong qhat1, ulong r) = X86Base.X64.DivRem(u3, u4, v1n);
#pragma warning restore SYSLIB5004
                    rhat = r;
                    qhat = qhat1;

                    // Reciprocal path
                }

                ulong hi = Multiply64(qhat, v0, out var lo);

                // Correct at most twice.
                if (!rcarry && (hi > rhat || (hi == rhat && lo > u2)))
                {
                    qhat--;
                    ulong lo2 = lo - v0;
                    hi -= (lo < v0) ? 1UL : 0UL;
                    lo = lo2;

                    rhat += v1n;
                    rcarry = rhat < v1n;

                    if (!rcarry && (hi > rhat || (hi == rhat && lo > u2)))
                    {
                        qhat--;
                        lo2 = lo - v0;
                        hi -= (lo < v0) ? 1UL : 0UL;
                        lo = lo2;
                    }
                }

                // Subtract qhat*v from u2,u3,u4 (3 limbs).
                ulong borrow = (u2 < lo) ? 1UL : 0UL;
                u2 -= lo;

                ulong hi1 = Multiply64(qhat, v1n, out lo);
                ulong sum = lo + hi;
                hi = hi1 + ((sum < lo) ? 1UL : 0UL);

                ulong t = u3 - sum;
                ulong b = (u3 < sum) ? 1UL : 0UL;
                u3 = t - borrow;
                borrow = b | ((t < borrow) ? 1UL : 0UL);

                t = u4 - hi;
                b = (u4 < hi) ? 1UL : 0UL;
                u4 = t - borrow;
                borrow = b | ((t < borrow) ? 1UL : 0UL);

                if (borrow != 0)
                {
                    // Add-back v and decrement qhat.
                    ulong s0 = u2 + v0;
                    ulong c = (s0 < u2) ? 1UL : 0UL;

                    ulong s1 = u3 + v1n;
                    ulong c1 = (s1 < u3) ? 1UL : 0UL;
                    s1 += c;
                    c1 |= (s1 < c) ? 1UL : 0UL;

                    u2 = s0;
                    u3 = s1;

                    qhat--;
                }

                Unsafe.AsRef(in q.u2) = qhat;
            }

            // ------------------------------------------------------------
            // Step j=1: q1 from (u3:u2:u1)
            // ------------------------------------------------------------
            {
                ulong rhat;
                bool rcarry;
                ulong qhat;
                // This special-case is REQUIRED for hardware div safety:
                // if uHi == v1n then the true quotient is >= 2^64, so DIV would #DE.
                if (u3 == v1n)
                {
                    rhat = u2 + v1n;
                    rcarry = rhat < u2;
                    qhat = ulong.MaxValue;
                }
                else
                {
                    rcarry = false;

#pragma warning disable SYSLIB5004 // X86Base.X64.DivRem is marked Experimental/preview
                    (ulong qhat1, ulong r) = X86Base.X64.DivRem(u2, u3, v1n);
#pragma warning restore SYSLIB5004
                    rhat = r;
                    qhat = qhat1;

                    // Reciprocal path
                }

                ulong hi = Multiply64(qhat, v0, out var lo);

                if (!rcarry && (hi > rhat || (hi == rhat && lo > u1)))
                {
                    qhat--;
                    ulong lo2 = lo - v0;
                    hi -= (lo < v0) ? 1UL : 0UL;
                    lo = lo2;

                    rhat += v1n;
                    rcarry = rhat < v1n;

                    if (!rcarry && (hi > rhat || (hi == rhat && lo > u1)))
                    {
                        qhat--;
                        lo2 = lo - v0;
                        hi -= (lo < v0) ? 1UL : 0UL;
                        lo = lo2;
                    }
                }

                ulong borrow = (u1 < lo) ? 1UL : 0UL;
                u1 -= lo;

                ulong hi1 = Multiply64(qhat, v1n, out lo);
                ulong sum = lo + hi;
                hi = hi1 + ((sum < lo) ? 1UL : 0UL);

                ulong t = u2 - sum;
                ulong b = (u2 < sum) ? 1UL : 0UL;
                u2 = t - borrow;
                borrow = b | ((t < borrow) ? 1UL : 0UL);

                t = u3 - hi;
                b = (u3 < hi) ? 1UL : 0UL;
                u3 = t - borrow;
                borrow = b | ((t < borrow) ? 1UL : 0UL);

                if (borrow != 0)
                {
                    ulong s0 = u1 + v0;
                    ulong c = (s0 < u1) ? 1UL : 0UL;

                    ulong s1 = u2 + v1n;
                    ulong c1 = (s1 < u2) ? 1UL : 0UL;
                    s1 += c;
                    c1 |= (s1 < c) ? 1UL : 0UL;

                    u1 = s0;
                    u2 = s1;

                    qhat--;
                }

                Unsafe.AsRef(in q.u1) = qhat;
            }

            // ------------------------------------------------------------
            // Step j=0: q0 from (u2:u1:u0)
            // ------------------------------------------------------------
            {
                ulong rhat;
                bool rcarry;
                ulong qhat;
                // This special-case is REQUIRED for hardware div safety:
                // if uHi == v1n then the true quotient is >= 2^64, so DIV would #DE.
                if (u2 == v1n)
                {
                    rhat = u1 + v1n;
                    rcarry = rhat < u1;
                    qhat = ulong.MaxValue;
                }
                else
                {
                    rcarry = false;

#pragma warning disable SYSLIB5004 // X86Base.X64.DivRem is marked Experimental/preview
                    (ulong qhat1, ulong r) = X86Base.X64.DivRem(u1, u2, v1n);
#pragma warning restore SYSLIB5004
                    rhat = r;
                    qhat = qhat1;

                    // Reciprocal path
                }

                ulong hi = Multiply64(qhat, v0, out var lo);

                if (!rcarry && (hi > rhat || (hi == rhat && lo > u0)))
                {
                    qhat--;
                    ulong lo2 = lo - v0;
                    hi -= (lo < v0) ? 1UL : 0UL;
                    lo = lo2;

                    rhat += v1n;
                    rcarry = rhat < v1n;

                    if (!rcarry && (hi > rhat || (hi == rhat && lo > u0)))
                    {
                        qhat--;
                        lo2 = lo - v0;
                        hi -= (lo < v0) ? 1UL : 0UL;
                        lo = lo2;
                    }
                }

                ulong borrow = (u0 < lo) ? 1UL : 0UL;
                u0 -= lo;

                ulong hi1 = Multiply64(qhat, v1n, out lo);
                ulong sum = lo + hi;
                hi = hi1 + ((sum < lo) ? 1UL : 0UL);

                ulong t = u1 - sum;
                ulong b = (u1 < sum) ? 1UL : 0UL;
                u1 = t - borrow;
                borrow = b | ((t < borrow) ? 1UL : 0UL);

                t = u2 - hi;
                b = (u2 < hi) ? 1UL : 0UL;
                u2 = t - borrow;
                borrow = b | ((t < borrow) ? 1UL : 0UL);

                if (borrow != 0)
                {
                    ulong s0 = u0 + v0;
                    ulong c = (s0 < u0) ? 1UL : 0UL;

                    ulong s1 = u1 + v1n;
                    ulong c1 = (s1 < u1) ? 1UL : 0UL;
                    s1 += c;
                    c1 |= (s1 < c) ? 1UL : 0UL;

                    u0 = s0;
                    u1 = s1;

                    qhat--;
                }

                Unsafe.AsRef(in q.u0) = qhat;
            }

            // q3 is always 0 for 256/128 here.
            Unsafe.AsRef(in q.u3) = 0;

            // ------------------------------------------------------------
            // Remainder (u0..u1 in normalised space) - unnormalise.
            // ------------------------------------------------------------
            Unsafe.SkipInit(out remainder);

            if (shift == 0)
            {
                Unsafe.AsRef(in remainder.u0) = u0;
                Unsafe.AsRef(in remainder.u1) = u1;
            }
            else
            {
                int rs = 64 - shift;
                Unsafe.AsRef(in remainder.u0) = (u0 >> shift) | (u1 << rs);
                Unsafe.AsRef(in remainder.u1) = u1 >> shift;
            }

            Unsafe.AsRef(in remainder.u2) = 0;
            Unsafe.AsRef(in remainder.u3) = 0;
        }

        [SkipLocalsInit]
        [MethodImpl(MethodImplOptions.NoInlining)]
        private static void DivideBy128Bits(in UInt256 x, in UInt256 y, out UInt256 q, out UInt256 remainder)
        {
            // ------------------------------------------------------------
            // n >= 2: Knuth D (specialised) with reciprocal qhat
            // ------------------------------------------------------------
            // Preconditions (debug-only)
            Debug.Assert(y.u1 != 0 && y.u2 == 0 && y.u3 == 0);

            // -------------------------
            // Normalise divisor (2 limbs)
            // -------------------------
            ulong y0 = y.u0;
            ulong y1 = y.u1;

            int shift = BitOperations.LeadingZeroCount(y1);

            ulong v0, v1n;
            if (shift != 0)
            {
                int rs = 64 - shift;
                v0 = y0 << shift;
                v1n = (y1 << shift) | (y0 >> rs);
            }
            else
            {
                v0 = y0;
                v1n = y1;
            }

            // Reciprocal of the normalised high limb.
            ulong vRecip = Reciprocal2By1(v1n);

            // -------------------------
            // Normalise dividend (5 limbs)
            // Load after divisor prep - avoids keeping u-limbs live across the Reciprocal call.
            // -------------------------
            ulong u0 = x.u0;
            ulong u1 = x.u1;
            ulong u2 = x.u2;
            ulong u3 = x.u3;
            ulong u4;

            if (shift != 0)
            {
                int rs = 64 - shift;

                // Shift high-to-low so each source limb is still intact when used.
                u4 = u3 >> rs;
                u3 = (u3 << shift) | (u2 >> rs);
                u2 = (u2 << shift) | (u1 >> rs);
                u1 = (u1 << shift) | (u0 >> rs);
                u0 <<= shift;
            }
            else
            {
                u4 = 0;
            }

            // Start touching out params only after all input loads are done (alias-safe).
            Unsafe.SkipInit(out q);

            // ------------------------------------------------------------
            // Step j=2: q2 from (u4:u3:u2)
            // ------------------------------------------------------------
            {
                ulong qhat;
                ulong rhat;
                bool rcarry;

                if (u4 == v1n)
                {
                    qhat = ulong.MaxValue;
                    rhat = u3 + v1n;
                    rcarry = rhat < u3;
                }
                else
                {
                    qhat = UDivRem2By1(u4, vRecip, v1n, u3, out rhat);
                    rcarry = false;
                }

                ulong hi = Multiply64(qhat, v0, out var lo);

                // Correct at most twice.
                if (!rcarry && (hi > rhat || (hi == rhat && lo > u2)))
                {
                    qhat--;
                    ulong lo2 = lo - v0;
                    hi -= (lo < v0) ? 1UL : 0UL;
                    lo = lo2;

                    rhat += v1n;
                    rcarry = rhat < v1n;

                    if (!rcarry && (hi > rhat || (hi == rhat && lo > u2)))
                    {
                        qhat--;
                        lo2 = lo - v0;
                        hi -= (lo < v0) ? 1UL : 0UL;
                        lo = lo2;
                    }
                }

                // Subtract qhat*v from u2,u3,u4 (3 limbs).
                ulong borrow = (u2 < lo) ? 1UL : 0UL;
                u2 -= lo;

                ulong hi1 = Multiply64(qhat, v1n, out lo);
                ulong sum = lo + hi;
                hi = hi1 + ((sum < lo) ? 1UL : 0UL);

                ulong t = u3 - sum;
                ulong b = (u3 < sum) ? 1UL : 0UL;
                u3 = t - borrow;
                borrow = b | ((t < borrow) ? 1UL : 0UL);

                t = u4 - hi;
                b = (u4 < hi) ? 1UL : 0UL;
                u4 = t - borrow;
                borrow = b | ((t < borrow) ? 1UL : 0UL);

                if (borrow != 0)
                {
                    // Add-back v and decrement qhat.
                    ulong s0 = u2 + v0;
                    ulong c = (s0 < u2) ? 1UL : 0UL;

                    ulong s1 = u3 + v1n;
                    ulong c1 = (s1 < u3) ? 1UL : 0UL;
                    s1 += c;
                    c1 |= (s1 < c) ? 1UL : 0UL;

                    u2 = s0;
                    u3 = s1;

                    qhat--;
                }
                Unsafe.AsRef(in q.u2) = qhat;
            }

            // ------------------------------------------------------------
            // Step j=1: q1 from (u3:u2:u1)
            // ------------------------------------------------------------
            {
                ulong qhat;
                ulong rhat;
                bool rcarry;

                if (u3 == v1n)
                {
                    qhat = ulong.MaxValue;
                    rhat = u2 + v1n;
                    rcarry = rhat < u2;
                }
                else
                {
                    qhat = UDivRem2By1(u3, vRecip, v1n, u2, out rhat);
                    rcarry = false;
                }

                ulong hi = Multiply64(qhat, v0, out var lo);

                if (!rcarry && (hi > rhat || (hi == rhat && lo > u1)))
                {
                    qhat--;
                    ulong lo2 = lo - v0;
                    hi -= (lo < v0) ? 1UL : 0UL;
                    lo = lo2;

                    rhat += v1n;
                    rcarry = rhat < v1n;

                    if (!rcarry && (hi > rhat || (hi == rhat && lo > u1)))
                    {
                        qhat--;
                        lo2 = lo - v0;
                        hi -= (lo < v0) ? 1UL : 0UL;
                        lo = lo2;
                    }
                }

                ulong borrow = (u1 < lo) ? 1UL : 0UL;
                u1 -= lo;

                ulong hi1 = Multiply64(qhat, v1n, out lo);
                ulong sum = lo + hi;
                hi = hi1 + ((sum < lo) ? 1UL : 0UL);

                ulong t = u2 - sum;
                ulong b = (u2 < sum) ? 1UL : 0UL;
                u2 = t - borrow;
                borrow = b | ((t < borrow) ? 1UL : 0UL);

                t = u3 - hi;
                b = (u3 < hi) ? 1UL : 0UL;
                u3 = t - borrow;
                borrow = b | ((t < borrow) ? 1UL : 0UL);

                if (borrow != 0)
                {
                    ulong s0 = u1 + v0;
                    ulong c = (s0 < u1) ? 1UL : 0UL;

                    ulong s1 = u2 + v1n;
                    ulong c1 = (s1 < u2) ? 1UL : 0UL;
                    s1 += c;
                    c1 |= (s1 < c) ? 1UL : 0UL;

                    u1 = s0;
                    u2 = s1;

                    qhat--;
                }
                Unsafe.AsRef(in q.u1) = qhat;
            }

            // ------------------------------------------------------------
            // Step j=0: q0 from (u2:u1:u0)
            // ------------------------------------------------------------
            {
                ulong qhat;
                ulong rhat;
                bool rcarry;

                if (u2 == v1n)
                {
                    qhat = ulong.MaxValue;
                    rhat = u1 + v1n;
                    rcarry = rhat < u1;
                }
                else
                {
                    qhat = UDivRem2By1(u2, vRecip, v1n, u1, out rhat);
                    rcarry = false;
                }

                ulong hi = Multiply64(qhat, v0, out var lo);

                if (!rcarry && (hi > rhat || (hi == rhat && lo > u0)))
                {
                    qhat--;
                    ulong lo2 = lo - v0;
                    hi -= (lo < v0) ? 1UL : 0UL;
                    lo = lo2;

                    rhat += v1n;
                    rcarry = rhat < v1n;

                    if (!rcarry && (hi > rhat || (hi == rhat && lo > u0)))
                    {
                        qhat--;
                        lo2 = lo - v0;
                        hi -= (lo < v0) ? 1UL : 0UL;
                        lo = lo2;
                    }
                }

                ulong borrow = (u0 < lo) ? 1UL : 0UL;
                u0 -= lo;

                ulong hi1 = Multiply64(qhat, v1n, out lo);
                ulong sum = lo + hi;
                hi = hi1 + ((sum < lo) ? 1UL : 0UL);

                ulong t = u1 - sum;
                ulong b = (u1 < sum) ? 1UL : 0UL;
                u1 = t - borrow;
                borrow = b | ((t < borrow) ? 1UL : 0UL);

                t = u2 - hi;
                b = (u2 < hi) ? 1UL : 0UL;
                u2 = t - borrow;
                borrow = b | ((t < borrow) ? 1UL : 0UL);

                if (borrow != 0)
                {
                    ulong s0 = u0 + v0;
                    ulong c = (s0 < u0) ? 1UL : 0UL;

                    ulong s1 = u1 + v1n;
                    ulong c1 = (s1 < u1) ? 1UL : 0UL;
                    s1 += c;
                    c1 |= (s1 < c) ? 1UL : 0UL;

                    u0 = s0;
                    u1 = s1;

                    qhat--;
                }

                Unsafe.AsRef(in q.u0) = qhat;
            }

            // q3 is always 0 for 256/128 here.
            Unsafe.AsRef(in q.u3) = 0;

            // ------------------------------------------------------------
            // Remainder (u0..u1 in normalised space) - unnormalise.
            // ------------------------------------------------------------
            Unsafe.SkipInit(out remainder);

            if (shift == 0)
            {
                Unsafe.AsRef(in remainder.u0) = u0;
                Unsafe.AsRef(in remainder.u1) = u1;
            }
            else
            {
                int rs = 64 - shift;
                Unsafe.AsRef(in remainder.u0) = (u0 >> shift) | (u1 << rs);
                Unsafe.AsRef(in remainder.u1) = u1 >> shift;
            }

            Unsafe.AsRef(in remainder.u2) = 0;
            Unsafe.AsRef(in remainder.u3) = 0;
        }

        [SkipLocalsInit]
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static ulong Multiply64(ulong a, ulong b, out ulong low)
        {
            if (Bmi2.X64.IsSupported)
            {
                // Two multiplies ends up being faster as it doesn't force spill to stack.
                low = a * b;
                return Bmi2.X64.MultiplyNoFlags(a, b);
            }
            else if (ArmBase.Arm64.IsSupported)
            {
                low = a * b;
                return ArmBase.Arm64.MultiplyHigh(a, b);
            }
            else
            {
                return Math.BigMul(a, b, out low);
            }
        }

        [SkipLocalsInit]
        [MethodImpl(MethodImplOptions.NoInlining | MethodImplOptions.AggressiveOptimization)]
        private static void DivideBy128BitsAvx512(in UInt256 x, in UInt256 y, out UInt256 q, out UInt256 remainder)
        {
            Debug.Assert(Avx512F.IsSupported);
            Debug.Assert(y.u1 != 0 && y.u2 == 0 && y.u3 == 0);

            // Pull loads up front - avoids any alias nastiness with out params.
            ulong y0 = y.u0;
            ulong y1 = y.u1;

            // Dividend limbs.
            ulong u0 = x.u0;
            ulong u1 = x.u1;
            ulong u2 = x.u2;
            ulong u3 = x.u3;
            ulong u4;

            int shift = BitOperations.LeadingZeroCount(y1);

            ulong v0, v1n;

            if (shift != 0)
            {
                int rs = 64 - shift;

                // Normalise divisor.
                v0 = y0 << shift;
                v1n = (y1 << shift) | (y0 >> rs);

                // Normalise dividend with AVX-512 (mask-free).
                // uNorm lanes:
                //   [u0<<sh,
                //    (u1<<sh)|(u0>>rs),
                //    (u2<<sh)|(u1>>rs),
                //    (u3<<sh)|(u2>>rs),
                //    (0<<sh) |(u3>>rs), ...]
                Vector512<ulong> u = Vector512.Create(u0, u1, u2, u3, 0UL, 0UL, 0UL, 0UL);

                Vector512<ulong> shv = Vector512.Create((ulong)shift);
                Vector512<ulong> rsv = Vector512.Create((ulong)rs);

                Vector512<ulong> lo = Avx512F.ShiftLeftLogicalVariable(u, shv);
                Vector512<ulong> hi = Avx512F.ShiftRightLogicalVariable(u, rsv);

                // Lane-shift hi up by 1: [0, hi0, hi1, hi2, hi3, ...]
                hi = Avx512F.AlignRight64(hi, Vector512<ulong>.Zero, 7);

                Vector512<ulong> uNorm = Avx512F.Or(lo, hi);

                u0 = uNorm.GetElement(0);
                u1 = uNorm.GetElement(1);
                u2 = uNorm.GetElement(2);
                u3 = uNorm.GetElement(3);
                u4 = uNorm.GetElement(4);
            }
            else
            {
                v0 = y0;
                v1n = y1;
                u4 = 0;
            }

            ulong vRecip = Reciprocal2By1(v1n);

            Unsafe.SkipInit(out q);
            ref ulong q0Ref = ref Unsafe.As<UInt256, ulong>(ref q);

            Unsafe.Add(ref q0Ref, 2) = DivStep2_NoInline(ref u2, ref u3, ref u4, v0, v1n, vRecip);
            Unsafe.Add(ref q0Ref, 1) = DivStep2_NoInline(ref u1, ref u2, ref u3, v0, v1n, vRecip);
            q0Ref = DivStep2_NoInline(ref u0, ref u1, ref u2, v0, v1n, vRecip);
            Unsafe.Add(ref q0Ref, 3) = 0;

            Unsafe.SkipInit(out remainder);
            ref ulong r0Ref = ref Unsafe.As<UInt256, ulong>(ref remainder);

            if (shift == 0)
            {
                r0Ref = u0;
                Unsafe.Add(ref r0Ref, 1) = u1;
            }
            else
            {
                int rs = 64 - shift;

                // Mask-free AVX-512 unnormalise of (u1:u0) >> shift.
                Vector512<ulong> r = Vector512.Create(u0, u1, 0UL, 0UL, 0UL, 0UL, 0UL, 0UL);

                Vector512<ulong> shv = Vector512.Create((ulong)shift);
                Vector512<ulong> lsv = Vector512.Create((ulong)rs);

                Vector512<ulong> right = Avx512F.ShiftRightLogicalVariable(r, shv);
                Vector512<ulong> left = Avx512F.ShiftLeftLogicalVariable(r, lsv);

                // carry lane0 = left lane1 (u1<<rs)
                Vector512<ulong> carry = Avx512F.AlignRight64(Vector512<ulong>.Zero, left, 1);

                Vector512<ulong> rr = Avx512F.Or(right, carry);

                r0Ref = rr.GetElement(0);
                Unsafe.Add(ref r0Ref, 1) = rr.GetElement(1);
            }

            Unsafe.Add(ref r0Ref, 2) = 0;
            Unsafe.Add(ref r0Ref, 3) = 0;
        }

        [MethodImpl(MethodImplOptions.NoInlining)]
        private static ulong DivStep2_NoInline(ref ulong u0r, ref ulong u1r, ref ulong u2r, ulong v0, ulong v1, ulong recip)
            => DivStep2(ref u0r, ref u1r, ref u2r, v0, v1, recip);

        // ------------------------------------------------------------
        // Knuth steps (unrolled)
        // ------------------------------------------------------------
        [SkipLocalsInit]
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static ulong DivStep2(ref ulong u0r, ref ulong u1r, ref ulong u2r, ulong v0, ulong v1, ulong recip)
        {
            // Variant B style: load u1/u2 once. Delay u0 until after quotient estimate.
            ulong u1 = u1r;
            ulong u2 = u2r;

            ulong qhat;
            ulong rhat;
            bool rcarry;

            // Single shared out-home for everything.
            ulong lo;

            if (u2 == v1)
            {
                qhat = ulong.MaxValue;
                rhat = u1 + v1;
                rcarry = rhat < u1;
            }
            else
            {
                qhat = UDivRem2By1(u2, recip, v1, u1, out lo);
                rhat = lo;
                rcarry = false;
            }

            ulong u0 = u0r;

            // qhat*v0 once - reused for correction + subtraction
            ulong hi = Multiply64(qhat, v0, out lo); // hi:lo = qhat*v0

            // Correct at most twice
            if (!rcarry && (hi > rhat || (hi == rhat && lo > u0)))
            {
                qhat--;

                // (hi:lo) -= v0
                hi -= (lo < v0) ? 1UL : 0UL;
                lo -= v0;

                ulong sum = rhat + v1;
                rcarry = sum < rhat;
                rhat = sum;

                if (!rcarry && (hi > rhat || (hi == rhat && lo > u0)))
                {
                    qhat--;

                    hi -= (lo < v0) ? 1UL : 0UL;
                    lo -= v0;
                }
            }

            // Subtract qhat*v from u (3 limbs)
            ulong borrow = (u0 < lo) ? 1UL : 0UL;
            u0 -= lo;

            ulong hi1 = Multiply64(qhat, v1, out lo);
            ulong sum1 = lo + hi;
            hi = hi1 + ((sum1 < lo) ? 1UL : 0UL);

            ulong t = u1 - sum1;
            ulong b = (u1 < sum1) ? 1UL : 0UL;
            u1 = t - borrow;
            borrow = b | ((t < borrow) ? 1UL : 0UL);

            t = u2 - hi;
            b = (u2 < hi) ? 1UL : 0UL;
            u2 = t - borrow;
            borrow = b | ((t < borrow) ? 1UL : 0UL);

            // Store raw subtraction results first (preserves aliasing behaviour)
            u0r = u0;
            u1r = u1;
            u2r = u2;

            if (borrow == 0)
                return qhat;

            // Cold path: add-back and decrement qhat

            ulong s0 = u0 + v0;
            ulong c0 = (s0 < u0) ? 1UL : 0UL;

            ulong s1 = u1 + v1;
            ulong c1 = (s1 < u1) ? 1UL : 0UL;

            ulong s1c = s1 + c0;
            ulong c2 = (s1c < s1) ? 1UL : 0UL;

            // Write order matters for ref-aliasing semantics - match original: u0r, then u1r, then u2r += carry
            u0r = s0;
            u1r = s1c;
            u2r += (c1 | c2);

            return qhat - 1;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static ulong DivStep3(ref ulong u0, ref ulong u1, ref ulong u2, ref ulong u3, ulong v0, ulong v1, ulong v2, ulong recip)
        {
            ulong qhat, rhat, rcarry;
            if (u3 == v2)
            {
                qhat = ulong.MaxValue;
                ulong sum = u2 + v2;
                rcarry = (sum < u2) ? 1UL : 0UL;
                rhat = sum;
            }
            else
            {
                qhat = UDivRem2By1(u3, recip, v2, u2, out rhat);
                rcarry = 0;
            }

            bool ret;
            if (rcarry != 0)
                ret = false;
            else
            {
                ulong pHi = Multiply64(qhat, v1, out ulong pLo);

                // if qhat*vNext > rhat*b + uCorr then decrement
                if (pHi > rhat || (pHi == rhat && pLo > u1))
                {
                    qhat--;

                    ulong sum1 = rhat + v2;
                    if (sum1 < rhat)
                        rcarry = 1;

                    rhat = sum1;
                    ret = true;
                }
                else
                {
                    ret = false;
                }
            }

            if (ret && rcarry == 0)

            {
                ulong pHi = Multiply64(qhat, v1, out ulong pLo);

                // if qhat*vNext > rhat*b + uCorr then decrement
                if (pHi > rhat || (pHi == rhat && pLo > u1))
                {
                    qhat--;

                    ulong sum = rhat + v2;
                    if (sum < rhat)
                        rcarry = 1;

                    rhat = sum;
                }
            }

            ulong borrow1 = 0;
            ulong carry = 0;

            ulong pHi1 = Multiply64(qhat, v0, out ulong pLo1);
            ulong sum2 = pLo1 + carry;
            ulong c2 = (sum2 < pLo1) ? 1UL : 0UL;
            carry = pHi1 + c2;
            SubInPlace(ref u0, sum2, ref borrow1);

            pHi1 = Multiply64(qhat, v1, out pLo1);
            sum2 = pLo1 + carry;
            c2 = (sum2 < pLo1) ? 1UL : 0UL;
            carry = pHi1 + c2;
            SubInPlace(ref u1, sum2, ref borrow1);

            pHi1 = Multiply64(qhat, v2, out pLo1);
            sum2 = pLo1 + carry;
            c2 = (sum2 < pLo1) ? 1UL : 0UL;
            carry = pHi1 + c2;
            SubInPlace(ref u2, sum2, ref borrow1);

            SubInPlace(ref u3, carry, ref borrow1);
            ulong borrow = borrow1;

            if (borrow != 0)
            {
                AddBack3(ref u0, ref u1, ref u2, ref u3, v0, v1, v2);
                qhat--;
            }

            return qhat;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static ulong DivStep4(in UInt256 u, ref ulong u4, in UInt256 v, ulong recip, out UInt256 rem)
        {
            ulong qhat, rhat, rcarry;
            if (u4 == v.u3)
            {
                qhat = ulong.MaxValue;
                ulong sum = u.u3 + v.u3;
                rcarry = (sum < u.u3) ? 1UL : 0UL;
                rhat = sum;
            }
            else
            {
                qhat = UDivRem2By1(u4, recip, v.u3, u.u3, out rhat);
                rcarry = 0;
            }

            if (CorrectQHatOnce(ref qhat, ref rhat, ref rcarry, v.u3, v.u2, u.u2))
                CorrectQHatOnce(ref qhat, ref rhat, ref rcarry, v.u3, v.u2, u.u2);

            ulong borrow = SubMul4(in u, ref u4, in v, qhat, out rem);

            if (borrow != 0)
            {
                if (!AddOverflow(in rem, in v, out rem))
                {
                    u4 += 1;
                }
                qhat--;
            }

            return qhat;
        }
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static ulong DivStep4(ref ulong u0, ref ulong u1, ref ulong u2, ref ulong u3, ref ulong u4, in UInt256 v, ulong recip)
        {
            ulong qhat, rhat, rcarry;
            if (u4 == v.u3)
            {
                qhat = ulong.MaxValue;
                ulong sum = u3 + v.u3;
                rcarry = (sum < u3) ? 1UL : 0UL;
                rhat = sum;
            }
            else
            {
                qhat = UDivRem2By1(u4, recip, v.u3, u3, out rhat);
                rcarry = 0;
            }

            if (CorrectQHatOnce(ref qhat, ref rhat, ref rcarry, v.u3, v.u2, u2))
                CorrectQHatOnce(ref qhat, ref rhat, ref rcarry, v.u3, v.u2, u2);

            ulong borrow = SubMul4(ref u0, ref u1, ref u2, ref u3, ref u4, v.u0, v.u1, v.u2, v.u3, qhat);

            if (borrow != 0)
            {
                AddBack4(ref u0, ref u1, ref u2, ref u3, ref u4, v.u0, v.u1, v.u2, v.u3);
                qhat--;
            }

            return qhat;
        }

        // ------------------------------------------------------------
        // qhat correction (at most twice in Knuth D)
        // ------------------------------------------------------------
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static bool CorrectQHatOnce(ref ulong qhat, ref ulong rhat, ref ulong rcarry, ulong vHi, ulong vNext, ulong uCorr)
        {
            if (rcarry != 0)
                return false;

            ulong pHi = Multiply64(qhat, vNext, out ulong pLo);

            // if qhat*vNext > rhat*b + uCorr then decrement
            if (pHi > rhat || (pHi == rhat && pLo > uCorr))
            {
                qhat--;

                ulong sum = rhat + vHi;
                if (sum < rhat)
                    rcarry = 1;

                rhat = sum;
                return true;
            }

            return false;
        }

        // ------------------------------------------------------------
        // Multiply-subtract and add-back
        // ------------------------------------------------------------

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static ulong SubMul3(ref ulong u0, ref ulong u1, ref ulong u2, ref ulong u3, ulong v0, ulong v1, ulong v2, ulong q)
        {
            ulong borrow = 0;
            ulong carry = 0;

            ulong pHi = Multiply64(q, v0, out ulong pLo);
            ulong sum = pLo + carry;
            ulong c2 = (sum < pLo) ? 1UL : 0UL;
            carry = pHi + c2;
            SubInPlace(ref u0, sum, ref borrow);

            pHi = Multiply64(q, v1, out pLo);
            sum = pLo + carry;
            c2 = (sum < pLo) ? 1UL : 0UL;
            carry = pHi + c2;
            SubInPlace(ref u1, sum, ref borrow);

            pHi = Multiply64(q, v2, out pLo);
            sum = pLo + carry;
            c2 = (sum < pLo) ? 1UL : 0UL;
            carry = pHi + c2;
            SubInPlace(ref u2, sum, ref borrow);

            SubInPlace(ref u3, carry, ref borrow);

            return borrow;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static ulong SubMul4(in UInt256 u, ref ulong u4, in UInt256 v, ulong q, out UInt256 rem)
        {
            ulong borrow = 0;
            ulong carry = 0;

            ulong pHi = Multiply64(q, v.u0, out ulong pLo);
            ulong sum = pLo + carry;
            ulong c2 = (sum < pLo) ? 1UL : 0UL;
            carry = pHi + c2;
            var r0 = Sub(u.u0, sum, ref borrow);

            pHi = Multiply64(q, v.u1, out pLo);
            sum = pLo + carry;
            c2 = (sum < pLo) ? 1UL : 0UL;
            carry = pHi + c2;
            var r1 = Sub(u.u1, sum, ref borrow);

            pHi = Multiply64(q, v.u2, out pLo);
            sum = pLo + carry;
            c2 = (sum < pLo) ? 1UL : 0UL;
            carry = pHi + c2;
            var r2 = Sub(u.u2, sum, ref borrow);
            pHi = Multiply64(q, v.u3, out pLo);
            sum = pLo + carry;
            c2 = (sum < pLo) ? 1UL : 0UL;
            carry = pHi + c2;
            var r3 = Sub(u.u3, sum, ref borrow);

            SubInPlace(ref u4, carry, ref borrow);

            rem = Create(r0, r1, r2, r3);
            return borrow;
        }
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static ulong SubMul4(ref ulong u0, ref ulong u1, ref ulong u2, ref ulong u3, ref ulong u4, ulong v0, ulong v1, ulong v2, ulong v3, ulong q)
        {
            ulong borrow = 0;
            ulong carry = 0;

            ulong pHi = Multiply64(q, v0, out ulong pLo);
            ulong sum = pLo + carry;
            ulong c2 = (sum < pLo) ? 1UL : 0UL;
            carry = pHi + c2;
            SubInPlace(ref u0, sum, ref borrow);

            pHi = Multiply64(q, v1, out pLo);
            sum = pLo + carry;
            c2 = (sum < pLo) ? 1UL : 0UL;
            carry = pHi + c2;
            SubInPlace(ref u1, sum, ref borrow);

            pHi = Multiply64(q, v2, out pLo);
            sum = pLo + carry;
            c2 = (sum < pLo) ? 1UL : 0UL;
            carry = pHi + c2;
            SubInPlace(ref u2, sum, ref borrow);

            pHi = Multiply64(q, v3, out pLo);
            sum = pLo + carry;
            c2 = (sum < pLo) ? 1UL : 0UL;
            carry = pHi + c2;
            SubInPlace(ref u3, sum, ref borrow);

            SubInPlace(ref u4, carry, ref borrow);

            return borrow;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static void AddBack3(ref ulong u0, ref ulong u1, ref ulong u2, ref ulong u3, ulong v0, ulong v1, ulong v2)
        {
            ulong c = 0;
            AddWithCarry(u0, v0, ref c, out u0);
            AddWithCarry(u1, v1, ref c, out u1);
            AddWithCarry(u2, v2, ref c, out u2);
            u3 += c;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static void AddBack4(ref ulong u0, ref ulong u1, ref ulong u2, ref ulong u3, ref ulong u4, ulong v0, ulong v1, ulong v2, ulong v3)
        {
            ulong c = 0;
            AddWithCarry(u0, v0, ref c, out u0);
            AddWithCarry(u1, v1, ref c, out u1);
            AddWithCarry(u2, v2, ref c, out u2);
            AddWithCarry(u3, v3, ref c, out u3);
            u4 += c;
        }


        // ------------------------------------------------------------
        // Low-level arithmetic primitives
        // ------------------------------------------------------------
        [SkipLocalsInit]
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static ulong MulHigh(ulong a, ulong b)
        {
            if (Bmi2.X64.IsSupported)
            {
                return Bmi2.X64.MultiplyNoFlags(a, b);
            }
            else if (ArmBase.Arm64.IsSupported)
            {
                return ArmBase.Arm64.MultiplyHigh(a, b);
            }
            else
            {
                return Math.BigMul(a, b, out _);
            }
        }

        private static ulong Sub(ulong x, ulong y, ref ulong borrow)
        {
            ulong t = x - y;
            ulong b1 = (x < y) ? 1UL : 0UL;
            ulong t2 = t - borrow;
            ulong b2 = (t < borrow) ? 1UL : 0UL;
            borrow = b1 | b2;
            return t2;
        }
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static void SubInPlace(ref ulong x, ulong y, ref ulong borrow)
        {
            ulong t = x - y;
            ulong b1 = (x < y) ? 1UL : 0UL;
            ulong t2 = t - borrow;
            ulong b2 = (t < borrow) ? 1UL : 0UL;
            x = t2;
            borrow = b1 | b2;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static UInt256 Create(ulong u0, ulong u1, ulong u2, ulong u3)
        {
            Unsafe.SkipInit(out UInt256 r);
            ref ulong p = ref Unsafe.As<UInt256, ulong>(ref r);
            p = u0;
            Unsafe.Add(ref p, 1) = u1;
            Unsafe.Add(ref p, 2) = u2;
            Unsafe.Add(ref p, 3) = u3;
            return r;
        }
    }
}
