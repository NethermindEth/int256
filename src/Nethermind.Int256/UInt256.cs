// SPDX-FileCopyrightText: 2023 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Buffers.Binary;
using System.Globalization;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics.X86;
using System.Runtime.Intrinsics;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;

[assembly: InternalsVisibleTo("Nethermind.Int256.Tests")]

namespace Nethermind.Int256
{
    [StructLayout(LayoutKind.Explicit)]
    public readonly struct UInt256 :
        IEquatable<UInt256>,
        IComparable,
        IComparable<UInt256>,
        IConvertible,
        ISpanFormattable,
        ISpanParsable<UInt256>,
        IBinaryInteger<UInt256>,
        IUnsignedNumber<UInt256>,
        IMinMaxValue<UInt256>,
        IInteger<UInt256>
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
            if (Vector256<uint>.IsSupported)
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
            if (Vector256<ulong>.IsSupported)
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
                    if (Vector256<byte>.IsSupported)
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
                if (Vector256<ulong>.IsSupported)
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

        private uint r0 => (uint)u0;
        private uint r1 => (uint)(u0 >> 32);
        private uint r2 => (uint)u1;
        private uint r3 => (uint)(u1 >> 32);

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
                if (Vector256<uint>.IsSupported)
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
                if (Vector256<uint>.IsSupported)
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

        private static ReadOnlySpan<byte> s_broadcastLookup => new byte[] {
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
        };

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
            if (!Avx2.IsSupported && !Vector256<ulong>.IsSupported)
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
            if (m.IsZero)
            {
                res = Zero;
                return;
            }

            if (AddOverflow(x, y, out UInt256 intermediate))
            {
                const int length = 5;
                Span<ulong> sum = stackalloc ulong[length] { intermediate.u0, intermediate.u1, intermediate.u2, intermediate.u3, 1 };
                Span<ulong> quot = stackalloc ulong[length];
                Udivrem(ref MemoryMarshal.GetReference(quot), ref MemoryMarshal.GetReference(sum), length, in m, out res);
            }
            else
            {
                Mod(intermediate, m, out res);
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
                res = (((ulong)x) % ((ulong)y));
                return;
            }

            const int length = 4;
            Span<ulong> quot = stackalloc ulong[length];
            Udivrem(ref MemoryMarshal.GetReference(quot), ref Unsafe.As<UInt256, ulong>(ref Unsafe.AsRef(in x)), length, y, out res);
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
        private static ulong SubMulTo(Span<ulong> x, in Span<ulong> y, ulong multiplier)
        {
            ulong borrow = 0;
            for (int i = 0; i < y.Length; i++)
            {
                ulong borrow1 = 0;
                SubtractWithBorrow(x[i], borrow, ref borrow1, out ulong s);
                (ulong ph, ulong pl) = Multiply64(y[i], multiplier);
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
            ulong reciprocal = Reciprocal2by1(d);
            ulong rem = u[^1];
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
            ulong x0 = x.u0;
            ulong y0 = y.u0;
            // If both inputs fit in 64 bits, use a simple multiplication routine.
            if ((x.u1 | x.u2 | x.u3 | y.u1 | y.u2 | y.u3) == 0)
            {
                // Fast multiply for numbers less than 2^64 (18,446,744,073,709,551,615)
                ulong high = Math.BigMul(x0, y0, out ulong low);
                // Assignment to res after multiply in case is used as input for x or y (by ref aliasing)
                res = default;
                Unsafe.AsRef(in res.u0) = low;
                Unsafe.AsRef(in res.u1) = high;
                return;
            }
            ref ulong rx = ref Unsafe.As<UInt256, ulong>(ref Unsafe.AsRef(in x));
            ref ulong ry = ref Unsafe.As<UInt256, ulong>(ref Unsafe.AsRef(in y));

            (ulong carry, ulong r0) = Multiply64(rx, ry);
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
            (ulong carry0, ulong res0) = Multiply64(u0, u0);
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

        public void Exp(in UInt256 e, out UInt256 res) => Exp(this, e, out res);

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
                ulong highUL = Math.BigMul(x.u0, y.u0, out ulong lowUL);
                // Assignment to high, low after multiply in case either is used as input for x or y (by ref aliasing)
                high = default;
                low = default;
                Unsafe.AsRef(in low.u0) = lowUL;
                Unsafe.AsRef(in low.u1) = highUL;
                return;
            }

            (ulong carry, ulong l0) = Multiply64(x.u0, y.u0);
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
                res = ((ulong)x) / (ulong)y;
                return;
            }

            // At this point, we know
            // x/y ; x > y > 0

            UInt256 intermediate = default; // initialize with zeros
            const int length = 4;
            Udivrem(ref Unsafe.As<UInt256, ulong>(ref intermediate), ref Unsafe.As<UInt256, ulong>(ref Unsafe.AsRef(in x)), length, y, out UInt256 _);
            res = intermediate;
        }

        public void Divide(in UInt256 a, out UInt256 res) => Divide(this, a, out res);

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        internal static (ulong quo, ulong rem) Div64(ulong hi, ulong lo, ulong y)
        {
            const ulong two32 = ((ulong)1) << 32;
            const ulong mask32 = two32 - 1;
            if (y == 0)
            {
                ThrowDivideByZeroException();
            }

            if (y <= hi)
            {
                ThrowOverflowException("y <= hi");
            }

            var s = LeadingZeros(y);
            y <<= s;

            ulong yn1 = y >> 32;
            ulong yn0 = y & mask32;
            ulong un32 = NativeLsh(hi, s) | Rsh(lo, (64 - s));
            ulong un10 = NativeLsh(lo, s);
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

            return (q1 * two32 + q0, NativeRsh((un21 * two32 + un0 - q0 * y), s));
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

        [OverloadResolutionPriority(1)]
        public static UInt256 operator <<(in UInt256 a, int n)
        {
            a.LeftShift(n, out UInt256 res);
            return res;
        }

        public static UInt256 operator <<(UInt256 a, int n)
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

        [OverloadResolutionPriority(1)]
        public static UInt256 operator >>(in UInt256 a, int n)
        {
            a.RightShift(n, out UInt256 res);
            return res;
        }

        public static UInt256 operator >>(UInt256 a, int n)
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
            if (Vector256<ulong>.IsSupported)
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
            if (Vector256<ulong>.IsSupported)
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

        [OverloadResolutionPriority(1)]
        public static UInt256 operator |(in UInt256 a, in UInt256 b)
        {
            Or(a, b, out UInt256 res);
            return res;
        }

        public static UInt256 operator |(UInt256 a, UInt256 b)
        {
            Or(in a, in b, out UInt256 res);
            return res;
        }

        public static void And(in UInt256 a, in UInt256 b, out UInt256 res)
        {
            if (Vector256<ulong>.IsSupported)
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

        [OverloadResolutionPriority(1)]
        public static UInt256 operator &(in UInt256 a, in UInt256 b)
        {
            And(a, b, out UInt256 res);
            return res;
        }

        public static UInt256 operator &(UInt256 a, UInt256 b)
        {
            And(in a, in b, out UInt256 res);
            return res;
        }

        public static void Xor(in UInt256 a, in UInt256 b, out UInt256 res)
        {
            if (Vector256<long>.IsSupported)
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

        [OverloadResolutionPriority(1)]
        public static UInt256 operator ^(in UInt256 a, in UInt256 b)
        {
            Xor(a, b, out UInt256 res);
            return res;
        }

        public static UInt256 operator ^(UInt256 a, UInt256 b)
        {
            Xor(in a, in b, out UInt256 res);
            return res;
        }

        [OverloadResolutionPriority(1)]
        public static UInt256 operator ~(in UInt256 a)
        {
            Not(in a, out UInt256 res);
            return res;
        }

        public static UInt256 operator ~(UInt256 a)
        {
            Not(in a, out UInt256 res);
            return res;
        }

        [OverloadResolutionPriority(1)]
        public static UInt256 operator +(in UInt256 a, in UInt256 b)
        {
            AddOverflow(in a, in b, out UInt256 res);
            return res;
        }

        public static UInt256 operator +(UInt256 a, UInt256 b)
        {
            AddOverflow(in a, in b, out UInt256 res);
            return res;
        }

        [OverloadResolutionPriority(1)]
        public static UInt256 operator ++(in UInt256 a)
        {
            AddOverflow(in a, 1, out UInt256 res);
            return res;
        }

        public static UInt256 operator ++(UInt256 a)
        {
            AddOverflow(in a, 1, out UInt256 res);
            return res;
        }

        [OverloadResolutionPriority(1)]
        public static UInt256 operator -(in UInt256 a, in UInt256 b)
        {
            if (SubtractUnderflow(in a, in b, out UInt256 c))
            {
                ThrowOverflowException($"Underflow in subtraction {a} - {b}");
            }

            return c;
        }

        public static UInt256 operator -(UInt256 a, UInt256 b)
        {
            if (SubtractUnderflow(in a, in b, out UInt256 c))
            {
                ThrowOverflowException($"Underflow in subtraction {a} - {b}");
            }

            return c;
        }

        [OverloadResolutionPriority(1)]
        public static bool operator ==(in UInt256 a, in UInt256 b) => a.Equals(b);

        public static bool operator ==(UInt256 a, UInt256 b) => a.Equals(b);

        [OverloadResolutionPriority(1)]
        public static bool operator !=(in UInt256 a, in UInt256 b) => !(a == b);

        public static bool operator !=(UInt256 a, UInt256 b) => !(a == b);

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

        [OverloadResolutionPriority(1)]
        public static UInt256 operator *(in UInt256 a, in UInt256 b)
        {
            Multiply(in a, in b, out UInt256 c);
            return c;
        }

        public static UInt256 operator *(UInt256 a, UInt256 b)
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

        [OverloadResolutionPriority(1)]
        public static UInt256 operator /(in UInt256 a, in UInt256 b)
        {
            Divide(in a, in b, out UInt256 c);
            return c;
        }

        public static UInt256 operator /(UInt256 a, UInt256 b)
        {
            Divide(in a, in b, out UInt256 c);
            return c;
        }

        [OverloadResolutionPriority(1)]
        public static bool operator <(in UInt256 a, in UInt256 b) => LessThan(in a, in b);
        public static bool operator <(UInt256 a, UInt256 b) => LessThan(in a, in b);
        public static bool operator <(in UInt256 a, int b) => LessThan(in a, b);
        public static bool operator <(int a, in UInt256 b) => LessThan(a, in b);
        public static bool operator <(in UInt256 a, uint b) => LessThan(in a, b);
        public static bool operator <(uint a, in UInt256 b) => LessThan(a, in b);
        public static bool operator <(in UInt256 a, long b) => LessThan(in a, b);
        public static bool operator <(long a, in UInt256 b) => LessThan(a, in b);
        public static bool operator <(in UInt256 a, ulong b) => LessThan(in a, b);
        public static bool operator <(ulong a, in UInt256 b) => LessThan(a, in b);
        [OverloadResolutionPriority(1)]
        public static bool operator <=(in UInt256 a, in UInt256 b) => !LessThan(in b, in a);
        public static bool operator <=(UInt256 a, UInt256 b) => !LessThan(in b, in a);
        public static bool operator <=(in UInt256 a, int b) => !LessThan(b, in a);
        public static bool operator <=(int a, in UInt256 b) => !LessThan(in b, a);
        public static bool operator <=(in UInt256 a, uint b) => !LessThan(b, in a);
        public static bool operator <=(uint a, in UInt256 b) => !LessThan(in b, a);
        public static bool operator <=(in UInt256 a, long b) => !LessThan(b, in a);
        public static bool operator <=(long a, in UInt256 b) => !LessThan(in b, a);
        public static bool operator <=(in UInt256 a, ulong b) => !LessThan(b, in a);
        public static bool operator <=(ulong a, UInt256 b) => !LessThan(in b, a);
        [OverloadResolutionPriority(1)]
        public static bool operator >(in UInt256 a, in UInt256 b) => LessThan(in b, in a);
        public static bool operator >(UInt256 a, UInt256 b) => LessThan(in b, in a);
        public static bool operator >(in UInt256 a, int b) => LessThan(b, in a);
        public static bool operator >(int a, in UInt256 b) => LessThan(in b, a);
        public static bool operator >(in UInt256 a, uint b) => LessThan(b, in a);
        public static bool operator >(uint a, in UInt256 b) => LessThan(in b, a);
        public static bool operator >(in UInt256 a, long b) => LessThan(b, in a);
        public static bool operator >(long a, in UInt256 b) => LessThan(in b, a);
        public static bool operator >(in UInt256 a, ulong b) => LessThan(b, in a);
        public static bool operator >(ulong a, in UInt256 b) => LessThan(in b, a);
        [OverloadResolutionPriority(1)]
        public static bool operator >=(in UInt256 a, in UInt256 b) => !LessThan(in a, in b);
        public static bool operator >=(UInt256 a, UInt256 b) => !LessThan(in a, in b);
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
            if (!Avx2.IsSupported && !Vector256<ulong>.IsSupported)
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
            if (Vector256<uint>.IsSupported)
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
            if (Vector256<uint>.IsSupported)
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

        public static UInt256 Parse(in ReadOnlySpan<char> value, NumberStyles numberStyles) => !TryParseCore(value, numberStyles, CultureInfo.InvariantCulture, out UInt256 c) ? throw new FormatException() : c;

        public static UInt256 Parse(ReadOnlySpan<char> s, NumberStyles style, IFormatProvider? provider)
            => TryParseCore(s, style, provider ?? CultureInfo.InvariantCulture, out UInt256 result)
                ? result
                : throw new FormatException();

        public static UInt256 Parse(string s, NumberStyles style, IFormatProvider? provider)
            => Parse(s.AsSpan(), style, provider);

        public static bool TryParse([NotNullWhen(true)] string? value, out UInt256 result)
        {
            if (value is null)
            {
                result = Zero;
                return false;
            }
            return TryParse(value.AsSpan(), out result);
        }

        public static bool TryParse([NotNullWhen(true)] string? s, NumberStyles style, IFormatProvider? provider, out UInt256 result)
        {
            if (s is null)
            {
                result = Zero;
                return false;
            }
            return TryParseCore(s.AsSpan(), style, provider ?? CultureInfo.InvariantCulture, out result);
        }

        public static bool TryParse(ReadOnlySpan<char> value, out UInt256 result) => value.StartsWith("0x", StringComparison.OrdinalIgnoreCase)
            ? TryParseCore(value[2..], NumberStyles.HexNumber, CultureInfo.InvariantCulture, out result)
            : TryParseCore(value, NumberStyles.Integer, CultureInfo.InvariantCulture, out result);

        public static bool TryParse(ReadOnlySpan<char> value, NumberStyles style, IFormatProvider? provider, out UInt256 result)
            => TryParseCore(value, style, provider, out result);

        private static bool TryParseCore(ReadOnlySpan<char> value, NumberStyles style, IFormatProvider? provider, out UInt256 result)
        {
            if (value.IsEmpty)
            {
                result = Zero;
                return false;
            }

            BigInteger a;
            bool bigParsedProperly;
            if ((style & NumberStyles.HexNumber) == NumberStyles.HexNumber && value[0] != '0')
            {
                Span<char> fixedHexValue = stackalloc char[value.Length + 1];
                fixedHexValue[0] = '0';
                value.CopyTo(fixedHexValue[1..]);
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

        #region INumberBase<UInt256> Implementation

        /// <inheritdoc />
        static UInt256 INumberBase<UInt256>.One => One;

        /// <inheritdoc />
        static int INumberBase<UInt256>.Radix => 2;

        /// <inheritdoc />
        static UInt256 INumberBase<UInt256>.Zero => Zero;

        /// <inheritdoc />
        static UInt256 IAdditiveIdentity<UInt256, UInt256>.AdditiveIdentity => Zero;

        /// <inheritdoc />
        static UInt256 IMultiplicativeIdentity<UInt256, UInt256>.MultiplicativeIdentity => One;

        /// <inheritdoc />
        public static UInt256 Abs(UInt256 value) => value;

        /// <inheritdoc />
        static bool INumberBase<UInt256>.IsCanonical(UInt256 value) => true;

        /// <inheritdoc />
        static bool INumberBase<UInt256>.IsComplexNumber(UInt256 value) => false;

        /// <inheritdoc />
        public static bool IsEvenInteger(UInt256 value) => (value.u0 & 1) == 0;

        /// <inheritdoc />
        static bool INumberBase<UInt256>.IsFinite(UInt256 value) => true;

        /// <inheritdoc />
        static bool INumberBase<UInt256>.IsImaginaryNumber(UInt256 value) => false;

        /// <inheritdoc />
        static bool INumberBase<UInt256>.IsInfinity(UInt256 value) => false;

        /// <inheritdoc />
        static bool INumberBase<UInt256>.IsInteger(UInt256 value) => true;

        /// <inheritdoc />
        static bool INumberBase<UInt256>.IsNaN(UInt256 value) => false;

        /// <inheritdoc />
        static bool INumberBase<UInt256>.IsNegative(UInt256 value) => false;

        /// <inheritdoc />
        static bool INumberBase<UInt256>.IsNegativeInfinity(UInt256 value) => false;

        /// <inheritdoc />
        static bool INumberBase<UInt256>.IsNormal(UInt256 value) => !value.IsZero;

        /// <inheritdoc />
        public static bool IsOddInteger(UInt256 value) => (value.u0 & 1) != 0;

        /// <inheritdoc />
        static bool INumberBase<UInt256>.IsPositive(UInt256 value) => true;

        /// <inheritdoc />
        static bool INumberBase<UInt256>.IsPositiveInfinity(UInt256 value) => false;

        /// <inheritdoc />
        static bool INumberBase<UInt256>.IsRealNumber(UInt256 value) => true;

        /// <inheritdoc />
        static bool INumberBase<UInt256>.IsSubnormal(UInt256 value) => false;

        /// <inheritdoc />
        static bool INumberBase<UInt256>.IsZero(UInt256 value) => value.IsZero;

        /// <inheritdoc />
        public static UInt256 MaxMagnitude(UInt256 x, UInt256 y) => Max(in x, in y);

        /// <inheritdoc />
        public static UInt256 MaxMagnitudeNumber(UInt256 x, UInt256 y) => Max(in x, in y);

        /// <inheritdoc />
        public static UInt256 MinMagnitude(UInt256 x, UInt256 y) => Min(in x, in y);

        /// <inheritdoc />
        public static UInt256 MinMagnitudeNumber(UInt256 x, UInt256 y) => Min(in x, in y);

        /// <inheritdoc />
        static UInt256 ISpanParsable<UInt256>.Parse(ReadOnlySpan<char> s, IFormatProvider? provider)
            => TryParse(s, out UInt256 result)
                ? result
                : throw new FormatException();

        /// <inheritdoc />
        static UInt256 IParsable<UInt256>.Parse(string s, IFormatProvider? provider)
            => TryParse(s, out UInt256 result)
                ? result
                : throw new FormatException();

        /// <inheritdoc />
        static bool ISpanParsable<UInt256>.TryParse(ReadOnlySpan<char> s, IFormatProvider? provider, out UInt256 result)
            => TryParse(s, out result);

        /// <inheritdoc />
        static bool IParsable<UInt256>.TryParse([NotNullWhen(true)] string? s, IFormatProvider? provider, out UInt256 result)
            => TryParse(s, out result);

        /// <inheritdoc />
        static bool INumberBase<UInt256>.TryConvertFromChecked<TOther>(TOther value, out UInt256 result)
            => TryConvertFromChecked(value, out result);

        /// <inheritdoc />
        static bool INumberBase<UInt256>.TryConvertFromSaturating<TOther>(TOther value, out UInt256 result)
            => TryConvertFromSaturating(value, out result);

        /// <inheritdoc />
        static bool INumberBase<UInt256>.TryConvertFromTruncating<TOther>(TOther value, out UInt256 result)
            => TryConvertFromTruncating(value, out result);

        /// <inheritdoc />
        static bool INumberBase<UInt256>.TryConvertToChecked<TOther>(UInt256 value, [MaybeNullWhen(false)] out TOther result)
            => TryConvertToChecked(value, out result);

        /// <inheritdoc />
        static bool INumberBase<UInt256>.TryConvertToSaturating<TOther>(UInt256 value, [MaybeNullWhen(false)] out TOther result)
            => TryConvertToSaturating(value, out result);

        /// <inheritdoc />
        static bool INumberBase<UInt256>.TryConvertToTruncating<TOther>(UInt256 value, [MaybeNullWhen(false)] out TOther result)
            => TryConvertToTruncating(value, out result);

        private static bool TryConvertFromChecked<TOther>(TOther value, out UInt256 result) where TOther : INumberBase<TOther>
        {
            if (typeof(TOther) == typeof(byte))
            {
                result = (byte)(object)value;
                return true;
            }
            if (typeof(TOther) == typeof(ushort))
            {
                result = (ushort)(object)value;
                return true;
            }
            if (typeof(TOther) == typeof(uint))
            {
                result = (uint)(object)value;
                return true;
            }
            if (typeof(TOther) == typeof(ulong))
            {
                result = (ulong)(object)value;
                return true;
            }
            if (typeof(TOther) == typeof(UInt128))
            {
                var v = (UInt128)(object)value;
                result = new UInt256((ulong)v, (ulong)(v >> 64), 0, 0);
                return true;
            }
            if (typeof(TOther) == typeof(nuint))
            {
                result = (nuint)(object)value;
                return true;
            }
            if (typeof(TOther) == typeof(sbyte))
            {
                var v = (sbyte)(object)value;
                if (v < 0) throw new OverflowException();
                result = (ulong)v;
                return true;
            }
            if (typeof(TOther) == typeof(short))
            {
                var v = (short)(object)value;
                if (v < 0) throw new OverflowException();
                result = (ulong)v;
                return true;
            }
            if (typeof(TOther) == typeof(int))
            {
                var v = (int)(object)value;
                if (v < 0) throw new OverflowException();
                result = (ulong)v;
                return true;
            }
            if (typeof(TOther) == typeof(long))
            {
                var v = (long)(object)value;
                if (v < 0) throw new OverflowException();
                result = (ulong)v;
                return true;
            }
            if (typeof(TOther) == typeof(Int128))
            {
                var v = (Int128)(object)value;
                if (v < 0) throw new OverflowException();
                result = new UInt256((ulong)v, (ulong)((UInt128)v >> 64), 0, 0);
                return true;
            }
            if (typeof(TOther) == typeof(nint))
            {
                var v = (nint)(object)value;
                if (v < 0) throw new OverflowException();
                result = (ulong)v;
                return true;
            }
            if (typeof(TOther) == typeof(Half))
            {
                var v = (Half)(object)value;
                double dv = (double)v;
                if (dv < 0 || double.IsNaN(dv) || double.IsInfinity(dv)) throw new OverflowException();
                result = (UInt256)dv;
                return true;
            }
            if (typeof(TOther) == typeof(float))
            {
                var v = (float)(object)value;
                if (v < 0 || float.IsNaN(v) || float.IsInfinity(v)) throw new OverflowException();
                result = (UInt256)(double)v;
                return true;
            }
            if (typeof(TOther) == typeof(double))
            {
                var v = (double)(object)value;
                if (v < 0 || double.IsNaN(v) || double.IsInfinity(v)) throw new OverflowException();
                result = (UInt256)v;
                return true;
            }
            if (typeof(TOther) == typeof(decimal))
            {
                var v = (decimal)(object)value;
                if (v < 0) throw new OverflowException();
                result = (UInt256)v;
                return true;
            }
            if (typeof(TOther) == typeof(BigInteger))
            {
                var v = (BigInteger)(object)value;
                result = (UInt256)v;
                return true;
            }

            result = default;
            return false;
        }

        private static bool TryConvertFromSaturating<TOther>(TOther value, out UInt256 result) where TOther : INumberBase<TOther>
        {
            if (typeof(TOther) == typeof(byte))
            {
                result = (byte)(object)value;
                return true;
            }
            if (typeof(TOther) == typeof(ushort))
            {
                result = (ushort)(object)value;
                return true;
            }
            if (typeof(TOther) == typeof(uint))
            {
                result = (uint)(object)value;
                return true;
            }
            if (typeof(TOther) == typeof(ulong))
            {
                result = (ulong)(object)value;
                return true;
            }
            if (typeof(TOther) == typeof(UInt128))
            {
                var v = (UInt128)(object)value;
                result = new UInt256((ulong)v, (ulong)(v >> 64), 0, 0);
                return true;
            }
            if (typeof(TOther) == typeof(nuint))
            {
                result = (nuint)(object)value;
                return true;
            }
            if (typeof(TOther) == typeof(sbyte))
            {
                var v = (sbyte)(object)value;
                result = v < 0 ? Zero : (ulong)v;
                return true;
            }
            if (typeof(TOther) == typeof(short))
            {
                var v = (short)(object)value;
                result = v < 0 ? Zero : (ulong)v;
                return true;
            }
            if (typeof(TOther) == typeof(int))
            {
                var v = (int)(object)value;
                result = v < 0 ? Zero : (ulong)v;
                return true;
            }
            if (typeof(TOther) == typeof(long))
            {
                var v = (long)(object)value;
                result = v < 0 ? Zero : (ulong)v;
                return true;
            }
            if (typeof(TOther) == typeof(Int128))
            {
                var v = (Int128)(object)value;
                result = v < 0 ? Zero : new UInt256((ulong)v, (ulong)((UInt128)v >> 64), 0, 0);
                return true;
            }
            if (typeof(TOther) == typeof(nint))
            {
                var v = (nint)(object)value;
                result = v < 0 ? Zero : (ulong)v;
                return true;
            }
            if (typeof(TOther) == typeof(Half))
            {
                var v = (double)(Half)(object)value;
                if (v < 0) result = Zero;
                else if (double.IsInfinity(v) || double.IsNaN(v)) result = MaxValue;
                else result = (UInt256)v;
                return true;
            }
            if (typeof(TOther) == typeof(float))
            {
                var v = (double)(float)(object)value;
                if (v < 0) result = Zero;
                else if (double.IsInfinity(v) || double.IsNaN(v)) result = MaxValue;
                else result = (UInt256)v;
                return true;
            }
            if (typeof(TOther) == typeof(double))
            {
                var v = (double)(object)value;
                if (v < 0) result = Zero;
                else if (double.IsInfinity(v) || double.IsNaN(v)) result = MaxValue;
                else result = (UInt256)v;
                return true;
            }
            if (typeof(TOther) == typeof(decimal))
            {
                var v = (decimal)(object)value;
                result = v < 0 ? Zero : (UInt256)v;
                return true;
            }
            if (typeof(TOther) == typeof(BigInteger))
            {
                var v = (BigInteger)(object)value;
                if (v < 0) result = Zero;
                else if (v > (BigInteger)MaxValue) result = MaxValue;
                else result = (UInt256)v;
                return true;
            }

            result = default;
            return false;
        }

        private static bool TryConvertFromTruncating<TOther>(TOther value, out UInt256 result) where TOther : INumberBase<TOther>
        {
            if (typeof(TOther) == typeof(byte))
            {
                result = (byte)(object)value;
                return true;
            }
            if (typeof(TOther) == typeof(ushort))
            {
                result = (ushort)(object)value;
                return true;
            }
            if (typeof(TOther) == typeof(uint))
            {
                result = (uint)(object)value;
                return true;
            }
            if (typeof(TOther) == typeof(ulong))
            {
                result = (ulong)(object)value;
                return true;
            }
            if (typeof(TOther) == typeof(UInt128))
            {
                var v = (UInt128)(object)value;
                result = new UInt256((ulong)v, (ulong)(v >> 64), 0, 0);
                return true;
            }
            if (typeof(TOther) == typeof(nuint))
            {
                result = (nuint)(object)value;
                return true;
            }
            if (typeof(TOther) == typeof(sbyte))
            {
                var v = (sbyte)(object)value;
                result = v < 0 ? new UInt256(unchecked((ulong)v), ulong.MaxValue, ulong.MaxValue, ulong.MaxValue) : (ulong)v;
                return true;
            }
            if (typeof(TOther) == typeof(short))
            {
                var v = (short)(object)value;
                result = v < 0 ? new UInt256(unchecked((ulong)v), ulong.MaxValue, ulong.MaxValue, ulong.MaxValue) : (ulong)v;
                return true;
            }
            if (typeof(TOther) == typeof(int))
            {
                var v = (int)(object)value;
                result = v < 0 ? new UInt256(unchecked((ulong)v), ulong.MaxValue, ulong.MaxValue, ulong.MaxValue) : (ulong)v;
                return true;
            }
            if (typeof(TOther) == typeof(long))
            {
                var v = (long)(object)value;
                result = v < 0 ? new UInt256(unchecked((ulong)v), ulong.MaxValue, ulong.MaxValue, ulong.MaxValue) : (ulong)v;
                return true;
            }
            if (typeof(TOther) == typeof(Int128))
            {
                var v = (Int128)(object)value;
                var unsigned = unchecked((UInt128)v);
                result = v < 0
                    ? new UInt256((ulong)unsigned, (ulong)(unsigned >> 64), ulong.MaxValue, ulong.MaxValue)
                    : new UInt256((ulong)unsigned, (ulong)(unsigned >> 64), 0, 0);
                return true;
            }
            if (typeof(TOther) == typeof(nint))
            {
                var v = (nint)(object)value;
                result = v < 0 ? new UInt256(unchecked((ulong)v), ulong.MaxValue, ulong.MaxValue, ulong.MaxValue) : (ulong)v;
                return true;
            }
            if (typeof(TOther) == typeof(BigInteger))
            {
                var v = (BigInteger)(object)value;
                Span<byte> bytes = stackalloc byte[32];
                if (!v.TryWriteBytes(bytes, out _, isUnsigned: false, isBigEndian: false))
                {
                    bytes.Fill((byte)(v.Sign < 0 ? 0xFF : 0));
                    v.TryWriteBytes(bytes[..Math.Min(v.GetByteCount(isUnsigned: false), 32)], out _, isUnsigned: false, isBigEndian: false);
                }
                result = new UInt256(bytes, isBigEndian: false);
                return true;
            }

            result = default;
            return false;
        }

        private static bool TryConvertToChecked<TOther>(UInt256 value, [MaybeNullWhen(false)] out TOther result) where TOther : INumberBase<TOther>
        {
            if (typeof(TOther) == typeof(byte))
            {
                result = (TOther)(object)(byte)value;
                return true;
            }
            if (typeof(TOther) == typeof(ushort))
            {
                result = (TOther)(object)(ushort)value;
                return true;
            }
            if (typeof(TOther) == typeof(uint))
            {
                result = (TOther)(object)(uint)value;
                return true;
            }
            if (typeof(TOther) == typeof(ulong))
            {
                result = (TOther)(object)(ulong)value;
                return true;
            }
            if (typeof(TOther) == typeof(UInt128))
            {
                if (value.u2 != 0 || value.u3 != 0) throw new OverflowException();
                result = (TOther)(object)(new UInt128(value.u1, value.u0));
                return true;
            }
            if (typeof(TOther) == typeof(nuint))
            {
                if (value.u1 != 0 || value.u2 != 0 || value.u3 != 0 || value.u0 > (ulong)nuint.MaxValue)
                {
                    throw new OverflowException();
                }
                result = (TOther)(object)(nuint)value.u0;
                return true;
            }
            if (typeof(TOther) == typeof(sbyte))
            {
                result = (TOther)(object)(sbyte)value;
                return true;
            }
            if (typeof(TOther) == typeof(short))
            {
                result = (TOther)(object)(short)value;
                return true;
            }
            if (typeof(TOther) == typeof(int))
            {
                result = (TOther)(object)(int)value;
                return true;
            }
            if (typeof(TOther) == typeof(long))
            {
                result = (TOther)(object)(long)value;
                return true;
            }
            if (typeof(TOther) == typeof(Int128))
            {
                if (value.u2 != 0 || value.u3 != 0 || value.u1 > long.MaxValue) throw new OverflowException();
                result = (TOther)(object)(new Int128(value.u1, value.u0));
                return true;
            }
            if (typeof(TOther) == typeof(nint))
            {
                if (value.u1 != 0 || value.u2 != 0 || value.u3 != 0) throw new OverflowException();
                result = (TOther)(object)checked((nint)value.u0);
                return true;
            }
            if (typeof(TOther) == typeof(Half))
            {
                result = (TOther)(object)(Half)(double)value;
                return true;
            }
            if (typeof(TOther) == typeof(float))
            {
                result = (TOther)(object)(float)(double)value;
                return true;
            }
            if (typeof(TOther) == typeof(double))
            {
                result = (TOther)(object)(double)value;
                return true;
            }
            if (typeof(TOther) == typeof(decimal))
            {
                result = (TOther)(object)(decimal)value;
                return true;
            }
            if (typeof(TOther) == typeof(BigInteger))
            {
                result = (TOther)(object)(BigInteger)value;
                return true;
            }

            result = default;
            return false;
        }

        private static bool TryConvertToSaturating<TOther>(UInt256 value, [MaybeNullWhen(false)] out TOther result) where TOther : INumberBase<TOther>
        {
            if (typeof(TOther) == typeof(byte))
            {
                result = (TOther)(object)((value.u1 | value.u2 | value.u3) != 0 || value.u0 > byte.MaxValue ? byte.MaxValue : (byte)value.u0);
                return true;
            }
            if (typeof(TOther) == typeof(ushort))
            {
                result = (TOther)(object)((value.u1 | value.u2 | value.u3) != 0 || value.u0 > ushort.MaxValue ? ushort.MaxValue : (ushort)value.u0);
                return true;
            }
            if (typeof(TOther) == typeof(uint))
            {
                result = (TOther)(object)((value.u1 | value.u2 | value.u3) != 0 || value.u0 > uint.MaxValue ? uint.MaxValue : (uint)value.u0);
                return true;
            }
            if (typeof(TOther) == typeof(ulong))
            {
                result = (TOther)(object)(value.u1 != 0 || value.u2 != 0 || value.u3 != 0 ? ulong.MaxValue : value.u0);
                return true;
            }
            if (typeof(TOther) == typeof(UInt128))
            {
                result = (TOther)(object)(value.u2 != 0 || value.u3 != 0 ? UInt128.MaxValue : new UInt128(value.u1, value.u0));
                return true;
            }
            if (typeof(TOther) == typeof(nuint))
            {
                result = (TOther)(object)(((value.u1 | value.u2 | value.u3) != 0 || value.u0 > (ulong)nuint.MaxValue) ? nuint.MaxValue : (nuint)value.u0);
                return true;
            }
            if (typeof(TOther) == typeof(sbyte))
            {
                result = (TOther)(object)(((value.u1 | value.u2 | value.u3) != 0 || value.u0 > (ulong)sbyte.MaxValue) ? sbyte.MaxValue : (sbyte)value.u0);
                return true;
            }
            if (typeof(TOther) == typeof(short))
            {
                result = (TOther)(object)(((value.u1 | value.u2 | value.u3) != 0 || value.u0 > (ulong)short.MaxValue) ? short.MaxValue : (short)value.u0);
                return true;
            }
            if (typeof(TOther) == typeof(int))
            {
                result = (TOther)(object)(((value.u1 | value.u2 | value.u3) != 0 || value.u0 > int.MaxValue) ? int.MaxValue : (int)value.u0);
                return true;
            }
            if (typeof(TOther) == typeof(long))
            {
                result = (TOther)(object)(((value.u1 | value.u2 | value.u3) != 0 || value.u0 > long.MaxValue) ? long.MaxValue : (long)value.u0);
                return true;
            }
            if (typeof(TOther) == typeof(Int128))
            {
                result = (TOther)(object)(value.u2 != 0 || value.u3 != 0 || value.u1 > (ulong)long.MaxValue ? Int128.MaxValue : new Int128(value.u1, value.u0));
                return true;
            }
            if (typeof(TOther) == typeof(nint))
            {
                result = (TOther)(object)(((value.u1 | value.u2 | value.u3) != 0 || value.u0 > (ulong)nint.MaxValue) ? nint.MaxValue : (nint)value.u0);
                return true;
            }
            if (typeof(TOther) == typeof(Half))
            {
                result = (TOther)(object)(Half)(double)value;
                return true;
            }
            if (typeof(TOther) == typeof(float))
            {
                result = (TOther)(object)(float)(double)value;
                return true;
            }
            if (typeof(TOther) == typeof(double))
            {
                result = (TOther)(object)(double)value;
                return true;
            }
            if (typeof(TOther) == typeof(decimal))
            {
                result = (TOther)(object)(decimal)value;
                return true;
            }
            if (typeof(TOther) == typeof(BigInteger))
            {
                result = (TOther)(object)(BigInteger)value;
                return true;
            }

            result = default;
            return false;
        }

        private static bool TryConvertToTruncating<TOther>(UInt256 value, [MaybeNullWhen(false)] out TOther result) where TOther : INumberBase<TOther>
        {
            if (typeof(TOther) == typeof(byte))
            {
                result = (TOther)(object)(byte)value.u0;
                return true;
            }
            if (typeof(TOther) == typeof(ushort))
            {
                result = (TOther)(object)(ushort)value.u0;
                return true;
            }
            if (typeof(TOther) == typeof(uint))
            {
                result = (TOther)(object)(uint)value.u0;
                return true;
            }
            if (typeof(TOther) == typeof(ulong))
            {
                result = (TOther)(object)value.u0;
                return true;
            }
            if (typeof(TOther) == typeof(UInt128))
            {
                result = (TOther)(object)(new UInt128(value.u1, value.u0));
                return true;
            }
            if (typeof(TOther) == typeof(nuint))
            {
                result = (TOther)(object)(nuint)value.u0;
                return true;
            }
            if (typeof(TOther) == typeof(sbyte))
            {
                result = (TOther)(object)(sbyte)value.u0;
                return true;
            }
            if (typeof(TOther) == typeof(short))
            {
                result = (TOther)(object)(short)value.u0;
                return true;
            }
            if (typeof(TOther) == typeof(int))
            {
                result = (TOther)(object)(int)value.u0;
                return true;
            }
            if (typeof(TOther) == typeof(long))
            {
                result = (TOther)(object)(long)value.u0;
                return true;
            }
            if (typeof(TOther) == typeof(Int128))
            {
                result = (TOther)(object)(new Int128(value.u1, value.u0));
                return true;
            }
            if (typeof(TOther) == typeof(nint))
            {
                result = (TOther)(object)(nint)value.u0;
                return true;
            }
            if (typeof(TOther) == typeof(Half))
            {
                result = (TOther)(object)(Half)(double)value;
                return true;
            }
            if (typeof(TOther) == typeof(float))
            {
                result = (TOther)(object)(float)(double)value;
                return true;
            }
            if (typeof(TOther) == typeof(double))
            {
                result = (TOther)(object)(double)value;
                return true;
            }
            if (typeof(TOther) == typeof(decimal))
            {
                result = (TOther)(object)(decimal)value;
                return true;
            }
            if (typeof(TOther) == typeof(BigInteger))
            {
                result = (TOther)(object)(BigInteger)value;
                return true;
            }

            result = default;
            return false;
        }

        #endregion

        #region INumber<UInt256> Implementation

        /// <inheritdoc />
        public static UInt256 Clamp(UInt256 value, UInt256 min, UInt256 max)
        {
            if (min > max)
                ThrowMinMaxException(min, max);
            if (value < min)
                return min;
            if (value > max)
                return max;
            return value;
        }

        [DoesNotReturn]
        private static void ThrowMinMaxException(UInt256 min, UInt256 max)
            => throw new ArgumentException($"'{min}' cannot be greater than '{max}'.");

        /// <inheritdoc />
        public static UInt256 CopySign(UInt256 value, UInt256 sign) => value;

        /// <inheritdoc />
        public static int Sign(UInt256 value) => value.IsZero ? 0 : 1;

        #endregion

        #region IComparisonOperators<UInt256, UInt256, bool> Implementation

        // Already implemented via existing operators

        #endregion

        #region IModulusOperators<UInt256, UInt256, UInt256> Implementation

        /// <inheritdoc />
        public static UInt256 operator %(in UInt256 left, in UInt256 right)
        {
            Mod(in left, in right, out UInt256 result);
            return result;
        }

        /// <inheritdoc />
        public static UInt256 operator %(UInt256 left, UInt256 right)
        {
            Mod(in left, in right, out UInt256 result);
            return result;
        }

        #endregion

        #region IDecrementOperators<UInt256> Implementation

        /// <inheritdoc />
        public static UInt256 operator --(in UInt256 value)
        {
            Subtract(in value, One, out UInt256 result);
            return result;
        }

        /// <inheritdoc />
        public static UInt256 operator --(UInt256 value)
        {
            Subtract(in value, One, out UInt256 result);
            return result;
        }

        #endregion

        #region IUnaryPlusOperators<UInt256, UInt256> Implementation

        /// <inheritdoc />
        public static UInt256 operator +(UInt256 value) => value;

        #endregion

        #region IUnaryNegationOperators<UInt256, UInt256> Implementation

        /// <inheritdoc />
        public static UInt256 operator -(UInt256 value) => Negate(in value);

        #endregion

        #region IBinaryInteger<UInt256> Implementation

        /// <inheritdoc />
        public static (UInt256 Quotient, UInt256 Remainder) DivRem(UInt256 left, UInt256 right)
        {
            Divide(in left, in right, out UInt256 quotient);
            Mod(in left, in right, out UInt256 remainder);
            return (quotient, remainder);
        }

        /// <inheritdoc />
        public static UInt256 LeadingZeroCount(UInt256 value)
        {
            if (value.u3 != 0) return (ulong)BitOperations.LeadingZeroCount(value.u3);
            if (value.u2 != 0) return (ulong)(64 + BitOperations.LeadingZeroCount(value.u2));
            if (value.u1 != 0) return (ulong)(128 + BitOperations.LeadingZeroCount(value.u1));
            return (ulong)(192 + BitOperations.LeadingZeroCount(value.u0));
        }

        /// <inheritdoc />
        public static UInt256 PopCount(UInt256 value) =>
            (ulong)(BitOperations.PopCount(value.u0) +
                   BitOperations.PopCount(value.u1) +
                   BitOperations.PopCount(value.u2) +
                   BitOperations.PopCount(value.u3));

        /// <inheritdoc />
        public static UInt256 TrailingZeroCount(UInt256 value)
        {
            if (value.u0 != 0) return (ulong)BitOperations.TrailingZeroCount(value.u0);
            if (value.u1 != 0) return (ulong)(64 + BitOperations.TrailingZeroCount(value.u1));
            if (value.u2 != 0) return (ulong)(128 + BitOperations.TrailingZeroCount(value.u2));
            if (value.u3 != 0) return (ulong)(192 + BitOperations.TrailingZeroCount(value.u3));
            return 256ul;
        }

        /// <inheritdoc />
        public static bool TryReadBigEndian(ReadOnlySpan<byte> source, bool isUnsigned, out UInt256 value)
        {
            if (source.Length < 32)
            {
                value = default;
                return false;
            }

            if (!isUnsigned && (source[0] & 0x80) != 0)
            {
                value = default;
                return false;
            }

            value = new UInt256(source[..32], isBigEndian: true);
            return true;
        }

        /// <inheritdoc />
        public static bool TryReadLittleEndian(ReadOnlySpan<byte> source, bool isUnsigned, out UInt256 value)
        {
            if (source.Length < 32)
            {
                value = default;
                return false;
            }

            if (!isUnsigned && (source[31] & 0x80) != 0)
            {
                value = default;
                return false;
            }

            value = new UInt256(source[..32], isBigEndian: false);
            return true;
        }

        /// <inheritdoc />
        public int GetByteCount() => 32;

        /// <inheritdoc />
        public int GetShortestBitLength() => BitLen;

        /// <inheritdoc />
        public bool TryWriteBigEndian(Span<byte> destination, out int bytesWritten)
        {
            if (destination.Length < 32)
            {
                bytesWritten = 0;
                return false;
            }

            ToBigEndian(destination[..32]);
            bytesWritten = 32;
            return true;
        }

        /// <inheritdoc />
        public bool TryWriteLittleEndian(Span<byte> destination, out int bytesWritten)
        {
            if (destination.Length < 32)
            {
                bytesWritten = 0;
                return false;
            }

            ToLittleEndian(destination[..32]);
            bytesWritten = 32;
            return true;
        }

        /// <inheritdoc />
        static UInt256 IBinaryInteger<UInt256>.RotateLeft(UInt256 value, int rotateAmount)
        {
            rotateAmount &= 255;
            if (rotateAmount == 0) return value;
            Lsh(in value, rotateAmount, out UInt256 left);
            Rsh(in value, 256 - rotateAmount, out UInt256 right);
            return left | right;
        }

        /// <inheritdoc />
        static UInt256 IBinaryInteger<UInt256>.RotateRight(UInt256 value, int rotateAmount)
        {
            rotateAmount &= 255;
            if (rotateAmount == 0) return value;
            Rsh(in value, rotateAmount, out UInt256 right);
            Lsh(in value, 256 - rotateAmount, out UInt256 left);
            return right | left;
        }

        #endregion

        #region IBinaryNumber<UInt256> Implementation

        /// <inheritdoc />
        static bool IBinaryNumber<UInt256>.IsPow2(UInt256 value)
        {
            int popCount = BitOperations.PopCount(value.u0) +
                          BitOperations.PopCount(value.u1) +
                          BitOperations.PopCount(value.u2) +
                          BitOperations.PopCount(value.u3);
            return popCount == 1;
        }

        /// <inheritdoc />
        static UInt256 IBinaryNumber<UInt256>.Log2(UInt256 value)
        {
            if (value.IsZero) throw new ArgumentException("Cannot compute Log2 of zero");
            return (ulong)(255 - (int)(ulong)LeadingZeroCount(value));
        }

        #endregion

        #region IBitwiseOperators<UInt256, UInt256, UInt256> Implementation

        // Already implemented via existing operators (|, &, ^, ~)

        #endregion

        #region IShiftOperators<UInt256, int, UInt256> Implementation

        /// <inheritdoc />
        public static UInt256 operator >>>(UInt256 value, int shiftAmount)
        {
            Rsh(in value, shiftAmount, out UInt256 result);
            return result;
        }

        #endregion

        #region ISpanFormattable Implementation

        /// <inheritdoc />
        public bool TryFormat(Span<char> destination, out int charsWritten, ReadOnlySpan<char> format, IFormatProvider? provider)
        {
            var bigInt = (BigInteger)this;
            return bigInt.TryFormat(destination, out charsWritten, format, provider);
        }

        /// <inheritdoc />
        public string ToString(string? format, IFormatProvider? formatProvider)
            => ((BigInteger)this).ToString(format, formatProvider);

        #endregion

        #region IMinMaxValue<UInt256> Implementation

        /// <inheritdoc />
        static UInt256 IMinMaxValue<UInt256>.MinValue => MinValue;

        /// <inheritdoc />
        static UInt256 IMinMaxValue<UInt256>.MaxValue => MaxValue;

        #endregion
    }
}
