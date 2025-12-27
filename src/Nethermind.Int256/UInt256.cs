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
#pragma warning disable SYSLIB5004 // DivRem is [Experimental] as of net10
    [StructLayout(LayoutKind.Explicit)]
    public readonly partial struct UInt256 : IEquatable<UInt256>, IComparable, IComparable<UInt256>, IInteger<UInt256>, IConvertible
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

        /// <summary>
        /// Adds two <see cref="UInt256"/> values and returns the wrapped 256-bit result.
        /// </summary>
        /// <remarks>
        /// Stores the low 256 bits of <c>a + b</c> in <paramref name="res"/>.
        /// Overflow (carry out of the most-significant bit) is ignored - the result wraps modulo <c>2^256</c>.
        /// Use <see cref="AddOverflow(in UInt256, in UInt256, out UInt256)"/> to detect overflow.
        /// </remarks>
        /// <param name="a">The first 256-bit addend.</param>
        /// <param name="b">The second 256-bit addend.</param>
        /// <param name="res">On return, contains <c>(a + b) mod 2^256</c>.</param>
        public static void Add(in UInt256 a, in UInt256 b, out UInt256 res)
            => AddOverflow(in a, in b, out res);

        /// <summary>
        /// Adds two <see cref="UInt256"/> values and reports whether the addition overflowed.
        /// </summary>
        /// <remarks>
        /// Computes the full 256-bit sum of <paramref name="a"/> and <paramref name="b"/> and stores the low 256 bits in
        /// <paramref name="res"/>. The return value indicates whether the true mathematical sum exceeded the range
        /// <c>[0, 2^256 - 1]</c>.
        /// </remarks>
        /// <param name="a">The first 256-bit addend.</param>
        /// <param name="b">The second 256-bit addend.</param>
        /// <param name="res">
        /// On return, contains the low 256 bits of <c>a + b</c>.
        /// </param>
        /// <returns>
        /// <see langword="true"/> if <c>a + b</c> overflowed (carry out of the most-significant bit); otherwise <see langword="false"/>.
        /// </returns>
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
            Vector256<ulong> cascadedCarries = Unsafe.Add(ref Unsafe.As<byte, Vector256<ulong>>(ref MemoryMarshal.GetReference(BroadcastLookup)), cascade);

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
            Vector256<ulong> cascadedCarries = Unsafe.Add(ref Unsafe.As<byte, Vector256<ulong>>(ref MemoryMarshal.GetReference(BroadcastLookup)), cascade);

            // Mark res as initialized so we can use it as left side of ref assignment
            Unsafe.SkipInit(out res);
            // Add the cascadedCarries to the result
            Unsafe.As<UInt256, Vector256<ulong>>(ref res) = Vector256.Add(result, cascadedCarries);

            return (carry & 0b1_0000) != 0;
        }

        /// <summary>
        /// Adds this value and <paramref name="a"/> and returns the wrapped 256-bit result.
        /// </summary>
        /// <remarks>
        /// Stores the low 256 bits of <c>this + a</c> in <paramref name="res"/>.
        /// Overflow is ignored - the result wraps modulo <c>2^256</c>.
        /// Use <see cref="AddOverflow(in UInt256, in UInt256, out UInt256)"/> to detect overflow.
        /// </remarks>
        /// <param name="a">The other 256-bit addend.</param>
        /// <param name="res">On return, contains <c>(this + a) mod 2^256</c>.</param>
        public void Add(in UInt256 a, out UInt256 res) => AddOverflow(this, a, out res);

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static void AddWithCarry(ulong x, ulong y, ref ulong carry, out ulong sum)
        {
            sum = x + y + carry;
            // both msb bits are 1 or one of them is 1 and we had carry from lower bits
            carry = ((x & y) | ((x | y) & (~sum))) >> 63;
        }

        /// <summary>
        /// Computes the modular sum of two 256-bit unsigned integers.
        /// </summary>
        /// <remarks>
        /// Sets <paramref name="res"/> to <c>(x + y) mod m</c>.
        /// If <paramref name="m"/> is zero, <paramref name="res"/> is set to zero.
        /// This behaviour intentionally differs from <see cref="System.Numerics.BigInteger"/>-style APIs.
        /// If a <see cref="System.DivideByZeroException"/> is required for a zero modulus, the caller must pre-check
        /// <paramref name="m"/> and throw before calling this method.
        /// </remarks>
        /// <param name="x">The first 256-bit addend.</param>
        /// <param name="y">The second 256-bit addend.</param>
        /// <param name="m">The modulus. If zero, the result is defined to be zero.</param>
        /// <param name="res">On return, contains the value of <c>(x + y) mod m</c>, or zero when <paramref name="m"/> is zero.</param>
        [SkipLocalsInit]
        public static void AddMod(in UInt256 x, in UInt256 y, in UInt256 m, out UInt256 res)
        {
            if (m.IsZero || m.IsOne)
            {
                res = default;
                return;
            }

            // Compute 257-bit sum S = x + y as 5 limbs (s0..s3, s4=carry)
            bool overflow = AddOverflow(in x, in y, out UInt256 sum);
            ulong s4 = !overflow ? 0UL : 1UL;

            if (m.IsUint64)
            {
                // If modulus fits in 64 bits, do direct remainder of the 5-limb value.
                if (X86Base.X64.IsSupported)
                {
                    RemSum257ByMod64BitsX86Base(in sum, s4, m.u0, out res);
                }
                else
                {
                    RemSum257ByMod64Bits(in sum, s4, m.u0, out res);
                }
            }
            else if (LessThanBoth(in x, in y, in m))
            {
                // Fast path: if x < m and y < m then S < 2m, so one subtract is enough (carry-aware).
                // (Branchy compare is fine - the fallback is much more expensive anyway.)
                ReduceSumAssumingLT2m(in sum, s4, in m, out res);
            }
            else if (!overflow)
            {
                // No overflow - sum is the exact x+y, so normal mod is correct.
                Mod(in sum, in m, out res);
            }
            else if (m.u3 != 0)
            {
                // reduce the 257-bit sum by the 256 bit mod: res = S % m256
                RemSum257ByMod256Bits(in sum, s4, in m, out res);
            }
            else if (m.u2 != 0)
            {
                // reduce the 257-bit sum by the 256 bit mod: res = S % m192
                RemSum257ByMod192Bits(in sum, s4, in m, out res);
            }
            else
            {
                // reduce the 257-bit sum by the 256 bit mod: res = S % m128
                RemSum257ByMod128Bits(in sum, s4, in m, out res);
            }
        }

        // ----------------------------
        // Fast reduction when S < 2m (eg x<m,y<m).
        // Uses carry-aware single subtract.
        // ----------------------------
        [SkipLocalsInit]
        [MethodImpl(MethodImplOptions.NoInlining)]
        private static void ReduceSumAssumingLT2m(in UInt256 sum, ulong carry, in UInt256 m, out UInt256 res)
        {
            // diff = sum - m
            ulong borrow = !SubtractUnderflow(in sum, in m, out UInt256 d) ? 0UL : 1UL;

            // Need subtract if (carry==1) || (sum>=m)
            // sum>=m <=> borrow==0
            ulong needSub = carry | (borrow ^ 1UL);
            ulong mask = 0UL - needSub;

            if (mask == 0)
            {
                res = sum;
            }
            else if (mask == ulong.MaxValue)
            {
                res = d;
            }
            else if (Vector256.IsHardwareAccelerated)
            {
                Vector256<ulong> dV = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in d));
                Vector256<ulong> sumV = Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in sum));
                Vector256<ulong> maskV = Vector256.Create(mask);

                Vector256<ulong> resultV = Vector256.ConditionalSelect(dV, sumV, maskV);

                Unsafe.SkipInit(out res);
                Unsafe.As<UInt256, Vector256<ulong>>(ref res) = resultV;
            }
            else
            {
                UInt256 mask256 = Create(mask, mask, mask, mask);
                res = (d & mask256) | (sum & ~mask256);
            }
        }

        // ----------------------------
        // Remainder of 5-limb value by 64-bit modulus (fast, fixes your test).
        // Computes ((a4..a0 base 2^64) % d).
        // ----------------------------
        [SkipLocalsInit]
        [MethodImpl(MethodImplOptions.NoInlining)]
        private static void RemSum257ByMod64Bits(in UInt256 a, ulong a4, ulong d, out UInt256 rem)
        {
            Debug.Assert(d != 0);
            Debug.Assert(a4 <= 1);

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

            rem = default;
            Unsafe.AsRef(in rem.u0) = (s == 0) ? r : (r >> s);
        }

        [SkipLocalsInit]
        [MethodImpl(MethodImplOptions.NoInlining)]
        private static void RemSum257ByMod64BitsX86Base(in UInt256 a, ulong a4, ulong d, out UInt256 rem)
        {
            Debug.Assert(d != 0);
            Debug.Assert(a4 <= 1);
            // Pull limbs up-front to encourage register residency and avoid repeated loads.
            // (Does not change semantics - just helps the JIT and OoO core.)
            ulong u0 = a.u0;
            ulong u1 = a.u1;
            ulong u2 = a.u2;
            ulong u3 = a.u3;

            // Treat the top as a single 128-bit chunk (a4:u3) and take its remainder in ONE DivRem.
            // This is valid as long as a4 < d. For a carry limb (0/1) and d>1, that's guaranteed.
            ulong r = X86Base.X64.DivRem(u3, a4, d).Remainder;
            r = X86Base.X64.DivRem(u2, r, d).Remainder;
            r = X86Base.X64.DivRem(u1, r, d).Remainder;
            r = X86Base.X64.DivRem(u0, r, d).Remainder;

            rem = default;
            Unsafe.AsRef(in rem.u0) = r;
        }
        // ----------------------------
        // General remainder: (257-bit sum) % m, where sum is 5 limbs and m is up to 4 limbs.
        // Uses Knuth D specialised, operating on a 6-limb u (top limb is 0).
        // ----------------------------
        [SkipLocalsInit]
        [MethodImpl(MethodImplOptions.NoInlining)]
        private static void RemSum257ByMod128Bits(in UInt256 a, ulong a4, in UInt256 m, out UInt256 rem)
        {
            Debug.Assert(m.u3 == 0 && m.u2 == 0 && m.u1 != 0);
            Debug.Assert(a4 <= 1);
            // Normalise divisor
            ulong vHi = m.u1;
            int sh = BitOperations.LeadingZeroCount(vHi);

            UInt256 v = ShiftLeftSmall(in m, sh);

            ulong vnHi = v.u1;
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
            // m = 5-n = 3, j = 3..0
            // Variant B style: load u1/u2 once. Delay u0 until after quotient estimate.
            ulong u6 = u4;
            ulong u7 = u5;

            ulong qhat;
            ulong rhat;
            bool rcarry;

            // Single shared out-home for everything.
            ulong lo;

            if (u7 == v.u1)
            {
                qhat = ulong.MaxValue;
                rhat = u6 + v.u1;
                rcarry = rhat < u6;
            }
            else
            {
                qhat = UDivRem2By1(u7, recip, v.u1, u6, out lo);
                rhat = lo;
                rcarry = false;
            }

            ulong u8 = u3;

            // qhat*v0 once - reused for correction + subtraction
            ulong hi = Multiply64(qhat, v.u0, out lo); // hi:lo = qhat*v0

            // Correct at most twice
            if (!rcarry && (hi > rhat || (hi == rhat && lo > u8)))
            {
                qhat--;

                // (hi:lo) -= v0
                hi -= (lo < v.u0) ? 1UL : 0UL;
                lo -= v.u0;

                ulong sum = rhat + v.u1;
                rcarry = sum < rhat;
                rhat = sum;

                if (!rcarry && (hi > rhat || (hi == rhat && lo > u8)))
                {
                    qhat--;

                    hi -= (lo < v.u0) ? 1UL : 0UL;
                    lo -= v.u0;
                }
            }

            // Subtract qhat*v from u (3 limbs)
            ulong borrow = (u8 < lo) ? 1UL : 0UL;
            u8 -= lo;

            ulong hi1 = Multiply64(qhat, v.u1, out lo);
            ulong sum1 = lo + hi;
            hi = hi1 + ((sum1 < lo) ? 1UL : 0UL);

            ulong t = u6 - sum1;
            ulong b = (u6 < sum1) ? 1UL : 0UL;
            u6 = t - borrow;
            borrow = b | ((t < borrow) ? 1UL : 0UL);

            t = u7 - hi;
            b = (u7 < hi) ? 1UL : 0UL;
            borrow = b | ((t < borrow) ? 1UL : 0UL);

            // Store raw subtraction results first (preserves aliasing behaviour)
            u3 = u8;
            u4 = u6;

            if (borrow != 0)
            {
                ulong s0 = u8 + v.u0;
                ulong c0 = (s0 < u8) ? 1UL : 0UL;

                ulong s1 = u6 + v.u1;

                ulong s1c = s1 + c0;

                // Write order matters for ref-aliasing semantics - match original: u0r, then u1r, then u2r += carry
                u3 = s0;
                u4 = s1c;
            }

            // Cold path: add-back and decrement qhat
            // Variant B style: load u1/u2 once. Delay u0 until after quotient estimate.
            ulong u9 = u3;
            ulong u10 = u4;

            ulong qhat1;
            ulong rhat1;
            bool rcarry1;

            // Single shared out-home for everything.
            ulong lo1;

            if (u10 == v.u1)
            {
                qhat1 = ulong.MaxValue;
                rhat1 = u9 + v.u1;
                rcarry1 = rhat1 < u9;
            }
            else
            {
                qhat1 = UDivRem2By1(u10, recip, v.u1, u9, out lo1);
                rhat1 = lo1;
                rcarry1 = false;
            }

            ulong u11 = u2;

            // qhat*v0 once - reused for correction + subtraction
            ulong hi2 = Multiply64(qhat1, v.u0, out lo1); // hi:lo = qhat*v0

            // Correct at most twice
            if (!rcarry1 && (hi2 > rhat1 || (hi2 == rhat1 && lo1 > u11)))
            {
                qhat1--;

                // (hi:lo) -= v0
                hi2 -= (lo1 < v.u0) ? 1UL : 0UL;
                lo1 -= v.u0;

                ulong sum2 = rhat1 + v.u1;
                rcarry1 = sum2 < rhat1;
                rhat1 = sum2;

                if (!rcarry1 && (hi2 > rhat1 || (hi2 == rhat1 && lo1 > u11)))
                {
                    qhat1--;

                    hi2 -= (lo1 < v.u0) ? 1UL : 0UL;
                    lo1 -= v.u0;
                }
            }

            // Subtract qhat*v from u (3 limbs)
            ulong borrow1 = (u11 < lo1) ? 1UL : 0UL;
            u11 -= lo1;

            ulong hi3 = Multiply64(qhat1, v.u1, out lo1);
            ulong sum3 = lo1 + hi2;
            hi2 = hi3 + ((sum3 < lo1) ? 1UL : 0UL);

            ulong t1 = u9 - sum3;
            ulong b1 = (u9 < sum3) ? 1UL : 0UL;
            u9 = t1 - borrow1;
            borrow1 = b1 | ((t1 < borrow1) ? 1UL : 0UL);

            t1 = u10 - hi2;
            b1 = (u10 < hi2) ? 1UL : 0UL;
            borrow1 = b1 | ((t1 < borrow1) ? 1UL : 0UL);

            // Store raw subtraction results first (preserves aliasing behaviour)
            u2 = u11;
            u3 = u9;

            if (borrow1 != 0)
            {
                ulong s2 = u11 + v.u0;
                ulong c3 = (s2 < u11) ? 1UL : 0UL;
                ulong s3 = u9 + v.u1;
                ulong s1C = s3 + c3;

                // Write order matters for ref-aliasing semantics - match original: u0r, then u1r, then u2r += carry
                u2 = s2;
                u3 = s1C;
            }

            // Cold path: add-back and decrement qhat
            // Variant B style: load u1/u2 once. Delay u0 until after quotient estimate.
            ulong u12 = u2;
            ulong u13 = u3;

            ulong qhat2;
            ulong rhat2;
            bool rcarry2;

            // Single shared out-home for everything.
            ulong lo2;

            if (u13 == v.u1)
            {
                qhat2 = ulong.MaxValue;
                rhat2 = u12 + v.u1;
                rcarry2 = rhat2 < u12;
            }
            else
            {
                qhat2 = UDivRem2By1(u13, recip, v.u1, u12, out lo2);
                rhat2 = lo2;
                rcarry2 = false;
            }

            ulong u14 = u1;

            // qhat*v0 once - reused for correction + subtraction
            ulong hi4 = Multiply64(qhat2, v.u0, out lo2); // hi:lo = qhat*v0

            // Correct at most twice
            if (!rcarry2 && (hi4 > rhat2 || (hi4 == rhat2 && lo2 > u14)))
            {
                qhat2--;

                // (hi:lo) -= v0
                hi4 -= (lo2 < v.u0) ? 1UL : 0UL;
                lo2 -= v.u0;

                ulong sum4 = rhat2 + v.u1;
                rcarry2 = sum4 < rhat2;
                rhat2 = sum4;

                if (!rcarry2 && (hi4 > rhat2 || (hi4 == rhat2 && lo2 > u14)))
                {
                    qhat2--;

                    hi4 -= (lo2 < v.u0) ? 1UL : 0UL;
                    lo2 -= v.u0;
                }
            }

            // Subtract qhat*v from u (3 limbs)
            ulong borrow2 = (u14 < lo2) ? 1UL : 0UL;
            u14 -= lo2;

            ulong hi5 = Multiply64(qhat2, v.u1, out lo2);
            ulong sum5 = lo2 + hi4;
            hi4 = hi5 + ((sum5 < lo2) ? 1UL : 0UL);

            ulong t2 = u12 - sum5;
            ulong b2 = (u12 < sum5) ? 1UL : 0UL;
            u12 = t2 - borrow2;
            borrow2 = b2 | ((t2 < borrow2) ? 1UL : 0UL);

            t2 = u13 - hi4;
            b2 = (u13 < hi4) ? 1UL : 0UL;
            borrow2 = b2 | ((t2 < borrow2) ? 1UL : 0UL);

            // Store raw subtraction results first (preserves aliasing behaviour)
            u1 = u14;
            u2 = u12;

            if (borrow2 != 0)
            {
                ulong s4 = u14 + v.u0;
                ulong c6 = (s4 < u14) ? 1UL : 0UL;
                ulong s5 = u12 + v.u1;
                ulong s1C1 = s5 + c6;

                // Write order matters for ref-aliasing semantics - match original: u0r, then u1r, then u2r += carry
                u1 = s4;
                u2 = s1C1;
            }

            // Cold path: add-back and decrement qhat
            // Variant B style: load u1/u2 once. Delay u0 until after quotient estimate.
            ulong u15 = u1;
            ulong u16 = u2;

            ulong qhat3;
            ulong rhat3;
            bool rcarry3;

            // Single shared out-home for everything.
            ulong lo3;

            if (u16 == v.u1)
            {
                qhat3 = ulong.MaxValue;
                rhat3 = u15 + v.u1;
                rcarry3 = rhat3 < u15;
            }
            else
            {
                qhat3 = UDivRem2By1(u16, recip, v.u1, u15, out lo3);
                rhat3 = lo3;
                rcarry3 = false;
            }

            ulong u17 = u0;

            // qhat*v0 once - reused for correction + subtraction
            ulong hi6 = Multiply64(qhat3, v.u0, out lo3); // hi:lo = qhat*v0

            // Correct at most twice
            if (!rcarry3 && (hi6 > rhat3 || (hi6 == rhat3 && lo3 > u17)))
            {
                qhat3--;

                // (hi:lo) -= v0
                hi6 -= (lo3 < v.u0) ? 1UL : 0UL;
                lo3 -= v.u0;

                ulong sum6 = rhat3 + v.u1;
                rcarry3 = sum6 < rhat3;
                rhat3 = sum6;

                if (!rcarry3 && (hi6 > rhat3 || (hi6 == rhat3 && lo3 > u17)))
                {
                    qhat3--;

                    hi6 -= (lo3 < v.u0) ? 1UL : 0UL;
                    lo3 -= v.u0;
                }
            }

            // Subtract qhat*v from u (3 limbs)
            ulong borrow3 = (u17 < lo3) ? 1UL : 0UL;
            u17 -= lo3;

            ulong hi7 = Multiply64(qhat3, v.u1, out lo3);
            ulong sum7 = lo3 + hi6;
            hi6 = hi7 + ((sum7 < lo3) ? 1UL : 0UL);

            ulong t3 = u15 - sum7;
            ulong b3 = (u15 < sum7) ? 1UL : 0UL;
            u15 = t3 - borrow3;
            borrow3 = b3 | ((t3 < borrow3) ? 1UL : 0UL);

            t3 = u16 - hi6;
            b3 = (u16 < hi6) ? 1UL : 0UL;
            borrow3 = b3 | ((t3 < borrow3) ? 1UL : 0UL);

            // Store raw subtraction results first (preserves aliasing behaviour)
            u0 = u17;
            u1 = u15;

            if (borrow3 != 0)
            {
                ulong s6 = u17 + v.u0;
                ulong c9 = (s6 < u17) ? 1UL : 0UL;
                ulong s7 = u15 + v.u1;
                ulong s1C2 = s7 + c9;

                // Write order matters for ref-aliasing semantics - match original: u0r, then u1r, then u2r += carry
                u0 = s6;
                u1 = s1C2;
            }

            // Cold path: add-back and decrement qhat

            UInt256 remN = Create(u0, u1, 0, 0);
            rem = ShiftRightSmall(remN, sh);
        }

        // ----------------------------
        // General remainder: (257-bit sum) % m, where sum is 5 limbs and m is up to 4 limbs.
        // Uses Knuth D specialised, operating on a 6-limb u (top limb is 0).
        // ----------------------------
        [SkipLocalsInit]
        [MethodImpl(MethodImplOptions.NoInlining)]
        private static void RemSum257ByMod192Bits(in UInt256 a, ulong a4, in UInt256 m, out UInt256 rem)
        {
            Debug.Assert(m.u3 == 0 && m.u2 != 0);
            Debug.Assert(a4 <= 1);
            // divisor limb count n in 3 (caller ensured m doesn't fit in 64 bits)

            // Normalise divisor
            ulong vHi = m.u2;
            int sh = BitOperations.LeadingZeroCount(vHi);

            UInt256 v = ShiftLeftSmall(in m, sh);

            ulong vnHi = v.u2;
            ulong recip = X86Base.X64.IsSupported ? 0 : Reciprocal2By1(vnHi);

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

            // m = 2, j = 2..0
            ulong qhat, rhat, rcarry;
            if (u5 == v.u2)
            {
                qhat = ulong.MaxValue;
                ulong sum = u4 + v.u2;
                rcarry = (sum < u4) ? 1UL : 0UL;
                rhat = sum;
            }
            else
            {
                if (X86Base.X64.IsSupported)
                {
                    (qhat, rhat) = X86Base.X64.DivRem(u4, u5, v.u2); // (upper:lower) = (u5:u4)
                }
                else
                {
                    qhat = UDivRem2By1(u5, recip, v.u2, u4, out rhat);
                }
                rcarry = 0;
            }

            if (rcarry == 0)
            {
                ulong pHi = Multiply64(qhat, v.u1, out ulong pLo);

                // if qhat*vNext > rhat*b + uCorr then decrement
                if (pHi > rhat || (pHi == rhat && pLo > u3))
                {
                    qhat--;

                    ulong sum1 = rhat + v.u2;
                    if (sum1 < rhat)
                        rcarry = 1;

                    rhat = sum1;
                }
            }

            if (rcarry == 0)
            {
                ulong pHi = Multiply64(qhat, v.u1, out ulong pLo);

                // if qhat*vNext > rhat*b + uCorr then decrement
                if (pHi > rhat || (pHi == rhat && pLo > u3))
                {
                    qhat--;
                }
            }

            ulong borrow1 = 0;

            ulong pHi1 = Multiply64(qhat, v.u0, out ulong pLo1);
            ulong sum2 = pLo1;
            ulong c2 = (sum2 < pLo1) ? 1UL : 0UL;
            ulong carry = pHi1 + c2;
            u2 = Sub(u2, sum2, ref borrow1);

            pHi1 = Multiply64(qhat, v.u1, out pLo1);
            sum2 = pLo1 + carry;
            c2 = (sum2 < pLo1) ? 1UL : 0UL;
            carry = pHi1 + c2;
            u3 = Sub(u3, sum2, ref borrow1);

            pHi1 = Multiply64(qhat, v.u2, out pLo1);
            sum2 = pLo1 + carry;
            c2 = (sum2 < pLo1) ? 1UL : 0UL;
            carry = pHi1 + c2;
            u4 = Sub(u4, sum2, ref borrow1);

            u5 = Sub(u5, carry, ref borrow1);
            ulong borrow = borrow1;

            if (borrow != 0)
            {
                AddBack3(ref u2, ref u3, ref u4, ref u5, v.u0, v.u1, v.u2);
            }

            ulong qhat1, rhat1, rcarry1;
            if (u4 == v.u2)
            {
                qhat1 = ulong.MaxValue;
                ulong sum3 = u3 + v.u2;
                rcarry1 = (sum3 < u3) ? 1UL : 0UL;
                rhat1 = sum3;
            }
            else
            {
                if (X86Base.X64.IsSupported)
                {
                    (qhat1, rhat1) = X86Base.X64.DivRem(u3, u4, v.u2); // (upper:lower) = (u4:u3)
                }
                else
                {
                    qhat1 = UDivRem2By1(u4, recip, v.u2, u3, out rhat1);
                }
                rcarry1 = 0;
            }

            if (rcarry1 == 0)
            {
                ulong pHi2 = Multiply64(qhat1, v.u1, out ulong pLo2);

                // if qhat*vNext > rhat*b + uCorr then decrement
                if (pHi2 > rhat1 || (pHi2 == rhat1 && pLo2 > u2))
                {
                    qhat1--;

                    ulong sum4 = rhat1 + v.u2;
                    if (sum4 < rhat1)
                        rcarry1 = 1;

                    rhat1 = sum4;
                }
            }

            if (rcarry1 == 0)
            {
                ulong pHi3 = Multiply64(qhat1, v.u1, out ulong pLo3);

                // if qhat*vNext > rhat*b + uCorr then decrement
                if (pHi3 > rhat1 || (pHi3 == rhat1 && pLo3 > u2))
                {
                    qhat1--;
                }
            }

            ulong borrow2 = 0;

            ulong pHi4 = Multiply64(qhat1, v.u0, out ulong pLo4);
            ulong sum5 = pLo4;
            ulong c3 = (sum5 < pLo4) ? 1UL : 0UL;
            ulong carry1 = pHi4 + c3;
            u1 = Sub(u1, sum5, ref borrow2);

            pHi4 = Multiply64(qhat1, v.u1, out pLo4);
            sum5 = pLo4 + carry1;
            c3 = (sum5 < pLo4) ? 1UL : 0UL;
            carry1 = pHi4 + c3;
            u2 = Sub(u2, sum5, ref borrow2);

            pHi4 = Multiply64(qhat1, v.u2, out pLo4);
            sum5 = pLo4 + carry1;
            c3 = (sum5 < pLo4) ? 1UL : 0UL;
            carry1 = pHi4 + c3;
            u3 = Sub(u3, sum5, ref borrow2);

            u4 = Sub(u4, carry1, ref borrow2);
            ulong borrow3 = borrow2;

            if (borrow3 != 0)
            {
                AddBack3(ref u1, ref u2, ref u3, ref u4, v.u0, v.u1, v.u2);
            }

            ulong qhat2, rhat2, rcarry2;
            if (u3 == v.u2)
            {
                qhat2 = ulong.MaxValue;
                ulong sum6 = u2 + v.u2;
                rcarry2 = (sum6 < u2) ? 1UL : 0UL;
                rhat2 = sum6;
            }
            else
            {
                if (X86Base.X64.IsSupported)
                {
                    (qhat2, rhat2) = X86Base.X64.DivRem(u2, u3, v.u2); // (upper:lower) = (u3:u2)
                }
                else
                {
                    qhat2 = UDivRem2By1(u3, recip, v.u2, u2, out rhat2);
                }
                rcarry2 = 0;
            }

            if (rcarry2 == 0)
            {
                ulong pHi5 = Multiply64(qhat2, v.u1, out ulong pLo5);

                // if qhat*vNext > rhat*b + uCorr then decrement
                if (pHi5 > rhat2 || (pHi5 == rhat2 && pLo5 > u1))
                {
                    qhat2--;

                    ulong sum7 = rhat2 + v.u2;
                    if (sum7 < rhat2)
                        rcarry2 = 1;

                    rhat2 = sum7;
                }
            }

            if (rcarry2 == 0)
            {
                ulong pHi6 = Multiply64(qhat2, v.u1, out ulong pLo6);

                // if qhat*vNext > rhat*b + uCorr then decrement
                if (pHi6 > rhat2 || (pHi6 == rhat2 && pLo6 > u1))
                {
                    qhat2--;
                }
            }

            ulong borrow4 = 0;

            ulong pHi7 = Multiply64(qhat2, v.u0, out ulong pLo7);
            ulong sum8 = pLo7;
            ulong c4 = (sum8 < pLo7) ? 1UL : 0UL;
            ulong carry2 = pHi7 + c4;
            u0 = Sub(u0, sum8, ref borrow4);

            pHi7 = Multiply64(qhat2, v.u1, out pLo7);
            sum8 = pLo7 + carry2;
            c4 = (sum8 < pLo7) ? 1UL : 0UL;
            carry2 = pHi7 + c4;
            u1 = Sub(u1, sum8, ref borrow4);

            pHi7 = Multiply64(qhat2, v.u2, out pLo7);
            sum8 = pLo7 + carry2;
            c4 = (sum8 < pLo7) ? 1UL : 0UL;
            carry2 = pHi7 + c4;
            u2 = Sub(u2, sum8, ref borrow4);

            u3 = Sub(u3, carry2, ref borrow4);
            ulong borrow5 = borrow4;

            if (borrow5 != 0)
            {
                AddBack3(ref u0, ref u1, ref u2, ref u3, v.u0, v.u1, v.u2);
            }

            if (sh == 0)
            {
                rem = Create(u0, u1, u2, 0);
                return;
            }

            {
                int rs = 64 - sh;
                ulong o0 = (u0 >> sh) | (u1 << rs);
                ulong o1 = (u1 >> sh) | (u2 << rs);
                ulong o2 = (u2 >> sh);
                rem = Create(o0, o1, o2, 0);
            }
        }

        // ----------------------------
        // General remainder: (257-bit sum) % m, where sum is 5 limbs and m is up to 4 limbs.
        // Uses Knuth D specialised, operating on a 6-limb u (top limb is 0).
        // ----------------------------
        [SkipLocalsInit]
        [MethodImpl(MethodImplOptions.NoInlining)]
        private static void RemSum257ByMod256Bits(in UInt256 a, ulong a4, in UInt256 m, out UInt256 rem)
        {
            Debug.Assert(m.u3 != 0);
            Debug.Assert(a4 <= 1);

            // Normalise divisor
            int sh = BitOperations.LeadingZeroCount(m.u3);
            UInt256 v = ShiftLeftSmall(in m, sh);
            UInt256 u = ShiftLeftSmall(in a, sh);

            ulong v3 = v.u3;

            ulong recip = X86Base.X64.IsSupported ? 0 : Reciprocal2By1(v3);
            // Normalise dividend: u5 is guaranteed 0 for a 257-bit input
            ulong u0 = u.u0;
            ulong u1 = u.u1;
            ulong u2 = u.u2;
            ulong u3 = u.u3;
            ulong u4 = (sh == 0) ? a4 : (a4 << sh) | (a.u3 >> (64 - sh));

            ulong v0 = v.u0;
            ulong v1 = v.u1;
            ulong v2 = v.u2;

            // High quotient digit q1 is only 0 or 1 (since u5==0, v3 has top bit set).
            // Implement as "attempt subtract V*B".
            if (u4 >= v3)
            {
                ulong b = 0;
                u1 = Sub(u1, v0, ref b);
                u2 = Sub(u2, v1, ref b);
                u3 = Sub(u3, v2, ref b);
                u4 = Sub(u4, v3, ref b);

                // If we borrowed past u4, we would have borrowed from u5 (which is 0) - so undo.
                if (b != 0)
                {
                    ulong c = 0;
                    AddWithCarry(u1, v0, ref c, out u1);
                    AddWithCarry(u2, v1, ref c, out u2);
                    AddWithCarry(u3, v2, ref c, out u3);
                    AddWithCarry(u4, v3, ref c, out u4);
                    // ignore final carry - it would go into u5
                }
            }

            // Now only one Knuth step remains (j = 0)
            ulong q0, r0, rcarry0;

            if (u4 == v3)
            {
                q0 = ulong.MaxValue;
                ulong sum = u3 + v3;
                rcarry0 = (sum < u3) ? 1UL : 0UL;
                r0 = sum;
            }
            else
            {
                if (X86Base.X64.IsSupported)
                {
                    (q0, r0) = X86Base.X64.DivRem(u3, u4, v3); // (upper:lower) = (u4:u3)
                }
                else
                {
                    q0 = UDivRem2By1(u4, recip, v3, u3, out r0);
                }

                rcarry0 = 0;
            }

            // q0 correction - only do the second check if we decremented once
            if (rcarry0 == 0)
            {
                ulong pHi = Multiply64(q0, v2, out ulong pLo);

                if (pHi > r0 || (pHi == r0 && pLo > u2))
                {
                    q0--;

                    ulong sum = r0 + v3;
                    rcarry0 = (sum < r0) ? 1UL : 0UL;
                    r0 = sum;

                    if (rcarry0 == 0)
                    {
                        pHi = Multiply64(q0, v2, out pLo);
                        if (pHi > r0 || (pHi == r0 && pLo > u2))
                            q0--;
                    }
                }
            }

            ulong borrow = SubMul4(ref u0, ref u1, ref u2, ref u3, ref u4, v0, v1, v2, v3, q0);
            if (borrow != 0)
            {
                AddBack4(ref u0, ref u1, ref u2, ref u3, ref u4, v0, v1, v2, v3);
            }

            UInt256 remN = Create(u0, u1, u2, u3);
            rem = ShiftRightSmall(in remN, sh);
        }
        /// <summary>
        /// Computes the modular sum of this value and <paramref name="a"/>.
        /// </summary>
        /// <remarks>
        /// Sets <paramref name="res"/> to <c>(this + a) mod m</c>.
        /// If <paramref name="m"/> is zero, <paramref name="res"/> is set to zero.
        /// If a <see cref="System.DivideByZeroException"/> is required for a zero modulus, the caller must pre-check
        /// <paramref name="m"/> and throw before calling this method.
        /// </remarks>
        /// <param name="a">The other 256-bit addend.</param>
        /// <param name="m">The modulus. If zero, the result is defined to be zero.</param>
        /// <param name="res">On return, contains the value of <c>(this + a) mod m</c>, or zero when <paramref name="m"/> is zero.</param>
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

        /// <summary>
        /// Computes the remainder of dividing one <see cref="UInt256"/> value by another.
        /// </summary>
        /// <remarks>
        /// Sets <paramref name="res"/> to <c>x % y</c> when <paramref name="y"/> is non-zero.
        /// If <paramref name="y"/> is zero, <paramref name="res"/> is set to zero.
        /// This behaviour intentionally differs from <see cref="System.Numerics.BigInteger"/>-style APIs.
        /// If a <see cref="System.DivideByZeroException"/> is required for a zero divisor, the caller must pre-check
        /// <paramref name="y"/> and throw before calling this method.
        /// </remarks>
        /// <param name="x">The dividend.</param>
        /// <param name="y">The divisor. If zero, the result is defined to be zero.</param>
        /// <param name="res">On return, contains <c>x % y</c>, or zero when <paramref name="y"/> is zero.</param>
        [SkipLocalsInit]
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

            ModFull(x, y, out res);
        }

        [SkipLocalsInit]
        [MethodImpl(MethodImplOptions.NoInlining)]
        private static void ModFull(in UInt256 x, in UInt256 y, out UInt256 res)
        {
            DivideImpl(x, y, out _, out res);
        }

        /// <summary>
        /// Computes the remainder of dividing this value by <paramref name="m"/>.
        /// </summary>
        /// <remarks>
        /// Sets <paramref name="res"/> to <c>this % m</c> when <paramref name="m"/> is non-zero.
        /// If <paramref name="m"/> is zero, <paramref name="res"/> is set to zero.
        /// If a <see cref="System.DivideByZeroException"/> is required for a zero divisor, the caller must pre-check
        /// <paramref name="m"/> and throw before calling this method.
        /// </remarks>
        /// <param name="m">The divisor. If zero, the result is defined to be zero.</param>
        /// <param name="res">On return, contains <c>this % m</c>, or zero when <paramref name="m"/> is zero.</param>
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

            ulong rem0, rem1 = 0, rem2 = 0, rem3 = 0;
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

                ulong qhat;
                if (u2 >= dh)
                {
                    qhat = ~((ulong)0);
                    // TODO: Add "qhat one to big" adjustment (not needed for correctness, but helps avoiding "add back" case).
                }
                else
                {
                    qhat = UDivRem2By1(u2, reciprocal, dh, u1, out var rhat);
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
                Unsafe.Add(ref quot, j) = UDivRem2By1(rem, reciprocal, d, u[j], out rem);
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

        // Preconditions:
        // - d normalised (msb set)
        // - u1 < d
        [SkipLocalsInit]
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static ulong UDivRem2By1(ulong uh, ulong reciprocal, ulong d, ulong ul, out ulong rem)
        {
            ulong hi = Multiply64(reciprocal, uh, out ulong low);

            low += ul;
            ulong q = hi + uh + 1UL;
            if (low < ul)
            {
                q++;
            }

            ulong r1 = ul - (q * d);

            if (r1 > low) { q--; r1 += d; }
            if (r1 >= d) { q++; r1 -= d; }

            rem = r1;
            return q;
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
                Vector256<ulong> cascadedBorrows = Unsafe.Add(ref Unsafe.As<byte, Vector256<ulong>>(ref MemoryMarshal.GetReference(BroadcastLookup)), cascade);

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
            if (y.IsOne)
            {
                res = x;
                return;
            }
            if (x.IsOne)
            {
                res = y;
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

        /// <summary>
        /// Sets <paramref name="res"/> to the integer quotient of <paramref name="x"/> divided by <paramref name="y"/>.
        /// </summary>
        /// <remarks>
        /// This performs an unsigned integer division with truncation toward zero (floor for unsigned values).
        /// <para>
        /// Special cases:
        /// <list type="bullet">
        ///   <item><description>If <paramref name="y"/> is zero, <paramref name="res"/> is set to zero.</description></item>
        ///   <item><description>If <paramref name="x"/> is less than <paramref name="y"/>, <paramref name="res"/> is set to zero.</description></item>
        ///   <item><description>If <paramref name="x"/> equals <paramref name="y"/>, <paramref name="res"/> is set to one.</description></item>
        /// </list>
        /// </para>
        /// <para>
        /// This method does not throw on divide-by-zero. If a <see cref="DivideByZeroException"/> (or equivalent)
        /// is required, it must be enforced by the caller before invoking this method.
        /// </para>
        /// </remarks>
        /// <param name="x">The dividend.</param>
        /// <param name="y">The divisor.</param>
        /// <param name="res">On return, contains the quotient <c>x / y</c>.</param>
        [SkipLocalsInit]
        public static void Divide(in UInt256 x, in UInt256 y, out UInt256 res)
        {
            // Handle y == 0 and y == 1 cheaply
            //
            // y0 is the low limb.
            // We structure this to keep y1/y2/y3 lifetimes short - do not load them unless y0 is 0 or 1.
            //
            // (y0 & ~1) == 0 is equivalent to (y0 == 0 || y0 == 1) but compiles well and keeps the branch compact.
            ulong y0 = y.u0;
            if ((y0 & ~1UL) == 0)
            {
                // yHi is the OR of the upper limbs.
                // - y == 0  iff y0 == 0 and yHi == 0
                // - y == 1  iff y0 == 1 and yHi == 0
                //
                // Computing yHi here (and only here) avoids keeping y1/y2/y3 live across the entire function,
                // which would force the JIT to use callee-saved regs (rbx/rsi/rdi/rbp/r14/r15) and emit pushes.
                ulong yHi = y.u1 | y.u2 | y.u3;
                if (yHi == 0)
                {
                    // Exact: if y == 0 -> quotient is 0 (we return default)
                    //        if y == 1 -> quotient is x (copy x)
                    //
                    // Note: written as a conditional expression for brevity.
                    res = (y0 == 0) ? default : x;
                    return;
                }
                // else y is 2^64 or larger - not a special-case, continue.
            }

            // Decide "u64 fast path" vs "wide path" with minimal register pressure
            //
            // Key idea: do not read x1 unless we already know x3|x2 == 0.
            // If we pull x1/x2/x3 all live at once and then also pull y2/y3 for the wide compare, we run out of
            // volatile regs (Windows x64 has rcx/rdx/r8 pinned for args; leaves rax/r9/r10/r11 as the main free ones).
            // That is exactly how you get extra pushes.
            ulong x3 = x.u3;
            ulong x2 = x.u2;

            // x fits in 64 bits iff x1==x2==x3==0.
            // We stage it:
            // - first check x3|x2 (cheap and already needed for wide compare)
            // - only then touch x1, so x1 does not become live on the wide path.
            if ((x3 | x2) == 0 && x.u1 == 0)
            {
                // u64 path
                //
                // Here x < 2^64. If y has any high limbs set, then y >= 2^64 > x, so quotient is 0.
                // This avoids any 256-bit division work and avoids the "unsafe" x.u0/y.u0 divide when y doesn't fit.
                if ((y.u1 | y.u2 | y.u3) != 0)
                {
                    res = default;
                    return;
                }

                // Now both x and y fit in 64 bits, and y != 0 (we already handled y==0 earlier).
                ulong x0 = x.u0;
                ulong yy0 = y.u0; // reload y0 in this scope so we do not keep the earlier y0 live unnecessarily

                // If y > x then quotient is 0.
                if (yy0 > x0) { res = default; return; }

                // If x == y then quotient is 1.
                if (yy0 == x0) { res = Create(1, 0, 0, 0); return; }

                // Normal 64-bit division.
                res = Create(x0 / yy0, 0, 0, 0);
                return;
            }

            // Wide compare gate - decide between {0, 1} and "real division"
            //
            // We only call DivideFull when x > y.
            // When x < y, quotient is 0.
            // When x == y, quotient is 1.
            //
            // Implemented as lexicographic compare from MS limb to LS limb:
            // (x3,x2,x1,x0) vs (y3,y2,y1,y0).
            //
            // Staged preloads:
            // - stage A loads y3 and y2 only (paired with x3/x2 already loaded)
            // - stage B loads x1/y1 and x0/y0 only if stage A says they are equal
            //
            // This keeps at most ~4 scalar values live at any time, helping the JIT stay in volatile regs and
            // avoid callee-saved spills - while still giving the CPU some independent loads to overlap.
            ulong y3 = y.u3;
            if (x3 < y3) { res = default; return; }                 // x < y
            if (x3 > y3) { DivideFull(in x, in y, out res); return; } // x > y -> real division

            ulong y2 = y.u2;
            if (x2 < y2) { res = default; return; }                 // x < y
            if (x2 > y2) { DivideFull(in x, in y, out res); return; } // x > y -> real division

            // Stage B (only reached when x3==y3 and x2==y2)
            ulong x1 = x.u1;
            ulong y1 = y.u1;
            if (x1 < y1) { res = default; return; }                 // x < y
            if (x1 > y1) { DivideFull(in x, in y, out res); return; } // x > y -> real division

            ulong x0b = x.u0;
            ulong y0b = y.u0;
            if (x0b < y0b) { res = default; return; }               // x < y
            if (x0b == y0b) { res = Create(1, 0, 0, 0); return; }   // x == y -> quotient 1

            // Remaining case: x > y.
            DivideFull(in x, in y, out res);
        }

        [SkipLocalsInit]
        // Slow path is isolated so the wrapper can tailcall it and avoid stack temps like "out _ remainder".
        [MethodImpl(MethodImplOptions.NoInlining)]
        private static void DivideFull(in UInt256 x, in UInt256 y, out UInt256 res)
        {
            // Full 256-bit division. We discard the remainder via out _.
            // Keeping this in a separate method prevents the wrapper from needing
            // a 32-byte stack slot for the remainder, which would otherwise force
            // a larger frame and extra stores even on fast exits.
            DivideImpl(x, y, out res, out _);
        }

        /// <summary>
        /// Divides this value by <paramref name="a"/> and returns the integer quotient.
        /// </summary>
        /// <remarks>
        /// Sets <paramref name="res"/> to <c>this / a</c> using unsigned integer division.
        /// If <paramref name="a"/> is zero, the result depends on the semantics of the underlying static
        /// <see cref="Divide(in UInt256, in UInt256, out UInt256)"/> implementation.
        /// If a <see cref="System.DivideByZeroException"/> is required for a zero divisor, the caller must pre-check
        /// <paramref name="a"/> and throw before calling this method.
        /// </remarks>
        /// <param name="a">The divisor.</param>
        /// <param name="res">On return, contains the quotient <c>this / a</c>.</param>
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
                z1 = res.u1;
                z2 = res.u2;
                z3 = res.u3;
                n -= 192;
                goto sh192;
            }
            else if (n > 128)
            {
                x.Rsh128(out res);
                z2 = res.u2;
                z3 = res.u3;
                n -= 128;
                goto sh128;
            }
            else if (n > 64)
            {
                x.Rsh64(out res);
                z3 = res.u3;
                n -= 64;
                goto sh64;
            }
            else
            {
                res = x;
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

            ulong vRecip = X86Base.X64.IsSupported ? 0 : Reciprocal2By1(v2n);
            ulong qhat, rhat, rcarry;
            if (u4d == v2n)
            {
                qhat = ulong.MaxValue;
                ulong sum = u3d + v2n;
                rcarry = (sum < u3d) ? 1UL : 0UL;
                rhat = sum;
            }
            else
            {
                if (X86Base.X64.IsSupported)
                {
                    (qhat, rhat) = X86Base.X64.DivRem(u3d, u4d, v2n); // (upper:lower) = (u4d:u3d)
                }
                else
                {
                    qhat = UDivRem2By1(u4d, vRecip, v2n, u3d, out rhat);
                }
                rcarry = 0;
            }

            if (rcarry == 0)
            {
                ulong pHi = Multiply64(qhat, v1n, out ulong pLo);

                // if qhat*vNext > rhat*b + uCorr then decrement
                if (pHi > rhat || (pHi == rhat && pLo > u2d))
                {
                    qhat--;

                    ulong sum1 = rhat + v2n;
                    if (sum1 < rhat)
                    {
                        rcarry = 1;
                    }

                    rhat = sum1;
                }
            }

            if (rcarry == 0)
            {
                ulong pHi = Multiply64(qhat, v1n, out ulong pLo);

                // if qhat*vNext > rhat*b + uCorr then decrement
                if (pHi > rhat || (pHi == rhat && pLo > u2d))
                {
                    qhat--;
                }
            }

            ulong borrow1 = 0;

            ulong pHi1 = Multiply64(qhat, v0, out ulong pLo1);
            u1d = Sub(u1d, pLo1, ref borrow1);

            ulong carry = pHi1;
            pHi1 = Multiply64(qhat, v1n, out pLo1);
            ulong sum2 = pLo1 + carry;
            ulong c2 = (sum2 < pLo1) ? 1UL : 0UL;
            carry = pHi1 + c2;
            u2d = Sub(u2d, sum2, ref borrow1);

            pHi1 = Multiply64(qhat, v2n, out pLo1);
            sum2 = pLo1 + carry;
            c2 = (sum2 < pLo1) ? 1UL : 0UL;
            carry = pHi1 + c2;
            u3d = Sub(u3d, sum2, ref borrow1);

            u4d = Sub(u4d, carry, ref borrow1);
            ulong borrow = borrow1;

            if (borrow != 0)
            {
                AddBack3(ref u1d, ref u2d, ref u3d, ref u4d, v0, v1n, v2n);
                qhat--;
            }

            ulong q1 = qhat;
            ulong qhat1, rhat1, rcarry1;
            if (u3d == v2n)
            {
                qhat1 = ulong.MaxValue;
                ulong sum3 = u2d + v2n;
                rcarry1 = (sum3 < u2d) ? 1UL : 0UL;
                rhat1 = sum3;
            }
            else
            {
                if (X86Base.X64.IsSupported)
                {
                    (qhat1, rhat1) = X86Base.X64.DivRem(u2d, u3d, v2n); // (upper:lower) = (u3d:u2d)
                }
                else
                {
                    qhat1 = UDivRem2By1(u3d, vRecip, v2n, u2d, out rhat1);
                }
                rcarry1 = 0;
            }

            if (rcarry1 == 0)
            {
                ulong pHi2 = Multiply64(qhat1, v1n, out ulong pLo2);

                // if qhat*vNext > rhat*b + uCorr then decrement
                if (pHi2 > rhat1 || (pHi2 == rhat1 && pLo2 > u1d))
                {
                    qhat1--;

                    ulong sum4 = rhat1 + v2n;
                    if (sum4 < rhat1)
                    {
                        rcarry1 = 1;
                    }

                    rhat1 = sum4;
                }
            }

            if (rcarry1 == 0)
            {
                ulong pHi3 = Multiply64(qhat1, v1n, out ulong pLo3);

                // if qhat*vNext > rhat*b + uCorr then decrement
                if (pHi3 > rhat1 || (pHi3 == rhat1 && pLo3 > u1d))
                {
                    qhat1--;
                }
            }

            ulong borrow2 = 0;

            ulong pHi4 = Multiply64(qhat1, v0, out ulong pLo4);
            ulong sum6 = pLo4;
            ulong c3 = (sum6 < pLo4) ? 1UL : 0UL;
            ulong carry1 = pHi4 + c3;
            u0n2 = Sub(u0n2, sum6, ref borrow2);

            pHi4 = Multiply64(qhat1, v1n, out pLo4);
            sum6 = pLo4 + carry1;
            c3 = (sum6 < pLo4) ? 1UL : 0UL;
            carry1 = pHi4 + c3;
            u1d = Sub(u1d, sum6, ref borrow2);

            pHi4 = Multiply64(qhat1, v2n, out pLo4);
            sum6 = pLo4 + carry1;
            c3 = (sum6 < pLo4) ? 1UL : 0UL;
            carry1 = pHi4 + c3;
            u2d = Sub(u2d, sum6, ref borrow2);

            u3d = Sub(u3d, carry1, ref borrow2);
            ulong borrow3 = borrow2;

            if (borrow3 != 0)
            {
                AddBack3(ref u0n2, ref u1d, ref u2d, ref u3d, v0, v1n, v2n);
                qhat1--;
            }

            ulong q0 = qhat1;

            q = Create(q0, q1, 0, 0);

            // Remainder is u0..u2
            UInt256 remN = Create(u0n2, u1d, u2d, 0);
            remainder = ShiftRightSmall(remN, shift);
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

            ulong vRecip = X86Base.X64.IsSupported ? 0 : Reciprocal2By1(v.u3);
            ulong qhat, rhat, rcarry;
            if (u4d == v.u3)
            {
                qhat = ulong.MaxValue;
                ulong sum = u.u3 + v.u3;
                rcarry = (sum < u.u3) ? 1UL : 0UL;
                rhat = sum;
            }
            else
            {
                if (X86Base.X64.IsSupported)
                {
                    (qhat, rhat) = X86Base.X64.DivRem(u.u3, u4d, v.u3); // (upper:lower) = (u4d:u.u3)
                }
                else
                {
                    qhat = UDivRem2By1(u4d, vRecip, v.u3, u.u3, out rhat);
                }
                rcarry = 0;
            }

            if (rcarry == 0)
            {
                ulong pHi = Multiply64(qhat, v.u2, out ulong pLo);

                // if qhat*vNext > rhat*b + uCorr then decrement
                if (pHi > rhat || (pHi == rhat && pLo > u.u2))
                {
                    qhat--;

                    ulong sum1 = rhat + v.u3;
                    if (sum1 < rhat)
                        rcarry = 1;

                    rhat = sum1;
                }
            }

            if (rcarry == 0)
            {
                ulong pHi = Multiply64(qhat, v.u2, out ulong pLo);

                // if qhat*vNext > rhat*b + uCorr then decrement
                if (pHi > rhat || (pHi == rhat && pLo > u.u2))
                {
                    qhat--;
                }
            }

            ulong borrow = SubMul4(in u, ref u4d, in v, qhat, out UInt256 rem);

            if (borrow != 0)
            {
                Add(in rem, in v, out rem);
                qhat--;
            }

            ulong q0 = qhat;

            q = Create(q0, 0, 0, 0);

            // Remainder is u0..u3
            remainder = ShiftRightSmall(rem, shift);
        }

        // Shift-right by 0..63 (used to unnormalise remainder)
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static UInt256 ShiftLeftSmall(in UInt256 v, int sh)
        {
            if (sh == 0) return v;

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
            if (sh == 0) return v;

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

        [SkipLocalsInit]
        [MethodImpl(MethodImplOptions.NoInlining)]
        private static void DivideBy128BitsX86Base(in UInt256 x, in UInt256 y, out UInt256 q, out UInt256 remainder)
        {
            // ------------------------------------------------------------
            // n == 2: specialised Knuth D with hardware DivRem
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
            ref ulong qRef = ref Unsafe.As<UInt256, ulong>(ref q);

            // ------------------------------------------------------------
            // Fast path: if the normalised low limb is 0 then V = v1n*B.
            // That turns the whole thing into a plain 256/64 division on (u4..u1),
            // with remainder (r:u0).
            // ------------------------------------------------------------
            if (v0 == 0)
            {
                Debug.Assert(u4 < v1n);

                ulong r = u4;

                (ulong q2, ulong r2) = X86Base.X64.DivRem(u3, r, v1n);
                r = r2;
                (ulong q1, ulong r1) = X86Base.X64.DivRem(u2, r, v1n);
                r = r1;
                (ulong q0, ulong r0) = X86Base.X64.DivRem(u1, r, v1n);
                r = r0;

                Unsafe.Add(ref qRef, 0) = q0;
                Unsafe.Add(ref qRef, 1) = q1;
                Unsafe.Add(ref qRef, 2) = q2;
                Unsafe.Add(ref qRef, 3) = 0;

                Unsafe.SkipInit(out remainder);
                ref ulong rRef = ref Unsafe.As<UInt256, ulong>(ref remainder);

                if (shift == 0)
                {
                    Unsafe.Add(ref rRef, 0) = u0;
                    Unsafe.Add(ref rRef, 1) = r;
                }
                else
                {
                    int rs = 64 - shift;
                    Unsafe.Add(ref rRef, 0) = (u0 >> shift) | (r << rs);
                    Unsafe.Add(ref rRef, 1) = r >> shift;
                }

                Unsafe.Add(ref rRef, 2) = 0;
                Unsafe.Add(ref rRef, 3) = 0;
                return;
            }

            // ------------------------------------------------------------
            // n == 2 trick:
            // After DivRem on v1n:
            //   (uHi*B + uMid) = qhat*v1n + rhat
            // So subtracting qhat*(v1n*B + v0) from (uHi:uMid:uLo) reduces to:
            //   (rhat:uLo) - qhat*v0
            //
            // This removes the qhat*v1n multiply and the full 3-limb subtract/add-back.
            // ------------------------------------------------------------

            // ------------------------------------------------------------
            // Step j=2: q2 from (u4:u3:u2)
            // ------------------------------------------------------------
            {
                // Always true for this setup: u4 < v1n, so DivRem is safe here.
                Debug.Assert(u4 < v1n);

                (ulong qhat, ulong rhat) = X86Base.X64.DivRem(u3, u4, v1n);
                bool rcarry = false;

                ulong hi = Multiply64(qhat, v0, out ulong lo);

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

                        rhat += v1n;
                    }
                }

                ulong borrow = (u2 < lo) ? 1UL : 0UL;
                u2 -= lo;
                u3 = rhat - hi - borrow;

                Unsafe.Add(ref qRef, 2) = qhat;
            }

            // ------------------------------------------------------------
            // Step j=1: q1 from (u3:u2:u1)
            // ------------------------------------------------------------
            {
                ulong rhat;
                bool rcarry;
                ulong qhat;

                // Required for DIV safety when uHi == v1n.
                if (u3 == v1n)
                {
                    qhat = ulong.MaxValue;
                    rhat = u2 + v1n;
                    rcarry = rhat < u2;
                }
                else
                {
                    (qhat, rhat) = X86Base.X64.DivRem(u2, u3, v1n);
                    rcarry = false;
                }

                ulong hi = Multiply64(qhat, v0, out ulong lo);

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

                        rhat += v1n;
                    }
                }

                ulong borrow = (u1 < lo) ? 1UL : 0UL;
                u1 -= lo;
                u2 = rhat - hi - borrow;

                Unsafe.Add(ref qRef, 1) = qhat;
            }

            // ------------------------------------------------------------
            // Step j=0: q0 from (u2:u1:u0)
            // ------------------------------------------------------------
            {
                ulong rhat;
                bool rcarry;
                ulong qhat;

                // Required for DIV safety when uHi == v1n.
                if (u2 == v1n)
                {
                    qhat = ulong.MaxValue;
                    rhat = u1 + v1n;
                    rcarry = rhat < u1;
                }
                else
                {
                    (qhat, rhat) = X86Base.X64.DivRem(u1, u2, v1n);
                    rcarry = false;
                }

                ulong hi = Multiply64(qhat, v0, out ulong lo);

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

                        rhat += v1n;
                    }
                }

                ulong borrow = (u0 < lo) ? 1UL : 0UL;
                u0 -= lo;
                u1 = rhat - hi - borrow;

                Unsafe.Add(ref qRef, 0) = qhat;
            }

            // q3 is always 0 for 256/128 here.
            Unsafe.Add(ref qRef, 3) = 0;

            // ------------------------------------------------------------
            // Remainder (u0..u1 in normalised space) - unnormalise.
            // ------------------------------------------------------------
            Unsafe.SkipInit(out remainder);
            ref ulong remRef = ref Unsafe.As<UInt256, ulong>(ref remainder);

            if (shift == 0)
            {
                Unsafe.Add(ref remRef, 0) = u0;
                Unsafe.Add(ref remRef, 1) = u1;
            }
            else
            {
                int rs = 64 - shift;
                Unsafe.Add(ref remRef, 0) = (u0 >> shift) | (u1 << rs);
                Unsafe.Add(ref remRef, 1) = u1 >> shift;
            }

            Unsafe.Add(ref remRef, 2) = 0;
            Unsafe.Add(ref remRef, 3) = 0;
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
                borrow = b | ((t < borrow) ? 1UL : 0UL);

                if (borrow != 0)
                {
                    // Add-back v and decrement qhat.
                    ulong s0 = u2 + v0;
                    ulong c = (s0 < u2) ? 1UL : 0UL;

                    ulong s1 = u3 + v1n;
                    s1 += c;

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
                borrow = b | ((t < borrow) ? 1UL : 0UL);

                if (borrow != 0)
                {
                    ulong s0 = u1 + v0;
                    ulong c = (s0 < u1) ? 1UL : 0UL;

                    ulong s1 = u2 + v1n;
                    s1 += c;

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
                borrow = b | ((t < borrow) ? 1UL : 0UL);

                if (borrow != 0)
                {
                    ulong s0 = u0 + v0;
                    ulong c = (s0 < u0) ? 1UL : 0UL;

                    ulong s1 = u1 + v1n;
                    s1 += c;

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
        private unsafe static ulong Multiply64(ulong a, ulong b, out ulong low)
        {
            if (Bmi2.X64.IsSupported)
            {
                // Two multiplies ends up being faster as it doesn't force spill to stack.
                ulong lowLocal;
                ulong high = Bmi2.X64.MultiplyNoFlags(a, b, &lowLocal);
                low = lowLocal;
                return high;
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

        // ------------------------------------------------------------
        // Knuth steps (unrolled)
        // ------------------------------------------------------------

        // ------------------------------------------------------------
        // qhat correction (at most twice in Knuth D)
        // ------------------------------------------------------------

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static ulong SubMul4(in UInt256 u, ref ulong u4, in UInt256 v, ulong q, out UInt256 rem)
        {
            ulong borrow = 0;

            ulong pHi = Multiply64(q, v.u0, out ulong pLo);
            ulong sum = pLo;
            ulong c2 = (sum < pLo) ? 1UL : 0UL;
            ulong carry = pHi + c2;
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

            u4 = Sub(u4, carry, ref borrow);

            rem = Create(r0, r1, r2, r3);
            return borrow;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static ulong SubMul4(ref ulong u0, ref ulong u1, ref ulong u2, ref ulong u3, ref ulong u4, ulong v0, ulong v1, ulong v2, ulong v3, ulong q)
        {
            ulong borrow = 0;

            ulong pHi = Multiply64(q, v0, out ulong pLo);
            ulong sum = pLo;
            ulong c2 = (sum < pLo) ? 1UL : 0UL;
            ulong carry = pHi + c2;
            u0 = Sub(u0, sum, ref borrow);

            pHi = Multiply64(q, v1, out pLo);
            sum = pLo + carry;
            c2 = (sum < pLo) ? 1UL : 0UL;
            carry = pHi + c2;
            u1 = Sub(u1, sum, ref borrow);

            pHi = Multiply64(q, v2, out pLo);
            sum = pLo + carry;
            c2 = (sum < pLo) ? 1UL : 0UL;
            carry = pHi + c2;
            u2 = Sub(u2, sum, ref borrow);

            pHi = Multiply64(q, v3, out pLo);
            sum = pLo + carry;
            c2 = (sum < pLo) ? 1UL : 0UL;
            carry = pHi + c2;
            u3 = Sub(u3, sum, ref borrow);

            u4 = Sub(u4, carry, ref borrow);

            return borrow;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private static void AddBack3(ref ulong u0, ref ulong u1, ref ulong u2, ref ulong u3, ulong v0, ulong v1, ulong v2)
        {
            ulong sum = u0 + v0;
            ulong carry = (sum < u0) ? 1UL : 0UL;
            u0 = sum;

            sum = u1 + v1;
            ulong c = (sum < u1) ? 1UL : 0UL;
            sum += carry;
            carry = c | ((sum < carry) ? 1UL : 0UL);
            u1 = sum;

            sum = u2 + v2;
            c = (sum < u2) ? 1UL : 0UL;
            sum += carry;
            carry = c | ((sum < carry) ? 1UL : 0UL);
            u2 = sum;

            u3 += carry;
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

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
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
        private static UInt256 Create(ulong u0, ulong u1, ulong u2, ulong u3)
        {
            if (Vector256.IsHardwareAccelerated)
            {
                Vector256<ulong> v = Vector256.Create(u0, u1, u2, u3);
                return Unsafe.As<Vector256<ulong>, UInt256>(ref v);
            }
            else
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
#pragma warning restore SYSLIB5004
}
