// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Collections.Generic;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

/// <summary>
/// Covers <see cref="UInt256.Mod"/>'s remainder-only Knuth kernels, which dispatch on divisor width
/// and never form the quotient. Every expected value comes from <see cref="BigInteger"/>, never from
/// limb arithmetic, so a shared mistake in the limb code cannot make a test agree with itself.
/// </summary>
/// <remarks>
/// The rare paths are what these tests exist for, and operands drawn at random do not reach them.
/// The D3 quotient-estimate correction fires on about 1% of digits; its second iteration is rarer
/// still, and in the four-limb kernel - which runs exactly one digit - it needs a divisor whose
/// normalised top limb sits just above 2^63. The add-back is rarer again, because it needs a borrow
/// out of a limb that a correction has not already carried into, which is the distinction the
/// kernels' borrow-and-carry test draws.
/// <para>
/// So cases are constructed as x = q*y + r, with q and r placed on the boundaries that drive those
/// branches and swept across every normalising shift, rather than sampled. <see cref="PinnedCases"/>
/// carries operands found by search, for a branch even that construction reaches only occasionally.
/// </para>
/// </remarks>
[Parallelizable(ParallelScope.All)]
public class ModKernelTests
{
    private static readonly BigInteger TwoPow256 = BigInteger.One << 256;

    private static BigInteger ToBig(in UInt256 v)
        => v.u0 | ((BigInteger)v.u1 << 64) | ((BigInteger)v.u2 << 128) | ((BigInteger)v.u3 << 192);

    private static UInt256 FromBig(BigInteger v)
    {
        if (v.Sign < 0 || v >= TwoPow256)
        {
            Assert.Fail($"case generator produced a value outside UInt256: {v:x}");
        }

        return new UInt256(
            (ulong)(v & ulong.MaxValue), (ulong)((v >> 64) & ulong.MaxValue),
            (ulong)((v >> 128) & ulong.MaxValue), (ulong)((v >> 192) & ulong.MaxValue));
    }

    private static string Show(in UInt256 v) => $"{v.u3:x16}_{v.u2:x16}_{v.u1:x16}_{v.u0:x16}";

    /// <summary>
    /// Checks one pair against <see cref="BigInteger"/>, and again against the remainder implied by
    /// <see cref="UInt256.Divide"/>.
    /// </summary>
    /// <remarks>
    /// The second check is independent evidence rather than a restatement of the first: Divide still
    /// goes through the full-quotient Knuth routine, which is a separate body of limb code from the
    /// remainder-only kernels under test, so the two agreeing is not self-confirmation. It also
    /// localises a failure - a pair BigInteger rejects but Divide accepts points at a kernel, while
    /// one both reject points further up, at the entry compare or the width dispatch.
    /// </remarks>
    private static void AssertMod(in UInt256 x, in UInt256 y)
    {
        BigInteger by = ToBig(in y);
        if (by.IsZero) return;

        UInt256.Mod(in x, in y, out UInt256 actual);
        BigInteger expected = ToBig(in x) % by;
        if (ToBig(in actual) != expected)
        {
            Assert.Fail($"{Show(in x)} % {Show(in y)}\n  expected {expected:x}\n  actual   {ToBig(in actual):x}");
        }

        UInt256.Divide(in x, in y, out UInt256 quotient);
        UInt256.Multiply(in quotient, in y, out UInt256 product);
        UInt256.Subtract(in x, in product, out UInt256 viaDivide);
        if (!viaDivide.Equals(actual))
        {
            Assert.Fail($"{Show(in x)} % {Show(in y)}\n  kernel {Show(in actual)}\n  divide {Show(in viaDivide)}");
        }
    }

    // Limb patterns that drive the quotient estimate to its bounds: a saturated limb makes it
    // saturate, a near-saturated one makes it overshoot, and a single bit fixes the normalising shift.
    private static readonly ulong[] Patterns =
    [
        1UL,
        2UL,
        ulong.MaxValue,
        ulong.MaxValue - 1,
        0x8000_0000_0000_0000UL,
        0x8000_0000_0000_0001UL,
        0x4000_0000_0000_0000UL,
        0xFFFF_FFFF_0000_0000UL,
        0x0000_0000_FFFF_FFFFUL,
        0xAAAA_AAAA_AAAA_AAABUL,
    ];

    /// <summary>Values whose most significant non-zero limb is exactly <paramref name="width"/>.</summary>
    private static IEnumerable<UInt256> ValuesOfWidth(int width)
    {
        foreach (ulong p in Patterns)
        {
            yield return Build(width, _ => p);
            // Only the top limb set: nothing below for a subtraction to borrow from.
            yield return Build(width, i => i == width - 1 ? p : 0UL);
            // Top limb minimal, everything below saturated: forces a carry out of the top.
            yield return Build(width, i => i == width - 1 ? 1UL : p);
            // Top limb saturated: normalising shift 0, which is its own branch in three kernels.
            yield return Build(width, i => i == width - 1 ? ulong.MaxValue : p);
        }

        // A deterministic sweep, biased towards saturated limbs for the same reason.
        Random random = new(0x4D0D + width);
        for (int i = 0; i < 8; i++)
        {
            yield return Build(width, _ => NextLimb(random));
        }

        static UInt256 Build(int width, Func<int, ulong> limb)
        {
            ulong u0 = limb(0);
            ulong u1 = width > 1 ? limb(1) : 0;
            ulong u2 = width > 2 ? limb(2) : 0;
            ulong u3 = width > 3 ? limb(3) : 0;

            // Keep the declared width exact - a zero top limb would silently retest a narrower shape.
            switch (width)
            {
                case 1 when u0 == 0: u0 = 1; break;
                case 2 when u1 == 0: u1 = 1; break;
                case 3 when u2 == 0: u2 = 1; break;
                case 4 when u3 == 0: u3 = 1; break;
            }

            return new UInt256(u0, u1, u2, u3);
        }
    }

    /// <summary>
    /// Every <paramref name="stride"/>-th value of a width. The tests that reduce a pair rather than
    /// divide it - signed remainder, modular product - reach the same kernels through the same width
    /// dispatch, so they need a representative spread rather than the whole cross product.
    /// </summary>
    private static IEnumerable<UInt256> SampleOfWidth(int width, int stride)
    {
        int i = 0;
        foreach (UInt256 v in ValuesOfWidth(width))
        {
            if (i++ % stride == 0) yield return v;
        }
    }

    private static ulong NextLimb(Random random)
    {
        ulong v = (ulong)random.NextInt64() ^ ((ulong)random.NextInt64() << 32);
        return random.Next(4) switch
        {
            0 => ulong.MaxValue,
            1 => v | 0xFFFF_FFFF_0000_0000UL,
            _ => v,
        };
    }

    public static IEnumerable<TestCaseData> WidthPairs
    {
        get
        {
            for (int x = 1; x <= 4; x++)
            {
                for (int y = 1; y <= 4; y++)
                {
                    yield return new TestCaseData(x, y).SetName($"{{m}}({x}x{y})");
                }
            }
        }
    }

    /// <summary>
    /// The shape is (dividend limbs) x (divisor limbs), which is what decides how many Knuth digits
    /// the division needs - so which kernel runs, and how many of its digits are skipped because the
    /// dividend stops short of the top limb.
    /// </summary>
    [TestCaseSource(nameof(WidthPairs))]
    public void Remainder_matches_BigInteger_by_shape(int dividendWidth, int divisorWidth)
    {
        foreach (UInt256 x in ValuesOfWidth(dividendWidth))
        {
            foreach (UInt256 y in ValuesOfWidth(divisorWidth))
            {
                AssertMod(in x, in y);
            }
        }
    }

    public static IEnumerable<TestCaseData> Shifts
    {
        get
        {
            for (int shift = 0; shift < 64; shift++)
            {
                yield return new TestCaseData(shift).SetName($"{{m}}(shift={shift})");
            }
        }
    }

    /// <summary>
    /// Sweeps the normalising shift, which the kernels apply as funnel shifts by <c>shift</c> and
    /// <c>64 - shift</c>. Shift 0 takes its own branch in the 192-, 128- and 64-bit kernels, and at
    /// shift 63 the carry-in limb is widest, so both ends need cases at every divisor width.
    /// </summary>
    /// <remarks>
    /// Quotients and remainders sit on the boundaries rather than at random: a quotient digit of
    /// 2^64 - 1 is what makes the estimate saturate, and a remainder of y - 1 is what leaves the
    /// subtraction closest to borrowing.
    /// </remarks>
    [TestCaseSource(nameof(Shifts))]
    public void Remainder_matches_BigInteger_across_normalising_shifts(int shift)
    {
        Random random = new(0x5417 + shift);

        for (int width = 1; width <= 4; width++)
        {
            foreach (ulong top in TopLimbs(shift))
            {
                foreach (UInt256 y in DivisorsWithTopLimb(width, top, random))
                {
                    BigInteger by = ToBig(in y);
                    if (by <= 1) continue;

                    foreach (BigInteger q in QuotientCandidates(width, random))
                    {
                        foreach (BigInteger r in new[] { BigInteger.Zero, BigInteger.One, by - 1, by >> 1 })
                        {
                            BigInteger bx = q * by + r;
                            if (bx >= TwoPow256) continue;
                            AssertMod(FromBig(bx), in y);
                        }
                    }
                }
            }
        }

        // Top divisor limbs with exactly `shift` leading zeros, so normalisation shifts by it. The
        // estimate's error grows as the normalised top limb approaches 2^63, which is where `bit`
        // lands once shifted up, so the low bits are varied around it rather than left clear.
        static IEnumerable<ulong> TopLimbs(int shift)
        {
            ulong bit = 1UL << (63 - shift);
            yield return bit;
            yield return bit | 1UL;
            yield return bit | (bit - 1);
            yield return bit | (bit >> 1);
        }

        static IEnumerable<UInt256> DivisorsWithTopLimb(int width, ulong top, Random random)
        {
            foreach (ulong low in new[] { 0UL, 1UL, ulong.MaxValue, NextLimb(random) })
            {
                ulong u0 = width > 1 ? low : top;
                ulong u1 = width > 2 ? low : width > 1 ? top : 0;
                ulong u2 = width > 3 ? low : width > 2 ? top : 0;
                ulong u3 = width > 3 ? top : 0;
                yield return new UInt256(u0, u1, u2, u3);
            }
        }

        static IEnumerable<BigInteger> QuotientCandidates(int divisorWidth, Random random)
        {
            yield return BigInteger.One;
            yield return ulong.MaxValue;
            yield return ulong.MaxValue - 1;

            // One digit per dividend limb past the divisor, so a wider quotient runs more digits.
            for (int digits = 1; digits + divisorWidth <= 4; digits++)
            {
                BigInteger q = 0;
                for (int i = 0; i < digits; i++) q = (q << 64) | NextLimb(random);
                yield return q;
                yield return (BigInteger.One << (64 * digits)) - 1;
            }
        }
    }

    /// <summary>
    /// Operands found by search, kept as literals so the branch they reach is covered on every run
    /// rather than whenever a generator happens to land on it.
    /// </summary>
    public static IEnumerable<TestCaseData> PinnedCases
    {
        get
        {
            // Both fire the four-limb kernel's second D3 correction, where the initial quotient
            // estimate is two too large rather than one. It needs a divisor whose normalised top
            // limb is just above 2^63 together with a dividend that fills limb 3, which neither the
            // shape nor the shift sweep above produces; a randomised search over the whole operand
            // space reaches it about eight times in twenty million pairs.
            yield return Pin("four-limb second D3 correction, minimal divisor top limb",
                new UInt256(0x0000000000100000, 0x0020000000000000, 0x000000000007ffff, 0xfffffffffffffffe),
                new UInt256(0x0000000000040000, 0x0000010000000000, 0x000000000003ffff, 0x0000000000000001));
            yield return Pin("four-limb second D3 correction, saturated dividend",
                new UInt256(0x0000000001ffffff, 0x0400000000000000, 0x0000200000000000, 0xffffffffffffffff),
                new UInt256(0x0080000000000000, 0xc000000000000000, 0x00003fffffffffff, 0x0000000000000001));

            static TestCaseData Pin(string name, UInt256 x, UInt256 y)
                => new TestCaseData(x, y).SetName($"{{m}}({name})");
        }
    }

    [TestCaseSource(nameof(PinnedCases))]
    public void Remainder_matches_BigInteger_for_pinned_cases(UInt256 x, UInt256 y) => AssertMod(in x, in y);

    /// <summary>
    /// Operands one either side of a power of two. The width and shift sweeps build limb-aligned
    /// values, so a carry that only ripples at a bit boundary sits outside them, and an exact power
    /// of two takes the masking path rather than a kernel.
    /// </summary>
    [Test]
    public void Remainder_matches_BigInteger_at_bit_boundaries()
    {
        // Limb and half-limb edges, which is where a carry has to cross from one funnel shift to the
        // next and where the normalising shift changes the limb a window starts in.
        int[] divisorBits = [1, 31, 32, 33, 63, 64, 65, 95, 127, 128, 129, 191, 192, 193, 255];

        for (int i = 0; i < 256; i++)
        {
            foreach (int dx in new[] { -1, 0, 1 })
            {
                BigInteger bx = (BigInteger.One << i) + dx;
                if (bx <= 0 || bx >= TwoPow256) continue;

                foreach (int j in divisorBits)
                {
                    foreach (int dy in new[] { -1, 0, 1 })
                    {
                        BigInteger by = (BigInteger.One << j) + dy;
                        if (by <= 0 || by >= TwoPow256) continue;
                        AssertMod(FromBig(bx), FromBig(by));
                    }
                }
            }
        }
    }

    /// <summary>
    /// <see cref="Int256.Mod"/> answers two non-negative operands without copying either of them and
    /// takes absolute values only on the arm that needs them, so each sign combination is a separate
    /// path. The remainder keeps the dividend's sign, which is what <see cref="BigInteger"/>'s own
    /// remainder operator does, so it can be compared directly.
    /// </summary>
    [TestCaseSource(nameof(WidthPairs))]
    public void Signed_remainder_matches_BigInteger_by_shape(int dividendWidth, int divisorWidth)
    {
        foreach (UInt256 xMagnitude in SampleOfWidth(dividendWidth, 3))
        {
            foreach (UInt256 yMagnitude in SampleOfWidth(divisorWidth, 3))
            {
                // A magnitude with limb 3's top bit set already reads as negative, so negating it
                // would retest a pair the loop covers anyway. Only well-formed magnitudes are signed.
                if (((xMagnitude.u3 | yMagnitude.u3) & (1UL << 63)) != 0) continue;

                Int256 x = new(xMagnitude), y = new(yMagnitude);
                Int256.Neg(in x, out Int256 negX);
                Int256.Neg(in y, out Int256 negY);

                AssertSignedMod(in x, in y);
                AssertSignedMod(in negX, in y);
                AssertSignedMod(in x, in negY);
                AssertSignedMod(in negX, in negY);
            }
        }

        static void AssertSignedMod(in Int256 x, in Int256 y)
        {
            BigInteger by = (BigInteger)y;
            if (by.IsZero) return;

            Int256.Mod(in x, in y, out Int256 actual);
            BigInteger expected = (BigInteger)x % by;
            if ((BigInteger)actual != expected)
            {
                Assert.Fail($"{(BigInteger)x} % {by}\n  expected {expected}\n  actual   {(BigInteger)actual}");
            }
        }
    }

    /// <summary>
    /// <see cref="UInt256.MultiplyMod"/> reduces both factors against a single-limb modulus and then
    /// reduces their product.
    /// </summary>
    /// <remarks>
    /// Hardware div takes the modulus unnormalised, which is sound only because both reduced factors
    /// are below it and so the product's upper limb is below it too. If that stopped holding the
    /// divide would overflow rather than answer wrongly, so the cases here pair each modulus with
    /// factors at its own boundary.
    /// </remarks>
    [Test]
    public void Modular_product_matches_BigInteger_for_single_limb_moduli()
    {
        Random random = new(0x3D0D);

        foreach (ulong modulus in Patterns)
        {
            Check(modulus);
        }

        // A power of two takes the masking path, one less takes a kernel with every low bit set, and
        // the random draw keeps the sweep from only ever seeing those two shapes.
        for (int i = 0; i < 64; i += 3)
        {
            Check(1UL << i);
            Check((1UL << i) - 1);
            Check(NextLimb(random));
        }

        static void Check(ulong modulus)
        {
            if (modulus == 0) return;

            UInt256 m = new(modulus, 0, 0, 0);
            UInt256 justBelow = new(modulus - 1, 0, 0, 0);

            for (int width = 1; width <= 4; width++)
            {
                foreach (UInt256 x in SampleOfWidth(width, 5))
                {
                    Verify(in x, in justBelow, in m, modulus);
                    Verify(in x, in x, in m, modulus);
                }
            }
        }

        static void Verify(in UInt256 x, in UInt256 y, in UInt256 m, ulong modulus)
        {
            UInt256.MultiplyMod(in x, in y, in m, out UInt256 actual);
            BigInteger expected = ToBig(in x) * ToBig(in y) % modulus;
            if (ToBig(in actual) != expected)
            {
                Assert.Fail($"{Show(in x)} * {Show(in y)} mod {modulus:x16}\n" +
                            $"  expected {expected:x}\n  actual   {ToBig(in actual):x}");
            }
        }
    }
}
