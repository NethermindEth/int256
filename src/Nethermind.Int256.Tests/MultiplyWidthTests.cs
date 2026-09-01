// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Collections.Generic;
using System.Numerics;
using System.Reflection;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

/// <summary>
/// Covers the 256x256-to-512-bit product, which dispatches on operand width: a one- or two-limb
/// operand takes a narrower helper with fewer partial products and a shorter carry chain.
/// Every expected value here comes from <see cref="BigInteger"/>, never from limb arithmetic,
/// so a shared mistake in the limb code cannot make a test agree with itself.
/// </summary>
[Parallelizable(ParallelScope.All)]
public class MultiplyWidthTests
{
    private delegate void ProductDelegate(in UInt256 x, in UInt256 y, out UInt256 low, out UInt256 high);

    private static ProductDelegate Resolve(string name)
    {
        MethodInfo method = typeof(UInt256).GetMethod(name, BindingFlags.NonPublic | BindingFlags.Static)
            ?? throw new InvalidOperationException(
                $"UInt256.{name} not found. The width dispatch changed shape - update or delete these tests rather than skipping them.");
        return (ProductDelegate)method.CreateDelegate(typeof(ProductDelegate));
    }

    private static readonly ProductDelegate Dispatch = Resolve("Multiply256To512Bit");
    private static readonly ProductDelegate FullWidth = Resolve("Multiply256To512BitLarge");

    private static BigInteger ToBig(in UInt256 v)
        => v.u0 | ((BigInteger)v.u1 << 64) | ((BigInteger)v.u2 << 128) | ((BigInteger)v.u3 << 192);

    private static BigInteger Product(in UInt256 low, in UInt256 high)
        => ToBig(in low) | (ToBig(in high) << 256);

    private static string Show(in UInt256 v) => $"{v.u3:x16}_{v.u2:x16}_{v.u1:x16}_{v.u0:x16}";

    /// <summary>
    /// Outputs are seeded with this rather than left zeroed. A narrow helper writes zeros into the
    /// limbs its product cannot reach; if it skips one, a zero-initialised output hides the leak
    /// while a real caller reusing a variable would see stale limbs.
    /// </summary>
    private static UInt256 Stale => new(
        0xBAAD_F00D_DEAD_BEEFUL, 0xFEED_FACE_CAFE_D00DUL, 0x1234_5678_9ABC_DEF0UL, 0xC0DE_C0DE_C0DE_C0DEUL);

    // Limb patterns that make carries ripple: saturated limbs, one-off-saturated, and single bits
    // at both ends of a limb. Random limbs almost never drive a carry chain to its bound.
    private static readonly ulong[] Patterns =
    [
        1UL,
        2UL,
        ulong.MaxValue,
        ulong.MaxValue - 1,
        0x8000_0000_0000_0000UL,
        0xFFFF_FFFF_0000_0000UL,
        0x0000_0000_FFFF_FFFFUL,
        0xAAAA_AAAA_AAAA_AAABUL,
    ];

    /// <summary>Values whose most significant non-zero limb is exactly <paramref name="width"/>.</summary>
    private static IEnumerable<UInt256> ValuesOfWidth(int width)
    {
        foreach (ulong p in Patterns)
        {
            // Every limb saturated with the same pattern.
            yield return Build(width, _ => p);
            // Only the top limb set: the shortest possible carry chain at this width.
            yield return Build(width, i => i == width - 1 ? p : 0UL);
            // Top limb minimal, everything below saturated: forces a carry out of the top.
            yield return Build(width, i => i == width - 1 ? 1UL : p);
        }

        // A deterministic sweep, biased towards saturated limbs for the same reason.
        Random random = new(0x57ED7 + width);
        for (int i = 0; i < 24; i++)
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

    [TestCaseSource(nameof(WidthPairs))]
    public void Product_matches_BigInteger(int xWidth, int yWidth)
    {
        foreach (UInt256 x in ValuesOfWidth(xWidth))
        {
            foreach (UInt256 y in ValuesOfWidth(yWidth))
            {
                UInt256 low = Stale, high = Stale;
                Dispatch(in x, in y, out low, out high);

                BigInteger expected = ToBig(in x) * ToBig(in y);
                BigInteger actual = Product(in low, in high);
                if (actual != expected)
                {
                    Assert.Fail($"{xWidth}x{yWidth}: {Show(in x)} * {Show(in y)}\n" +
                                $"  expected {expected:x}\n  actual   {actual:x}");
                }
            }
        }
    }

    /// <summary>
    /// The full-width routine is a different algorithm - product scanning over sixteen partial
    /// products with a three-limb accumulator, against operand scanning with a single-limb carry -
    /// so agreement between them is independent evidence, and a mismatch localises a dispatch bug
    /// to the shape it happened on.
    /// </summary>
    [TestCaseSource(nameof(WidthPairs))]
    public void Dispatch_agrees_with_the_full_width_routine(int xWidth, int yWidth)
    {
        foreach (UInt256 x in ValuesOfWidth(xWidth))
        {
            foreach (UInt256 y in ValuesOfWidth(yWidth))
            {
                UInt256 low = Stale, high = Stale;
                Dispatch(in x, in y, out low, out high);
                UInt256 refLow = Stale, refHigh = Stale;
                FullWidth(in x, in y, out refLow, out refHigh);

                if (!low.Equals(refLow) || !high.Equals(refHigh))
                {
                    Assert.Fail($"{xWidth}x{yWidth}: {Show(in x)} * {Show(in y)}\n" +
                                $"  dispatch   {Show(in high)} {Show(in low)}\n" +
                                $"  full width {Show(in refHigh)} {Show(in refLow)}");
                }
            }
        }
    }

    /// <summary>
    /// Carry stress at bit boundaries rather than limb boundaries. The width generator only makes
    /// limb-aligned patterns, so these products sit outside it. Offsets cluster around every limb
    /// edge, which is where a carry has to cross from one accumulator step to the next: the helpers
    /// accumulate with a one-limb carry, justified by t[i] + x[i]*y + carry never exceeding
    /// 2^128 - 1, and a wrong bound would show up here first.
    /// </summary>
    [Test]
    public void Products_at_bit_boundaries_carry_correctly()
    {
        int[] offsets = [1, 2, 31, 32, 33, 63, 64, 65, 95, 127, 128, 129, 191, 192, 193, 223, 255, 256];

        foreach (int a in offsets)
        {
            foreach (int b in offsets)
            {
                // All-ones of a bits times all-ones of b bits: the longest possible carry ripple.
                BigInteger onesA = (BigInteger.One << a) - 1;
                BigInteger onesB = (BigInteger.One << b) - 1;
                AssertProduct((UInt256)onesA, (UInt256)onesB, onesA * onesB, $"(2^{a}-1)*(2^{b}-1)");

                // A single bit at each offset: no ripple, but every limb position in turn.
                if (a < 256 && b < 256)
                {
                    AssertProduct((UInt256)(BigInteger.One << a), (UInt256)(BigInteger.One << b),
                        BigInteger.One << (a + b), $"2^{a}*2^{b}");
                }
            }
        }

        static void AssertProduct(UInt256 x, UInt256 y, BigInteger expected, string what)
        {
            UInt256 low = Stale, high = Stale;
            Dispatch(in x, in y, out low, out high);
            BigInteger actual = Product(in low, in high);
            if (actual != expected)
            {
                Assert.Fail($"{what}: expected {expected:x}, actual {actual:x}");
            }
        }
    }

    /// <summary>
    /// Zero is a live operand - the EVM multiplies by it - and the width generator deliberately
    /// excludes it, since a zero top limb would silently retest a narrower shape. The deleted
    /// predecessor of this fixture covered zero through one boundary pair; this covers it against
    /// every width, aliased and not, with a stale output that must be fully cleared.
    /// </summary>
    [Test]
    public void Zero_operand_gives_a_zero_product_and_no_overflow()
    {
        UInt256 zero = default;

        for (int width = 1; width <= 4; width++)
        {
            foreach (UInt256 v in ValuesOfWidth(width))
            {
                Check(in zero, in v);
                Check(in v, in zero);
            }
        }

        Check(in zero, in zero);

        static void Check(in UInt256 x, in UInt256 y)
        {
            UInt256 low = Stale, high = Stale;
            Dispatch(in x, in y, out low, out high);
            if (!low.IsZero || !high.IsZero)
            {
                Assert.Fail($"{Show(in x)} * {Show(in y)} left {Show(in high)} {Show(in low)}, expected zero");
            }

            if (UInt256.MultiplyOverflow(in x, in y, out UInt256 res) || !res.IsZero)
            {
                Assert.Fail($"MultiplyOverflow({Show(in x)}, {Show(in y)}) reported overflow or a non-zero product");
            }

            // Aliased: a stale high half here would surface as a spurious overflow.
            UInt256 aliased = x;
            if (UInt256.MultiplyOverflow(in aliased, in y, out aliased) || !aliased.IsZero)
            {
                Assert.Fail($"aliased MultiplyOverflow({Show(in x)}, {Show(in y)}) reported overflow or a non-zero product");
            }
        }
    }

    /// <summary>
    /// The helpers copy every limb they need into locals before writing any result limb, because a
    /// caller may pass the same storage for an input and an output. Hoisting a store above a read
    /// breaks this and nothing else notices.
    /// </summary>
    /// <remarks>
    /// Only the MultiplyOverflow assertions reach the width helpers, and only through the low
    /// output - that is the only aliasing the public surface can produce, since MultiplyMod hands
    /// the multiply two fresh locals. The MultiplyMod assertions below cover the reduction path
    /// instead, which is worth having but is not what this test is named for.
    /// </remarks>
    [TestCaseSource(nameof(WidthPairs))]
    public void Output_may_alias_either_input(int xWidth, int yWidth)
    {
        UInt256 modulus = new(0xFFFF_FFFF_FFFF_FFF1UL, 0x0123_4567_89AB_CDEFUL, 0xFEDC_BA98_7654_3210UL, 0x8000_0000_0000_0001UL);

        foreach (UInt256 x in ValuesOfWidth(xWidth))
        {
            foreach (UInt256 y in ValuesOfWidth(yWidth))
            {
                BigInteger product = ToBig(in x) * ToBig(in y);
                BigInteger truncated = product & TestNumbers.UInt256Max;
                bool overflows = product > TestNumbers.UInt256Max;

                UInt256 unaliased = x;
                bool plain = UInt256.MultiplyOverflow(in unaliased, in y, out UInt256 plainResult);

                UInt256 left = x;
                bool leftOverflow = UInt256.MultiplyOverflow(in left, in y, out left);
                Check(ToBig(in left) == truncated && leftOverflow == overflows, "MultiplyOverflow res aliased onto x", in x, in y);

                UInt256 right = y;
                bool rightOverflow = UInt256.MultiplyOverflow(in x, in right, out right);
                Check(ToBig(in right) == truncated && rightOverflow == overflows, "MultiplyOverflow res aliased onto y", in x, in y);

                Check(ToBig(in plainResult) == truncated && plain == overflows, "MultiplyOverflow unaliased", in x, in y);

                BigInteger reduced = product % ToBig(in modulus);

                UInt256 modLeft = x;
                modLeft.MultiplyMod(y, modulus, out modLeft);
                Check(ToBig(in modLeft) == reduced, "MultiplyMod res aliased onto x", in x, in y);

                UInt256 modRight = y;
                x.MultiplyMod(modRight, modulus, out modRight);
                Check(ToBig(in modRight) == reduced, "MultiplyMod res aliased onto y", in x, in y);

                UInt256 modMod = modulus;
                x.MultiplyMod(y, modMod, out modMod);
                Check(ToBig(in modMod) == reduced, "MultiplyMod res aliased onto the modulus", in x, in y);
            }
        }

        static void Check(bool ok, string what, in UInt256 x, in UInt256 y)
        {
            if (!ok)
            {
                Assert.Fail($"{what} gave the wrong answer for {Show(in x)} * {Show(in y)}");
            }
        }
    }

    public static IEnumerable<TestCaseData> OverflowLimbCases
    {
        get
        {
            // 2^255 * 2^(64i + 1) = 2^(256 + 64i): the only set bit in the high half lands in limb i.
            // Each case fails a test that only looks at one limb of the high half.
            for (int limb = 0; limb < 4; limb++)
            {
                yield return new TestCaseData(255, 64 * limb + 1, true).SetName($"{{m}}(high limb {limb} set)");
            }

            // 2^255 * 2 - 1 worth of headroom: the largest product that still fits.
            yield return new TestCaseData(128, 127, false).SetName("{m}(exactly 2^255, no overflow)");
            yield return new TestCaseData(128, 128, true).SetName("{m}(exactly 2^256, overflow by one bit)");
            yield return new TestCaseData(0, 255, false).SetName("{m}(1 * 2^255, no overflow)");
        }
    }

    /// <summary>
    /// The overflow flag is a scalar test over all four limbs of the high half. Anything that reads
    /// only some of them - or reads the wrong width - passes on random inputs and fails on a product
    /// whose only high bit sits in a limb it does not look at.
    /// </summary>
    [TestCaseSource(nameof(OverflowLimbCases))]
    public void MultiplyOverflow_reports_every_high_limb(int xShift, int yShift, bool expectedOverflow)
    {
        UInt256 x = One << xShift;
        UInt256 y = One << yShift;

        bool overflow = UInt256.MultiplyOverflow(in x, in y, out UInt256 result);

        BigInteger product = BigInteger.One << (xShift + yShift);
        Assert.Multiple(() =>
        {
            Assert.That(overflow, Is.EqualTo(expectedOverflow), $"overflow flag for 2^{xShift} * 2^{yShift}");
            Assert.That(ToBig(in result), Is.EqualTo(product & TestNumbers.UInt256Max), "truncated product");
        });
    }

    [Test]
    public void MultiplyOverflow_is_exact_at_the_boundary()
    {
        // One bit either side of 2^256: (2^255 - 1) * 2 fits, 2^255 * 2 does not.
        UInt256 justUnder = (One << 255) - One;
        UInt256 two = new(2);

        Assert.Multiple(() =>
        {
            Assert.That(UInt256.MultiplyOverflow(in justUnder, in two, out UInt256 under), Is.False);
            Assert.That(ToBig(in under), Is.EqualTo(((BigInteger.One << 255) - 1) * 2));

            UInt256 at = One << 255;
            Assert.That(UInt256.MultiplyOverflow(in at, in two, out UInt256 over), Is.True);
            Assert.That(ToBig(in over), Is.EqualTo(BigInteger.Zero), "2^256 truncates to zero");

            Assert.That(UInt256.MultiplyOverflow(in UInt256.MaxValue, in UInt256.MaxValue, out UInt256 max), Is.True);
            Assert.That(ToBig(in max), Is.EqualTo(BigInteger.One), "(2^256 - 1)^2 truncates to one");
        });
    }

    private static UInt256 One => UInt256.One;

    /// <summary>
    /// Each helper's declared domain: how many limbs it reads from the first and second operand.
    /// The dispatch is only safe because it never routes an operand wider than these.
    /// </summary>
    public static IEnumerable<TestCaseData> WidthHelpers
    {
        get
        {
            yield return new TestCaseData("Multiply64By128", 1, 2).SetName("{m}(Multiply64By128 reads 1 and 2 limbs)");
            yield return new TestCaseData("Multiply128By128", 2, 2).SetName("{m}(Multiply128By128 reads 2 and 2 limbs)");
            yield return new TestCaseData("MultiplyWideBy64", 4, 1).SetName("{m}(MultiplyWideBy64 reads 4 and 1 limbs)");
            yield return new TestCaseData("MultiplyWideBy128", 4, 2).SetName("{m}(MultiplyWideBy128 reads 4 and 2 limbs)");
        }
    }

    /// <summary>
    /// A helper must be correct over its declared domain and must ignore every limb outside it -
    /// that is the precondition the width dispatch trades on. Junk in the limbs a helper is not
    /// supposed to read has to leave the answer untouched, otherwise widening the dispatch later
    /// silently produces wrong products instead of merely slow ones.
    /// </summary>
    /// <remarks>
    /// Routing a shape to a helper that is *too wide* stays correct and only costs partial
    /// products, so no assertion here can catch it; NarrowMultiplyDispatchBenchmark covers that.
    /// </remarks>
    [TestCaseSource(nameof(WidthHelpers))]
    public void Width_helper_reads_exactly_its_declared_limbs(string name, int xLimbs, int yLimbs)
    {
        ProductDelegate helper = Resolve(name);
        const ulong junk = 0xDEAD_BEEF_C0DE_F00DUL;

        foreach (UInt256 x in ValuesOfWidth(xLimbs))
        {
            foreach (UInt256 y in ValuesOfWidth(yLimbs))
            {
                UInt256 low = Stale, high = Stale;
                helper(in x, in y, out low, out high);

                BigInteger expected = ToBig(in x) * ToBig(in y);
                BigInteger actual = Product(in low, in high);
                if (actual != expected)
                {
                    Assert.Fail($"{name}({Show(in x)}, {Show(in y)})\n  expected {expected:x}\n  actual   {actual:x}");
                }

                UInt256 xJunk = WithJunkAbove(in x, xLimbs, junk);
                UInt256 yJunk = WithJunkAbove(in y, yLimbs, junk);
                // A helper that reads all four limbs of an operand has no out-of-domain limb on
                // that side, so only the other side proves anything. Fail if neither does.
                Assert.That(xJunk.Equals(x) && yJunk.Equals(y), Is.False,
                    $"{name} has no out-of-domain limb on either side; this case cannot fail");
                UInt256 junkLow = Stale, junkHigh = Stale;
                helper(in xJunk, in yJunk, out junkLow, out junkHigh);

                if (!junkLow.Equals(low) || !junkHigh.Equals(high))
                {
                    Assert.Fail($"{name} read a limb outside its {xLimbs}x{yLimbs} domain: " +
                                $"{Show(in xJunk)} * {Show(in yJunk)} gave {Show(in junkHigh)} {Show(in junkLow)}, " +
                                $"expected {Show(in high)} {Show(in low)}");
                }
            }
        }

        static UInt256 WithJunkAbove(in UInt256 v, int limbs, ulong junk) => new(
            limbs > 0 ? v.u0 : junk,
            limbs > 1 ? v.u1 : junk,
            limbs > 2 ? v.u2 : junk,
            limbs > 3 ? v.u3 : junk);
    }

    public static IEnumerable<TestCaseData> ModulusClasses
    {
        get
        {
            yield return new TestCaseData(new UInt256(0xFFFF_FFFF_FFFF_FFF1UL, 0x0123_4567_89AB_CDEFUL, 0xFEDC_BA98_7654_3210UL, 0x8000_0000_0000_0001UL)).SetName("{m}(256-bit modulus)");
            yield return new TestCaseData(new UInt256(ulong.MaxValue, ulong.MaxValue, ulong.MaxValue, 0)).SetName("{m}(192-bit modulus)");
            yield return new TestCaseData(new UInt256(3, 0, 0, 0)).SetName("{m}(small modulus)");
            yield return new TestCaseData(UInt256.MaxValue).SetName("{m}(modulus = 2^256 - 1)");
            yield return new TestCaseData(new UInt256(0, 0, 1, 0)).SetName("{m}(power-of-two modulus)");
            yield return new TestCaseData(UInt256.One).SetName("{m}(modulus = 1)");
        }
    }

    /// <summary>
    /// The reduction consumes both halves of the product, so a wrong high half survives a
    /// truncated-multiply test and only shows up here.
    /// </summary>
    [TestCaseSource(nameof(ModulusClasses))]
    public void MultiplyMod_matches_BigInteger_for_every_operand_width(UInt256 modulus)
    {
        BigInteger m = ToBig(in modulus);

        for (int xWidth = 1; xWidth <= 4; xWidth++)
        {
            for (int yWidth = 1; yWidth <= 4; yWidth++)
            {
                foreach (UInt256 x in ValuesOfWidth(xWidth))
                {
                    foreach (UInt256 y in ValuesOfWidth(yWidth))
                    {
                        UInt256.MultiplyMod(in x, in y, in modulus, out UInt256 result);

                        BigInteger expected = ToBig(in x) * ToBig(in y) % m;
                        if (ToBig(in result) != expected)
                        {
                            Assert.Fail($"{xWidth}x{yWidth} mod {Show(in modulus)}: {Show(in x)} * {Show(in y)}\n" +
                                        $"  expected {expected:x}\n  actual   {ToBig(in result):x}");
                        }
                    }
                }
            }
        }
    }
}
