// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Numerics;
using System.Reflection;
using System.Threading;
using System.Threading.Tasks;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

// Full-width MULMOD (m >= 2^192): the Barrett reduction for the well-known field moduli and the public operation over
// those and other moduli, against BigInteger.
public class MultiplyModBarrettTests
{
    private static readonly BigInteger Two64 = BigInteger.One << 64;
    private static readonly BigInteger Two192 = BigInteger.One << 192;
    private static readonly BigInteger Two256 = BigInteger.One << 256;
    private static readonly BigInteger Max512 = (BigInteger.One << 512) - 1;

    private static readonly Type ModulusInterface = typeof(UInt256).GetNestedType("IBarrettModulus", BindingFlags.NonPublic)!;
    private static readonly MethodInfo ReduceBarrett = typeof(UInt256).GetMethod("Remainder512ByBarrett", BindingFlags.NonPublic | BindingFlags.Static)!;

    // The moduli with a Barrett reduction, by the name of their constants.
    private static readonly Dictionary<string, BigInteger> Known = new()
    {
        ["Bn254R"] = Hex("30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001"),
        ["Bn254P"] = Hex("30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47"),
        ["Secp256k1P"] = Hex("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f"),
        ["Secp256k1N"] = Hex("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141"),
        ["P256P"] = Hex("ffffffff00000001000000000000000000000000ffffffffffffffffffffffff"),
        ["P256N"] = Hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551"),
    };

    // The known moduli, other field moduli and the boundaries of the four-limb range.
    private static readonly BigInteger[] FullWidthModuli =
    [
        .. Known.Values,
        Hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"), // BLS12-381 r
        (BigInteger.One << 255) - 19,
        Two192,
        Two192 + 1,
        Two192 + Two64,
        Two192 + (BigInteger.One << 128),
        Two192 + Two192 - 1,
        (BigInteger.One << 224) + 1,
        BigInteger.One << 255,
        (BigInteger.One << 255) + 1,
        (BigInteger.One << 255) - 1,
        Two256 - 2,
        Two256 - 3,
        Two256 - Two192,
        Two256 - Two64 - 1,
        (BigInteger.One << 255) + Two192,
        3 * Two192,
        ((BigInteger)ulong.MaxValue << 192) + ulong.MaxValue,
        // Known moduli with one limb changed take the division.
        Known["Bn254R"] ^ 1,
        Known["Bn254R"] ^ (BigInteger.One << 64),
        Known["Bn254R"] ^ (BigInteger.One << 128),
        Known["Bn254P"] ^ (BigInteger.One << 70),
        Known["Secp256k1P"] - Two64,
        Known["Secp256k1N"] ^ (BigInteger.One << 3),
        Known["P256P"] ^ (BigInteger.One << 140),
        Known["P256N"] ^ (BigInteger.One << 190),
    ];

    private static IEnumerable<TestCaseData> Moduli() =>
        FullWidthModuli.Select((m, i) => new TestCaseData(m).SetArgDisplayNames($"m{i}"));

    private static IEnumerable<TestCaseData> KnownModuli() =>
        Known.Select(p => new TestCaseData(p.Key).SetArgDisplayNames(p.Key));

    [Test]
    public void Test_moduli_are_full_width() =>
        Assert.That(FullWidthModuli.All(m => m >= Two192 && m < Two256), Is.True);

    [Test]
    public void Every_modulus_with_a_reduction_is_tested()
    {
        string[] implemented = typeof(UInt256).GetNestedTypes(BindingFlags.NonPublic)
            .Where(t => t.IsValueType && ModulusInterface.IsAssignableFrom(t)).Select(t => t.Name).Order().ToArray();
        Assert.That(implemented, Is.EqualTo(Known.Keys.Order().ToArray()));
    }

    [TestCaseSource(nameof(KnownModuli))]
    public void Constants_match_the_modulus_and_its_reciprocal(string name)
    {
        Type type = ModulusType(name);
        BigInteger m = Known[name];
        Assert.That(Limbs(type, "M"), Is.EqualTo(m));
        Assert.That(Limbs(type, "Mu"), Is.EqualTo(Max512 / m));
        Assert.That((ulong)type.GetField("Top")!.GetValue(null)!, Is.EqualTo((ulong)(m >> 192)));
    }

    // Bound on x / m - qhat over all x < 2^512: (1 + (2^512 - 1) mod m) / m from mu, (2^192 - 1) * mu / 2^512 from
    // q1 and the dropped columns. Below one, qhat is at most one below floor(x / m): one correction at most.
    [TestCaseSource(nameof(KnownModuli))]
    public void Quotient_estimate_needs_at_most_one_correction(string name)
    {
        BigInteger m = Known[name], mu = Max512 / m;
        BigInteger scale = BigInteger.One << 512;
        BigInteger bound = (1 + Max512 % m) * scale / m + (Two192 - 1) * mu + 4 * (scale >> 64);
        Assert.That(bound, Is.LessThan(scale));
    }

    [TestCaseSource(nameof(KnownModuli))]
    public void Barrett_reduction_matches_BigInteger_at_boundaries(string name)
    {
        BigInteger m = Known[name];
        Random random = new(0xBA77);
        foreach (BigInteger x in Dividends(m, random))
        {
            Assert.That(Barrett(name, x), Is.EqualTo(x % m), $"x={x:X}");
        }
    }

    [TestCaseSource(nameof(KnownModuli))]
    public void Barrett_reduction_matches_BigInteger_for_random_dividends(string name)
    {
        BigInteger m = Known[name];
        Random random = new(0xD1CE);
        int corrected = 0, total = 0;
        for (int i = 0; i < 30_000; i++)
        {
            BigInteger x = (i % 3) switch
            {
                0 => RandomBits(random, 257 + random.Next(256)),
                1 => (RandomBits(random, 256) % m) * (RandomBits(random, 256) % m),
                // Just above a multiple of m, where the estimate falls one short.
                _ => RandomBits(random, 1 + random.Next(512 - (int)m.GetBitLength())) * m + random.Next(3),
            };
            if (x < Two256 || x > Max512) continue;
            Assert.That(Barrett(name, x), Is.EqualTo(x % m), $"x={x:X}");
            total++;
            if (x / m != TruncatedBarrettQuotient(x, m)) corrected++;
        }

        // Both outcomes of the final correction are exercised.
        Assert.That(corrected, Is.GreaterThan(100));
        Assert.That(total - corrected, Is.GreaterThan(100));
    }

    // The truncated quotient of any modulus >= 2^192 is at most three below floor(x / m), the bound the reduction's
    // comment states; moduli near 2^192 reach two.
    [Test]
    public void Truncated_quotient_is_at_most_three_below_for_any_full_width_modulus()
    {
        Random random = new(0x7A11);
        int[] histogram = new int[4];
        for (int i = 0; i < 20_000; i++)
        {
            BigInteger m = i % 2 == 0 ? RandomModulus(random, i % 64, i % 6 == 0) : Two192 + RandomBits(random, 1 + random.Next(191));
            BigInteger x = i % 2 == 0 ? RandomBits(random, 512) : ((Max512 - RandomBits(random, 1 + random.Next(300))) / m) * m + random.Next(4);
            if (x > Max512) continue;
            BigInteger difference = x / m - TruncatedBarrettQuotient(x, m);
            Assert.That(difference >= 0 && difference <= 3, Is.True, $"m={m:X} x={x:X}");
            histogram[(int)difference]++;
        }

        Assert.That(histogram[2], Is.GreaterThan(0));
    }

    [TestCaseSource(nameof(Moduli))]
    public void MultiplyMod_matches_BigInteger_for_operand_boundaries(BigInteger m)
    {
        Random random = new(0x0B0E);
        BigInteger[] operands = Operands(m, random).ToArray();
        foreach (BigInteger a in operands)
            foreach (BigInteger b in operands)
            {
                AssertMultiplyMod(a, b, m);
            }
    }

    // a * b lands just below, on, or just above a multiple of m.
    [TestCaseSource(nameof(Moduli))]
    public void MultiplyMod_matches_BigInteger_near_multiples_of_the_modulus(BigInteger m)
    {
        Random random = new(0x0A11);
        for (int i = 0; i < 2_000; i++)
        {
            BigInteger a = RandomBits(random, 1 + random.Next(256)) % m;
            if (a.IsZero || !BigInteger.GreatestCommonDivisor(a, m).IsOne) continue;
            BigInteger inverse = ModInverse(a, m);
            foreach (int delta in new[] { -2, -1, 0, 1, 2 })
            {
                BigInteger b = (inverse * (delta + m)) % m;
                BigInteger lift = (Two256 - 1 - b) / m;
                b += lift.IsZero ? 0 : m * (RandomBits(random, 256) % lift);
                AssertMultiplyMod(a, b, m);
                AssertMultiplyMod(b, a, m);
            }
        }
    }

    // Random moduli (one in two a known one, the rest of every width class) and operands of every width, in parallel.
    // INT256_MULMOD_CASES scales it.
    [Test]
    public void MultiplyMod_matches_BigInteger_for_random_cases()
    {
        int cases = CaseCount(400_000);
        BigInteger[] known = [.. Known.Values];
        int chunks = 64;
        int failures = 0;
        string? first = null;
        Parallel.For(0, chunks, chunk =>
        {
            Random random = new(0x3A7 + chunk * 7919);
            for (int i = 0; i < cases / chunks; i++)
            {
                BigInteger m = random.Next(2) == 0 ? known[random.Next(known.Length)] : RandomModulus(random, random.Next(64), random.Next(4) == 0);
                BigInteger a = RandomOperand(random, m), b = RandomOperand(random, m);
                UInt256.MultiplyMod(FromBig(a), FromBig(b), FromBig(m), out UInt256 res);
                if (ToBig(res) != a * b % m && Interlocked.Increment(ref failures) == 1)
                    first = $"a={a:X} b={b:X} m={m:X}";
            }
        });
        Assert.That(failures, Is.Zero, first);
        TestContext.Out.WriteLine($"random cases: {cases / chunks * chunks}");
    }

    // Field arithmetic: one known modulus, reduced operands, chained products as in x^5 rounds.
    [Test]
    public void MultiplyMod_matches_BigInteger_for_field_products()
    {
        int cases = CaseCount(400_000);
        BigInteger[] fields = [.. Known.Values];
        int chunks = 60;
        int failures = 0;
        string? first = null;
        Parallel.For(0, chunks, chunk =>
        {
            Random random = new(0xF1E1D + chunk * 104729);
            BigInteger m = fields[chunk % fields.Length];
            UInt256 modulus = FromBig(m);
            BigInteger x = RandomBits(random, 256) % m;
            for (int i = 0; i < cases / chunks; i++)
            {
                BigInteger y = i % 3 == 0 ? x : RandomBits(random, 256) % m;
                UInt256.MultiplyMod(FromBig(x), FromBig(y), modulus, out UInt256 res);
                BigInteger expected = x * y % m;
                if (ToBig(res) != expected && Interlocked.Increment(ref failures) == 1)
                    first = $"x={x:X} y={y:X} m={m:X}";
                x = expected;
                if (x.IsZero) x = RandomBits(random, 256) % m;
            }
        });
        Assert.That(failures, Is.Zero, first);
        TestContext.Out.WriteLine($"field products: {cases / chunks * chunks}");
    }

    // The result may share storage with any operand, including the modulus.
    [TestCaseSource(nameof(Moduli))]
    public void MultiplyMod_result_may_alias_an_operand(BigInteger m)
    {
        Random random = new(0xA11A5);
        for (int i = 0; i < 64; i++)
        {
            BigInteger a = RandomBits(random, 256), b = RandomBits(random, 256);
            BigInteger expected = a * b % m;
            UInt256 x = FromBig(a), y = FromBig(b), z = FromBig(m);
            UInt256.MultiplyMod(in x, in y, in z, out z);
            Assert.That(ToBig(z), Is.EqualTo(expected));
            z = FromBig(m);
            UInt256.MultiplyMod(in x, in y, in z, out x);
            Assert.That(ToBig(x), Is.EqualTo(expected));
            x = FromBig(a);
            UInt256.MultiplyMod(in x, in y, in z, out y);
            Assert.That(ToBig(y), Is.EqualTo(expected));
            y = FromBig(b);
            UInt256.MultiplyMod(in x, in x, in z, out x);
            Assert.That(ToBig(x), Is.EqualTo(a * a % m));
        }
    }

    private static void AssertMultiplyMod(BigInteger a, BigInteger b, BigInteger m)
    {
        UInt256.MultiplyMod(FromBig(a), FromBig(b), FromBig(m), out UInt256 res);
        Assert.That(ToBig(res), Is.EqualTo(a * b % m), $"a={a:X} b={b:X} m={m:X}");
    }

    private static IEnumerable<BigInteger> Dividends(BigInteger m, Random random)
    {
        yield return Max512;
        yield return Max512 - 1;
        yield return Two256;
        yield return Two256 + 1;
        yield return Max512 - Max512 % m;
        yield return Max512 - Max512 % m - 1;
        yield return m * m;
        yield return m * m - 1;
        yield return m * m + 1;
        yield return (m - 1) * (m - 1);
        yield return (Two256 - 1) * (Two256 - 1);
        yield return (Two256 - 1) * m;
        yield return Two256 * m;
        for (int i = 0; i < 256; i++)
        {
            BigInteger q = RandomBits(random, 1 + random.Next(512 - (int)m.GetBitLength()));
            BigInteger[] remainders = [BigInteger.Zero, BigInteger.One, m - 1, m - 2, m / 2, RandomBits(random, 256) % m];
            foreach (BigInteger r in remainders)
            {
                BigInteger x = q * m + r;
                if (x <= Max512 && x >= Two256) yield return x;
            }
        }
    }

    private static IEnumerable<BigInteger> Operands(BigInteger m, Random random)
    {
        BigInteger[] fixedValues =
        [
            0, 1, 2, 3, m - 1, m - 2, m, m + 1, 2 * m - 1, Two256 - 1, Two256 - 2, Two256 - m,
            BigInteger.One << 255, Two64 - 1, Two64, Two64 + 1, (BigInteger.One << 128) - 1, BigInteger.One << 128,
            (BigInteger.One << 128) + 1, Two192 - 1, Two192, Two192 + 1, (m >> 1) + 1, (m >> 128) + 1,
        ];
        foreach (BigInteger v in fixedValues)
        {
            if (v >= 0 && v < Two256) yield return v;
        }

        for (int i = 0; i < 8; i++)
        {
            yield return RandomBits(random, 256) % m;
            yield return RandomBits(random, 256);
        }
    }

    private static BigInteger RandomOperand(Random random, BigInteger m) => random.Next(8) switch
    {
        0 => RandomBits(random, 1 + random.Next(256)),
        1 => m - 1 - RandomBits(random, random.Next(64)) % m,
        2 => Two256 - 1 - RandomBits(random, random.Next(64)),
        3 => RandomBits(random, 256),
        _ => RandomBits(random, 256) % m,
    };

    // A modulus in [2^192, 2^256) with `shift` leading zero bits, optionally with zero lower limbs.
    private static BigInteger RandomModulus(Random random, int shift, bool zeroLimbs)
    {
        BigInteger m = RandomBits(random, 256 - shift) | (BigInteger.One << (255 - shift));
        if (zeroLimbs)
        {
            BigInteger keep = (BigInteger.One << 192) * ((BigInteger.One << 64) - 1);
            for (int limb = 0; limb < 3; limb++)
            {
                if (random.Next(2) == 0) keep |= ((BigInteger.One << 64) - 1) << (64 * limb);
            }

            m &= keep;
        }

        return m;
    }

    private static BigInteger RandomBits(Random random, int bits)
    {
        if (bits <= 0) return BigInteger.Zero;
        byte[] bytes = new byte[(bits + 7) / 8 + 1];
        random.NextBytes(bytes);
        bytes[^1] = 0;
        return new BigInteger(bytes) & ((BigInteger.One << bits) - 1);
    }

    private static BigInteger ModInverse(BigInteger a, BigInteger m)
    {
        BigInteger t = 0, newT = 1, r = m, newR = a;
        while (!newR.IsZero)
        {
            BigInteger q = r / newR;
            (t, newT) = (newT, t - q * newT);
            (r, newR) = (newR, r - q * newR);
        }

        return t < 0 ? t + m : t;
    }

    // The quotient estimate of Remainder512ByBarrett: the column 3..9 partial products of (x >> 192) * mu over 2^320.
    private static BigInteger TruncatedBarrettQuotient(BigInteger x, BigInteger m)
    {
        BigInteger mu = Max512 / m, q1 = x >> 192, sum = 0;
        for (int i = 0; i < 5; i++)
            for (int j = 0; j < 5; j++)
            {
                if (i + j >= 3) sum += Limb(q1, i) * Limb(mu, j) << (64 * (i + j));
            }

        return sum >> 320;
    }

    private static BigInteger Limb(BigInteger v, int i) => (v >> (64 * i)) & ulong.MaxValue;

    private static int CaseCount(int defaultCount)
        => int.TryParse(Environment.GetEnvironmentVariable("INT256_MULMOD_CASES"), out int n) && n > 0 ? n : defaultCount;

    private static Type ModulusType(string name) => typeof(UInt256).GetNestedType(name, BindingFlags.NonPublic)!;

    private static BigInteger Limbs(Type type, string prefix)
    {
        BigInteger value = 0;
        for (int i = prefix == "M" ? 3 : 4; i >= 0; i--)
            value = (value << 64) | (ulong)type.GetProperty($"{prefix}{i}", BindingFlags.Public | BindingFlags.Static)!.GetValue(null)!;
        return value;
    }

    // The reduction, checked to need exactly the subtractions the quotient estimate leaves (so a wrong estimate, which
    // the division fallback would hide from the result, still fails).
    private static BigInteger Barrett(string name, BigInteger x)
    {
        object?[] args = [FromBig(x & (Two256 - 1)), FromBig(x >> 256), null];
        int passes = (int)ReduceBarrett.MakeGenericMethod(ModulusType(name)).Invoke(null, args)!;
        BigInteger m = Known[name];
        Assert.That((BigInteger)passes, Is.EqualTo(x / m - TruncatedBarrettQuotient(x, m)), $"x={x:X}");
        return ToBig((UInt256)args[2]!);
    }

    private static BigInteger Hex(string value) => BigInteger.Parse("0" + value, NumberStyles.HexNumber);

    private static BigInteger ToBig(UInt256 v) => v.u0 | ((BigInteger)v.u1 << 64) | ((BigInteger)v.u2 << 128) | ((BigInteger)v.u3 << 192);

    private static UInt256 FromBig(BigInteger v) => new((ulong)(v & ulong.MaxValue), (ulong)((v >> 64) & ulong.MaxValue),
        (ulong)((v >> 128) & ulong.MaxValue), (ulong)((v >> 192) & ulong.MaxValue));
}
