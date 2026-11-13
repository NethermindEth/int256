// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Numerics;
using System.Reflection;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

public class MultiplyModShortBarrettTests
{
    private static readonly BigInteger Two256 = BigInteger.One << 256;

    private static readonly Type ModulusInterface = typeof(UInt256).GetNestedType("IShortBarrettModulus", BindingFlags.NonPublic)!;
    private static readonly MethodInfo Reduce = typeof(UInt256).GetMethod("Remainder512ByShortBarrett", BindingFlags.NonPublic | BindingFlags.Static)!;

    private static readonly Dictionary<string, BigInteger> Known = new()
    {
        ["Bn254R"] = Hex("30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001"),
        ["Bn254P"] = Hex("30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47"),
        ["Prime251"] = (BigInteger.One << 251) + 17 * (BigInteger.One << 192) + 1,
    };

    private static IEnumerable<TestCaseData> KnownModuli() =>
        Known.Select(p => new TestCaseData(p.Key).SetArgDisplayNames(p.Key));

    [Test]
    public void Every_modulus_with_the_reduction_is_tested()
    {
        string[] implemented = typeof(UInt256).GetNestedTypes(BindingFlags.NonPublic)
            .Where(t => t.IsValueType && ModulusInterface.IsAssignableFrom(t)).Select(t => t.Name).Order().ToArray();
        Assert.That(implemented, Is.EqualTo(Known.Keys.Order().ToArray()));
    }

    [TestCaseSource(nameof(KnownModuli))]
    public void Constants_match_the_modulus(string name)
    {
        Type type = ModulusType(name);
        BigInteger m = Known[name];
        int n = (int)type.GetProperty("Bits", BindingFlags.Public | BindingFlags.Static)!.GetValue(null)!;
        Assert.That(n, Is.EqualTo((int)m.GetBitLength()));
        Assert.That(n, Is.InRange(252, 254));
        Assert.That(Nu(type), Is.EqualTo((BigInteger.One << (2 * n)) / m));
    }

    [TestCaseSource(nameof(KnownModuli))]
    public void Reduction_matches_BigInteger_at_boundaries(string name)
    {
        BigInteger m = Known[name];
        BigInteger limit = BigInteger.One << (2 * (int)m.GetBitLength());
        BigInteger[] fixedValues =
        [
            0, 1, m - 1, m, m + 1, Two256 - 1, Two256, limit - 1, limit - 2, limit - limit % m, limit - limit % m - 1,
            m * m, m * m - 1, m * m + 1, (m - 1) * (m - 1), 4 * m - 1, 4 * m,
        ];
        foreach (BigInteger x in fixedValues)
        {
            if (x >= 0 && x < limit) Check(name, x);
        }

        Random random = new(0x5B01);
        for (int i = 0; i < 4_000; i++)
        {
            BigInteger q = RandomBits(random, 1 + random.Next((int)m.GetBitLength()));
            BigInteger[] remainders = [0, 1, m - 1, m - 2, m / 2, RandomBits(random, 256) % m];
            foreach (BigInteger r in remainders)
            {
                BigInteger x = q * m + r;
                if (x < limit) Check(name, x);
            }
        }
    }

    [TestCaseSource(nameof(KnownModuli))]
    public void Reduction_matches_BigInteger_for_random_and_product_dividends(string name)
    {
        BigInteger m = Known[name];
        int n = (int)m.GetBitLength();
        Random random = new(0xB0B1);
        int[] histogram = new int[4];
        for (int i = 0; i < 60_000; i++)
        {
            BigInteger x = (i % 3) switch
            {
                0 => RandomBits(random, 1 + random.Next(2 * n)),
                1 => (RandomBits(random, 256) % m) * (RandomBits(random, 256) % m),
                _ => RandomBits(random, 1 + random.Next(n)) * m + random.Next(4),
            };
            if (x >= BigInteger.One << (2 * n)) continue;
            histogram[Check(name, x)]++;
        }

        Assert.That(histogram[0], Is.GreaterThan(100));
        Assert.That(histogram[1], Is.GreaterThan(100));
    }

    [TestCaseSource(nameof(KnownModuli))]
    public void Reduction_matches_BigInteger_on_estimate_floor_boundaries(string name)
    {
        BigInteger m = Known[name];
        int n = (int)m.GetBitLength();
        BigInteger nu = (BigInteger.One << (2 * n)) / m, scale = BigInteger.One << (n + 1);
        Random random = new(0xF10A);
        int checkedCount = 0;
        for (int i = 0; i < 6_000; i++)
        {
            BigInteger k = RandomBits(random, 1 + random.Next(n));
            BigInteger q1 = (k * scale + nu - 1) / nu + random.Next(-2, 3);
            BigInteger low = (i % 3) switch { 0 => 0, 1 => (BigInteger.One << (n - 1)) - 1, _ => RandomBits(random, n - 1) };
            BigInteger x = (q1 << (n - 1)) + low;
            if (x < 0 || x >= BigInteger.One << (2 * n)) continue;
            Check(name, x);
            checkedCount++;
        }

        Assert.That(checkedCount, Is.GreaterThan(5_000));
    }

    [TestCaseSource(nameof(KnownModuli))]
    public void Estimate_is_at_most_three_below_the_quotient(string name)
    {
        BigInteger m = Known[name];
        int n = (int)m.GetBitLength();
        Random random = new(0x3B3);
        int worst = 0;
        for (int i = 0; i < 200_000; i++)
        {
            BigInteger x = (BigInteger.One << (2 * n)) - 1 - RandomBits(random, 1 + random.Next(2 * n));
            if (x < 0) continue;
            int difference = (int)(x / m - Estimate(x, m, n));
            Assert.That(difference, Is.InRange(0, 3), $"x={x:X}");
            worst = Math.Max(worst, difference);
        }

        Assert.That(worst, Is.GreaterThanOrEqualTo(1));
    }

    private static int Check(string name, BigInteger x)
    {
        BigInteger m = Known[name];
        object?[] args = [FromBig(x & (Two256 - 1)), FromBig(x >> 256), null];
        int passes = (int)Reduce.MakeGenericMethod(ModulusType(name)).Invoke(null, args)!;
        Assert.That(ToBig((UInt256)args[2]!), Is.EqualTo(x % m), $"x={x:X}");
        Assert.That((BigInteger)passes, Is.EqualTo(x / m - Estimate(x, m, (int)m.GetBitLength())), $"x={x:X}");
        return passes;
    }

    private static BigInteger Estimate(BigInteger x, BigInteger m, int n)
    {
        BigInteger nu = (BigInteger.One << (2 * n)) / m, a = x >> (n - 1), sum = 0;
        for (int i = 0; i < 4; i++)
            for (int j = 0; j < 4; j++)
            {
                BigInteger product = Limb(a, i) * Limb(nu, j);
                if (i + j >= 3) sum += product << (64 * (i + j));
                else if (i + j == 2) sum += (product >> 64) << 192;
            }

        return sum >> (n + 1);
    }

    private static BigInteger Limb(BigInteger v, int i) => (v >> (64 * i)) & ulong.MaxValue;

    private static Type ModulusType(string name) => typeof(UInt256).GetNestedType(name, BindingFlags.NonPublic)!;

    private static BigInteger Nu(Type type)
    {
        BigInteger value = 0;
        for (int i = 3; i >= 0; i--)
            value = (value << 64) | (ulong)type.GetProperty($"Nu{i}", BindingFlags.Public | BindingFlags.Static)!.GetValue(null)!;
        return value;
    }

    private static BigInteger RandomBits(Random random, int bits)
    {
        if (bits <= 0) return BigInteger.Zero;
        byte[] bytes = new byte[(bits + 7) / 8 + 1];
        random.NextBytes(bytes);
        bytes[^1] = 0;
        return new BigInteger(bytes) & ((BigInteger.One << bits) - 1);
    }

    private static BigInteger Hex(string value) => BigInteger.Parse("0" + value, NumberStyles.HexNumber);

    private static BigInteger ToBig(UInt256 v) => v.u0 | ((BigInteger)v.u1 << 64) | ((BigInteger)v.u2 << 128) | ((BigInteger)v.u3 << 192);

    private static UInt256 FromBig(BigInteger v) => new((ulong)(v & ulong.MaxValue), (ulong)((v >> 64) & ulong.MaxValue),
        (ulong)((v >> 128) & ulong.MaxValue), (ulong)((v >> 192) & ulong.MaxValue));
}
