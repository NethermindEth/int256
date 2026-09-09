// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Numerics;
using System.Reflection;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

public class ComparisonMaskTests
{
    private delegate bool CompareBoth(in UInt256 x, in UInt256 y, in UInt256 modulus);

    [Test]
    public void Operators_match_all_limb_ordering_patterns()
    {
        UInt256 right = new(0x8000_0000_0000_0000, 0x7FFF_FFFF_FFFF_FFFF, 1, ulong.MaxValue - 1);
        for (int pattern = 0; pattern < 81; pattern++)
        {
            int remaining = pattern;
            ulong Limb(ulong value)
            {
                int delta = remaining % 3 - 1;
                remaining /= 3;
                return delta < 0 ? value - 1 : value + (ulong)delta;
            }

            UInt256 left = new(Limb(right.u0), Limb(right.u1), Limb(right.u2), Limb(right.u3));
            AssertOperators(left, right);
            AssertOperators(right, left);
        }
    }

    private static void AssertOperators(UInt256 left, UInt256 right)
    {
        BigInteger a = (BigInteger)left, b = (BigInteger)right;
        Assert.That(left < right, Is.EqualTo(a < b));
        Assert.That(left <= right, Is.EqualTo(a <= b));
        Assert.That(left > right, Is.EqualTo(a > b));
        Assert.That(left >= right, Is.EqualTo(a >= b));
        Assert.That(left == right, Is.EqualTo(a == b));
        Assert.That(left != right, Is.EqualTo(a != b));
        Assert.That(left.Equals(in right), Is.EqualTo(a == b));
        Assert.That(Math.Sign(left.CompareTo(in right)), Is.EqualTo(a.CompareTo(b)));
    }

    [Test]
    public void Portable_vector_comparison_matches_all_paired_limb_patterns()
    {
        CompareBoth compare = typeof(UInt256)
            .GetMethod("LessThanBothVector256", BindingFlags.Static | BindingFlags.NonPublic)!
            .CreateDelegate<CompareBoth>();

        UInt256 modulus = new(1, 1, 1, 1);
        for (int pattern = 0; pattern < 6561; pattern++)
        {
            int remaining = pattern;
            ulong Limb()
            {
                ulong value = (ulong)(remaining % 3);
                remaining /= 3;
                return value;
            }

            UInt256 left = new(Limb(), Limb(), Limb(), Limb());
            UInt256 right = new(Limb(), Limb(), Limb(), Limb());
            bool expected = (BigInteger)left < (BigInteger)modulus && (BigInteger)right < (BigInteger)modulus;
            Assert.That(compare(in left, in right, in modulus), Is.EqualTo(expected), $"Pattern {pattern}");

            UInt256.AddMod(in left, in right, in modulus, out UInt256 actual);
            Assert.That((BigInteger)actual, Is.EqualTo(((BigInteger)left + (BigInteger)right) % (BigInteger)modulus));
        }
    }

    [Test]
    public void Primitive_equality_preserves_signed_and_unsigned_boundaries()
    {
        UInt256[] values = [UInt256.Zero, UInt256.One, new(uint.MaxValue), new(ulong.MaxValue), new(1, 1, 0, 0), UInt256.MaxValue];
        foreach (UInt256 value in values)
        {
            Assert.That(value == 0, Is.EqualTo(((BigInteger)value).IsZero));
            Assert.That(0 == value, Is.EqualTo(((BigInteger)value).IsZero));
            Assert.That(value != 0, Is.EqualTo(!((BigInteger)value).IsZero));
            Assert.That(0 != value, Is.EqualTo(!((BigInteger)value).IsZero));
            Assert.That(value == 1, Is.EqualTo((BigInteger)value == 1));
            Assert.That(1 == value, Is.EqualTo((BigInteger)value == 1));
            foreach (long other in new[] { long.MinValue, -1, 0, 1, long.MaxValue })
            {
                bool expected = (BigInteger)value == other;
                Assert.That(value.Equals(other), Is.EqualTo(expected));
                Assert.That(value == other, Is.EqualTo(expected));
                Assert.That(other == value, Is.EqualTo(expected));
                Assert.That(value != other, Is.EqualTo(!expected));
                Assert.That(other != value, Is.EqualTo(!expected));
            }

            foreach (ulong other in new[] { 0UL, 1UL, uint.MaxValue, (ulong)long.MaxValue, ulong.MaxValue })
            {
                bool expected = (BigInteger)value == other;
                Assert.That(value.Equals(other), Is.EqualTo(expected));
                Assert.That(value == other, Is.EqualTo(expected));
                Assert.That(other == value, Is.EqualTo(expected));
            }
        }
    }
}
