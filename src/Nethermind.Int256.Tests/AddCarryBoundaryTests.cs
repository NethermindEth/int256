// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

public class AddCarryBoundaryTests
{
    [Test]
    public void Carry_states_and_aliases_match_BigInteger()
    {
        (ulong A, ulong B)[] limbs =
        [
            (0, 0),
            (ulong.MaxValue, 0),
            (ulong.MaxValue, 1),
            (1UL << 63, 1UL << 63),
            (1, ulong.MaxValue - 1),
            (ulong.MaxValue, ulong.MaxValue),
            (ulong.MaxValue - 1, 0)
        ];

        int combinations = limbs.Length * limbs.Length * limbs.Length * limbs.Length;
        for (int pattern = 0; pattern < combinations; pattern++)
        {
            int value = pattern;
            ulong[] a = new ulong[4], b = new ulong[4];
            for (int limb = 0; limb < 4; limb++, value /= limbs.Length)
                (a[limb], b[limb]) = limbs[value % limbs.Length];

            UInt256 x = new(a[0], a[1], a[2], a[3]);
            UInt256 y = new(b[0], b[1], b[2], b[3]);
            Check(x, y);
            Check(y, x);
            CheckAllAliases(x);
        }
    }

    private static void Check(UInt256 a, UInt256 b)
    {
        BigInteger sum = (BigInteger)a + (BigInteger)b;
        UInt256 expected = (UInt256)(sum & ((BigInteger.One << 256) - 1));
        bool expectedOverflow = sum >> 256 != 0;

        Assert.That(a + b, Is.EqualTo(expected));
        a.Add(b, out UInt256 instanceResult);
        Assert.That(instanceResult, Is.EqualTo(expected));
        UInt256 instanceAlias = a;
        instanceAlias.Add(b, out instanceAlias);
        Assert.That(instanceAlias, Is.EqualTo(expected));
        Int256.Add(new Int256(a), new Int256(b), out Int256 signedResult);
        Assert.That(signedResult, Is.EqualTo(new Int256(expected)));
        UInt256 incremented = a;
        incremented++;
        Assert.That(incremented, Is.EqualTo((UInt256)(((BigInteger)a + 1) & ((BigInteger.One << 256) - 1))));


        UInt256.Add(a, b, out UInt256 result);
        Assert.That(result, Is.EqualTo(expected));
        UInt256 left = a, right = b;
        UInt256.Add(left, b, out left);
        UInt256.Add(a, right, out right);
        Assert.That(left, Is.EqualTo(expected));
        Assert.That(right, Is.EqualTo(expected));

        Assert.That(UInt256.AddOverflow(a, b, out result), Is.EqualTo(expectedOverflow));
        Assert.That(result, Is.EqualTo(expected));
        left = a;
        right = b;
        Assert.That(UInt256.AddOverflow(left, b, out left), Is.EqualTo(expectedOverflow));
        Assert.That(UInt256.AddOverflow(a, right, out right), Is.EqualTo(expectedOverflow));
        Assert.That(left, Is.EqualTo(expected));
        Assert.That(right, Is.EqualTo(expected));
    }

    private static void CheckAllAliases(UInt256 value)
    {
        BigInteger sum = (BigInteger)value * 2;
        UInt256 expected = (UInt256)(sum & ((BigInteger.One << 256) - 1));
        UInt256 result = value;
        UInt256.Add(result, result, out result);
        Assert.That(result, Is.EqualTo(expected));
        result = value;
        Assert.That(UInt256.AddOverflow(result, result, out result), Is.EqualTo(sum >> 256 != 0));
        Assert.That(result, Is.EqualTo(expected));
    }
}
