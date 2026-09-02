// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

public partial class UInt256Tests
{
    [Test]
    public void CompareTo_Uses_the_first_differing_limb()
    {
        UInt256 common = new(0x0123_4567_89AB_CDEFUL, 0x1111_2222_3333_4444UL, 0x5555_6666_7777_8888UL, 0x9999_AAAA_BBBB_CCCCUL);

        AssertCompare(new UInt256(common.u0, common.u1, common.u2, common.u3 - 1), common, -1);
        AssertCompare(common, new UInt256(common.u0, common.u1, common.u2, common.u3 - 1), 1);
        AssertCompare(new UInt256(common.u0, common.u1, common.u2 - 1, common.u3), common, -1);
        AssertCompare(common, new UInt256(common.u0, common.u1, common.u2 - 1, common.u3), 1);
        AssertCompare(new UInt256(common.u0, common.u1 - 1, common.u2, common.u3), common, -1);
        AssertCompare(common, new UInt256(common.u0, common.u1 - 1, common.u2, common.u3), 1);
        AssertCompare(new UInt256(common.u0 - 1, common.u1, common.u2, common.u3), common, -1);
        AssertCompare(common, new UInt256(common.u0 - 1, common.u1, common.u2, common.u3), 1);
    }

    [Test]
    public void CompareTo_Matches_BigInteger()
    {
        UInt256[] values =
        [
            UInt256.Zero,
            UInt256.One,
            new UInt256(ulong.MaxValue),
            new UInt256(0, ulong.MaxValue, 0, 0),
            new UInt256(0, 0, ulong.MaxValue, 0),
            new UInt256(0, 0, 0, ulong.MaxValue),
            new UInt256(ulong.MaxValue, ulong.MaxValue, ulong.MaxValue, ulong.MaxValue),
        ];

        Random random = new(42);
        Array.Resize(ref values, values.Length + 128);
        for (int i = 7; i < values.Length; i++)
        {
            values[i] = new UInt256(
                (ulong)random.NextInt64(),
                (ulong)random.NextInt64(),
                (ulong)random.NextInt64(),
                (ulong)random.NextInt64());
        }

        foreach (UInt256 a in values)
        {
            foreach (UInt256 b in values)
            {
                int expected = Math.Sign(((BigInteger)a).CompareTo((BigInteger)b));
                Assert.That(Math.Sign(a.CompareTo(in b)), Is.EqualTo(expected));
                Assert.That(Math.Sign(a.CompareTo(b)), Is.EqualTo(expected));
                Assert.That(Math.Sign(a.CompareTo((object)b)), Is.EqualTo(expected));
            }
        }
    }

    private static void AssertCompare(UInt256 a, UInt256 b, int expected)
    {
        Assert.That(a.CompareTo(in b), Is.EqualTo(expected));
        Assert.That(a.CompareTo(b), Is.EqualTo(expected));
        Assert.That(a.CompareTo((object)b), Is.EqualTo(expected));
    }
}
