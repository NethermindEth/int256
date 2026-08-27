// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

public partial class UInt256Tests
{
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
}
