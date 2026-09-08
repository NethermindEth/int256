// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

public class MultiplyOverflowBoundaryTests
{
    [Test]
    public void Products_near_width_and_overflow_boundaries_preserve_aliases()
    {
        BigInteger mask = (BigInteger.One << 256) - 1;
        int[] bits = [0, 1, 31, 32, 63, 64, 65, 95, 127, 128, 129, 191, 192, 193, 255];
        foreach (int bit in bits)
        foreach (int offset in new[] { -1, 0, 1 })
        {
            BigInteger a = (BigInteger.One << bit) + offset;
            foreach (int otherBit in bits)
            foreach (int otherOffset in new[] { -1, 0, 1 })
                Check(a, (BigInteger.One << otherBit) + otherOffset);
            if (a != 0)
                for (int delta = -1; delta <= 1; delta++)
                    Check(a, BigInteger.Min(mask, mask / a + delta));
            Check(a, a);
        }

        void Check(BigInteger a, BigInteger b)
        {
            if (b < 0) return;
            UInt256 x = (UInt256)a, y = (UInt256)b;
            UInt256 expected = (UInt256)((a * b) & mask);
            bool expectedOverflow = a * b > mask;
            UInt256 left = x, right = y;
            bool actual = UInt256.MultiplyOverflow(in x, in y, out UInt256 result);
            bool aliasLeft = UInt256.MultiplyOverflow(in left, in y, out left);
            bool aliasRight = UInt256.MultiplyOverflow(in x, in right, out right);
            Assert.That(actual == expectedOverflow && aliasLeft == expectedOverflow && aliasRight == expectedOverflow
                && result == expected && left == expected && right == expected, Is.True, $"{a} * {b}");
            UInt256.Multiply(in x, in y, out result);
            Assert.That(result, Is.EqualTo(expected));
            if (a == b)
            {
                left = x;
                actual = UInt256.MultiplyOverflow(in left, in left, out left);
                Assert.That(actual == expectedOverflow && left == expected, Is.True, "All three arguments alias");
            }
        }
    }
}
