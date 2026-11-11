// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Numerics;
using NUnit.Framework;

namespace Nethermind.Int256.Test;

/// <summary>
/// Covers the explicit conversion from <see cref="double"/> to <see cref="UInt256"/> on doubles next to the limb
/// boundaries. Every double from 1 up is an integer times a power of two, so the expected value is exact.
/// </summary>
[Parallelizable(ParallelScope.All)]
public class DoubleConversionBoundaryTests
{
    private static IEnumerable<double> Values()
    {
        foreach (int bit in new[] { 52, 53, 63, 64, 65, 127, 128, 129, 191, 192, 193, 255 })
        {
            double power = Math.ScaleB(1, bit);
            yield return Math.BitDecrement(power);
            yield return power;
            yield return Math.BitIncrement(power);
            yield return power * 1.5;
        }

        yield return Math.BitDecrement(Math.ScaleB(1, 256));
        yield return ulong.MaxValue;
        yield return (double)ulong.MaxValue - 2048;
    }

    [TestCaseSource(nameof(Values))]
    public void Converts_exactly(double value)
    {
        Assert.That((BigInteger)(UInt256)value, Is.EqualTo(new BigInteger(value)));
    }
}
