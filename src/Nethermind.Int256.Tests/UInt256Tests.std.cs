// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using NUnit.Framework;

namespace Nethermind.Int256.Test;

public partial class UInt256Tests
{
    [TestCase(0L)]
    [TestCase(1L)]
    [TestCase(0x00000000DEADBEEFL)]
    public void GetHashCode_RandomizedFallbackMaintainsDistribution(long seed)
        => AssertHashCodesAreDistributed(
            value => new UInt256(0, 0, 0, (uint)value).GetXxHashCode(seed),
            $"randomized fallback for seed {seed}");
}
