// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Numerics;
using BenchmarkDotNet.Attributes;

namespace Nethermind.Int256.Benchmark;

[IterationTime(100)]
[WarmupCount(3)]
[IterationCount(5)]
public class StructuredExp
{
    [Params(16, 24, 31, 32, 43, 47, 48, 51, 52, 55, 56, 63)] public int Valuation { get; set; }
    [Params(33, 64, 96, 128)] public int Bits { get; set; }
    [Params(false, true)] public bool Dense { get; set; }
    private UInt256 _base;
    private UInt256 _exponent;

    [GlobalSetup]
    public void Setup()
    {
        _base = new UInt256(1 + (1UL << Valuation), 11, 13, 17);
        _exponent = (UInt256)(Dense ? (BigInteger.One << Bits) - 1 : (BigInteger.One << (Bits - 1)) + 1);
    }

    [Benchmark(OperationsPerInvoke = 256)]
    public UInt256 Exp()
    {
        UInt256 result = default;
        for (int i = 0; i < 256; ++i) UInt256.Exp(_base, _exponent, out result);
        return result;
    }
}
