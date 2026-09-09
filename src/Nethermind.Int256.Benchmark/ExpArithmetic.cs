// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Numerics;
using BenchmarkDotNet.Attributes;

namespace Nethermind.Int256.Benchmark;

[IterationTime(100)]
[WarmupCount(3)]
[IterationCount(5)]
public class ExpArithmetic
{
    [Params("dense256", "sparse256", "zero-prefix", "three256")]
    public string Shape { get; set; } = "dense256";
    private UInt256 _base;
    private UInt256 _exponent;

    [GlobalSetup]
    public void Setup()
    {
        _base = new UInt256(3, 11, 13, 17);
        BigInteger exponent = (BigInteger.One << 256) - 1;
        switch (Shape)
        {
            case "sparse256": exponent = (BigInteger.One << 255) + 1; break;
            case "zero-prefix": exponent = BigInteger.One << 255; break;
            case "three256": _base = new UInt256(3); break;
        }
        _exponent = (UInt256)exponent;
    }

    [Benchmark(OperationsPerInvoke = 256)]
    public UInt256 Exp()
    {
        UInt256 result = default;
        for (int i = 0; i < 256; ++i) UInt256.Exp(_base, _exponent, out result);
        return result;
    }
}
