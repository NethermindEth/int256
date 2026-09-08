// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using BenchmarkDotNet.Attributes;

namespace Nethermind.Int256.Benchmark;

// -1 changes the runtime exponent; the other cases isolate each decimal count.
[IterationTime(100)]
[WarmupCount(3)]
[IterationCount(5)]
public class DecimalExp
{
    [Params(-1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18)]
    public int Decimals { get; set; }

    private readonly UInt256[] _exponents = new UInt256[256];
    private UInt256 _base = new(10);

    [GlobalSetup]
    public void Setup()
    {
        for (int i = 0; i < _exponents.Length; ++i)
            _exponents[i] = new((ulong)(Decimals < 0 ? i % 19 : Decimals));
        new Random(1337).Shuffle(_exponents);
    }

    [Benchmark(OperationsPerInvoke = 256)]
    public UInt256 Exp()
    {
        UInt256 result = default;
        for (int i = 0; i < _exponents.Length; ++i)
            UInt256.Exp(_base, _exponents[i], out result);
        return result;
    }
}
