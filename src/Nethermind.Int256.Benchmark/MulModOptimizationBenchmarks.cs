// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using BenchmarkDotNet.Attributes;

namespace Nethermind.Int256.Benchmark;

public class MulModOptimizationBenchmarks
{
    private const int Count = 1024;
    private readonly UInt256[] _left = new UInt256[Count];
    private readonly UInt256[] _right = new UInt256[Count];
    private readonly UInt256[] _moduli = new UInt256[Count];

    [Params("full", "shift", "192", "192shift", "128", "128shift", "64", "max", "narrow", "pow64")]
    public string Shape { get; set; } = "full";

    [GlobalSetup]
    public void Setup()
    {
        Random random = new(567);
        ulong Next() => ((ulong)random.NextInt64() << 1) | (uint)random.Next(2);
        for (int i = 0; i < Count; i++)
        {
            _left[i] = new(Next(), Next(), Next(), Next());
            _right[i] = new(Next(), Next(), Next(), Next());
            _moduli[i] = Shape switch
            {
                "full" => new(Next(), Next(), Next(), Next() | (1UL << 63)),
                "shift" => new(Next(), Next(), Next(), (Next() >> 32) | 1),
                "192" => new(Next(), Next(), Next() | (1UL << 63), 0),
                "192shift" => new(Next(), Next(), (Next() >> 32) | 1, 0),
                "128" => new(Next(), Next() | (1UL << 63), 0, 0),
                "128shift" => new(Next(), (Next() >> 32) | 1, 0, 0),
                "64" => new(Next() | 1),
                "pow64" => new(1UL << (i % 63 + 1)),
                "max" => UInt256.MaxValue,
                _ => new(Next(), Next(), Next(), Next() | 1),
            };
            if (Shape == "narrow") _left[i] = new(Next());
        }
    }

    [Benchmark(OperationsPerInvoke = Count)]
    public ulong MultiplyMod()
    {
        ulong checksum = 0;
        for (int i = 0; i < Count; i++)
        {
            UInt256.MultiplyMod(in _left[i], in _right[i], in _moduli[i], out UInt256 result);
            checksum += result.u0;
        }
        return checksum;
    }
}
