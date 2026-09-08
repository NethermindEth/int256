// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Linq;
using System.Numerics;
using System.Reflection;
using System.Security.Cryptography;
using BenchmarkDotNet.Attributes;

namespace Nethermind.Int256.Benchmark;

[IterationTime(100)]
[WarmupCount(3)]
[IterationCount(5)]
public class StructuredExp
{
    [Params(16, 24, 31, 32, 48, 63)] public int Valuation { get; set; }
    [Params(33, 64, 96, 128)] public int Bits { get; set; }
    [Params(false, true)] public bool Dense { get; set; }
    private UInt256 _base;
    private UInt256 _exponent;

    [GlobalSetup]
    public void Setup()
    {
        byte[] il = typeof(UInt256).GetMethods(BindingFlags.Public | BindingFlags.Static)
            .Single(m => m.Name == nameof(UInt256.Exp) && m.GetParameters().Length == 3)
            .GetMethodBody()!.GetILAsByteArray()!;
        Console.WriteLine($"EXP IL: {il.Length} bytes; SHA256={Convert.ToHexString(SHA256.HashData(il))}");
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
