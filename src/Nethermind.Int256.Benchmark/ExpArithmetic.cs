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
public class ExpArithmetic
{
    [Params("dense256", "sparse256", "zero-prefix", "three256", "near32-dense", "near32-sparse", "near43-dense", "near43-sparse", "near47-dense", "near47-sparse", "near48-dense", "near48-sparse", "near51-sparse", "near52-sparse", "near55-sparse", "near56-sparse", "near63")]
    public string Shape { get; set; } = "dense256";
    private UInt256 _base;
    private UInt256 _exponent;

    [GlobalSetup]
    public void Setup()
    {
        byte[] il = typeof(UInt256).GetMethods(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static)
            .Where(m => m.Name.Contains("Exp", StringComparison.Ordinal))
            .OrderBy(m => m.Name, StringComparer.Ordinal)
            .SelectMany(m => m.GetMethodBody()?.GetILAsByteArray() ?? Array.Empty<byte>()).ToArray();
        Console.WriteLine($"EXP helper IL: {il.Length} bytes; SHA256={Convert.ToHexString(SHA256.HashData(il))}");
        _base = new UInt256(3, 11, 13, 17);
        BigInteger exponent = (BigInteger.One << 256) - 1;
        switch (Shape)
        {
            case "sparse256": exponent = (BigInteger.One << 255) + 1; break;
            case "zero-prefix": exponent = BigInteger.One << 255; break;
            case "three256": _base = new UInt256(3); break;
            case "near32-dense": _base = new UInt256(1UL + (1UL << 32), 11, 13, 17); exponent = (BigInteger.One << 96) - 1; break;
            case "near32-sparse": _base = new UInt256(1UL + (1UL << 32), 11, 13, 17); exponent = (BigInteger.One << 95) + 1; break;
            case "near43-dense": _base = new UInt256(1UL + (1UL << 43), 11, 13, 17); exponent = (BigInteger.One << 96) - 1; break;
            case "near43-sparse": _base = new UInt256(1UL + (1UL << 43), 11, 13, 17); exponent = (BigInteger.One << 95) + 1; break;
            case "near47-dense": _base = new UInt256(1UL + (1UL << 47), 11, 13, 17); exponent = (BigInteger.One << 96) - 1; break;
            case "near47-sparse": _base = new UInt256(1UL + (1UL << 47), 11, 13, 17); exponent = (BigInteger.One << 95) + 1; break;
            case "near48-dense": _base = new UInt256(1UL + (1UL << 48), 11, 13, 17); exponent = (BigInteger.One << 96) - 1; break;
            case "near48-sparse": _base = new UInt256(1UL + (1UL << 48), 11, 13, 17); exponent = (BigInteger.One << 95) + 1; break;
            case "near51-sparse": _base = new UInt256(1UL + (1UL << 51), 11, 13, 17); exponent = (BigInteger.One << 95) + 1; break;
            case "near52-sparse": _base = new UInt256(1UL + (1UL << 52), 11, 13, 17); exponent = (BigInteger.One << 95) + 1; break;
            case "near55-sparse": _base = new UInt256(1UL + (1UL << 55), 11, 13, 17); exponent = (BigInteger.One << 95) + 1; break;
            case "near56-sparse": _base = new UInt256(1UL + (1UL << 56), 11, 13, 17); exponent = (BigInteger.One << 95) + 1; break;
            case "near63": _base = new UInt256(1UL + (1UL << 63), 11, 13, 17); exponent = ulong.MaxValue; break;
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
