// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Runtime.CompilerServices;
using BenchmarkDotNet.Attributes;

namespace Nethermind.Int256.Benchmark;

/// <summary>
/// MULMOD by the full-width moduli that the standard build reduces by Barrett reduction with constant reciprocals,
/// plus a random full-width modulus that divides.
/// </summary>
[MemoryDiagnoser]
public class BarrettModulusBench
{
    private const int Count = 1024;

    private readonly UInt256[] _x = new UInt256[Count];
    private readonly UInt256[] _y = new UInt256[Count];
    private readonly UInt256[] _m = new UInt256[Count];

    [Params("Secp256k1P", "Secp256k1N", "P256P", "P256N", "Bn254R", "RandomFullWidth")]
    public string Shape { get; set; } = "P256P";

    [GlobalSetup]
    public void Setup()
    {
        Random random = new(0x2ED0);
        for (int i = 0; i < Count; i++)
        {
            UInt256 x = Random256(random);
            UInt256 y = Random256(random);
            UInt256 m = Shape switch
            {
                "Secp256k1P" => Hex("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f"),
                "Secp256k1N" => Hex("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141"),
                "P256P" => Hex("ffffffff00000001000000000000000000000000ffffffffffffffffffffffff"),
                "P256N" => Hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551"),
                "Bn254R" => Hex("30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001"),
                _ => Random256(random) | (UInt256.One << 255),
            };

            UInt256.Mod(in x, in m, out x);
            UInt256.Mod(in y, in m, out y);
            _x[i] = x;
            _y[i] = y;
            _m[i] = m;
        }
    }

    [Benchmark(OperationsPerInvoke = Count)]
    public ulong MultiplyMod()
    {
        ulong acc = 0;
        for (int i = 0; i < Count; i++)
        {
            MultiplyMod(in _x[i], in _y[i], in _m[i], out UInt256 r);
            acc ^= r.u0 ^ r.u3;
        }
        return acc;
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void MultiplyMod(in UInt256 x, in UInt256 y, in UInt256 m, out UInt256 res)
        => UInt256.MultiplyMod(in x, in y, in m, out res);

    private static UInt256 Hex(string value) => new(Convert.FromHexString(value), isBigEndian: true);

    private static UInt256 Random256(Random random)
    {
        Span<byte> bytes = stackalloc byte[32];
        random.NextBytes(bytes);
        return new UInt256(bytes, isBigEndian: false);
    }
}
