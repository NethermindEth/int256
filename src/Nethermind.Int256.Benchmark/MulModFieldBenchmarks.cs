// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Numerics;
using BenchmarkDotNet.Attributes;

namespace Nethermind.Int256.Benchmark;

// MULMOD with a full-width modulus (m >= 2^192), by how the modulus repeats and how wide the operands are.
// The BN254 and secp256k1 cases mirror contracts that reduce in one prime field (MiMC, Poseidon, EC arithmetic).
public class MulModFieldBenchmarks
{
    private const int Count = 1024;
    private readonly UInt256[] _left = new UInt256[Count];
    private readonly UInt256[] _right = new UInt256[Count];
    private readonly UInt256[] _moduli = new UInt256[Count];

    private static readonly UInt256 Bn254R = UInt256.Parse("21888242871839275222246405745257275088548364400416034343698204186575808495617");
    private static readonly UInt256 Bn254P = UInt256.Parse("21888242871839275222246405745257275088696311157297823662689037894645226208583");
    private static readonly UInt256 P256N = UInt256.Parse("115792089210356248762697446949407573529996955224135760342422259061068512044369");
    private static readonly UInt256 Secp256k1P = UInt256.Parse("115792089237316195423570985008687907853269984665640564039457584007908834671663");

    [Params("bn254", "bn254-hi1", "bn254-hi2", "secp256k1", "p256n", "fixed-full", "fixed-shift", "two-fields", "near-bn254", "varying-full", "varying-shift", "runs8")]
    public string Case { get; set; } = "bn254";

    [GlobalSetup]
    public void Setup()
    {
        Random random = new(0x4D554C);
        ulong Next() => ((ulong)random.NextInt64() << 1) | (uint)random.Next(2);
        UInt256 Full() => new(Next(), Next(), Next(), Next());
        UInt256 Below(in UInt256 m)
        {
            UInt256.Mod(Full(), m, out UInt256 r);
            return r;
        }

        UInt256 fixedFull = new(Next(), Next(), Next(), Next() | (1UL << 63));
        UInt256 fixedShift = new(Next(), Next(), Next(), (Next() >> 32) | 1);
        UInt256 runModulus = default;
        UInt256 nearBn254 = new(Bn254R.u0 ^ 2, Bn254R.u1, Bn254R.u2, Bn254R.u3);
        for (int i = 0; i < Count; i++)
        {
            if (i % 8 == 0) runModulus = new(Next(), Next(), Next(), Next() | 1);
            (_moduli[i], _left[i], _right[i]) = Case switch
            {
                "bn254" => (Bn254R, Below(Bn254R), Below(Bn254R)),
                "bn254-hi1" => (Bn254R, Below(Bn254R), new UInt256(Next())),
                "bn254-hi2" => (Bn254R, Below(Bn254R), new UInt256(Next(), Next(), 0, 0)),
                "secp256k1" => (Secp256k1P, Below(Secp256k1P), Below(Secp256k1P)),
                "p256n" => (P256N, Below(P256N), Below(P256N)),
                "near-bn254" => (nearBn254, Below(nearBn254), Below(nearBn254)),
                "fixed-full" => (fixedFull, Full(), Full()),
                "fixed-shift" => (fixedShift, Full(), Full()),
                "two-fields" => i % 2 == 0 ? (Bn254R, Below(Bn254R), Below(Bn254R)) : (Bn254P, Below(Bn254P), Below(Bn254P)),
                "varying-full" => (new UInt256(Next(), Next(), Next(), Next() | (1UL << 63)), Full(), Full()),
                "varying-shift" => (new UInt256(Next(), Next(), Next(), (Next() >> 32) | 1), Full(), Full()),
                "runs8" => (runModulus, Full(), Full()),
                _ => throw new ArgumentException(Case),
            };
        }

        // Fail fast if a reduction is wrong: a benchmark of a wrong result is worthless.
        for (int i = 0; i < Count; i++)
        {
            UInt256.MultiplyMod(in _left[i], in _right[i], in _moduli[i], out UInt256 r);
            BigInteger expected = (BigInteger)_left[i] * (BigInteger)_right[i] % (BigInteger)_moduli[i];
            if ((BigInteger)r != expected) throw new InvalidOperationException($"MultiplyMod mismatch at {i} for {Case}");
        }
    }

    [Benchmark(OperationsPerInvoke = Count)]
    public ulong Independent()
    {
        ulong checksum = 0;
        for (int i = 0; i < Count; i++)
        {
            UInt256.MultiplyMod(in _left[i], in _right[i], in _moduli[i], out UInt256 result);
            checksum += result.u0;
        }
        return checksum;
    }

    // Each product feeds the next, as in x^5 rounds: latency rather than throughput.
    [Benchmark(OperationsPerInvoke = Count)]
    public ulong Chained()
    {
        UInt256 x = _left[0];
        for (int i = 0; i < Count; i++)
        {
            UInt256.MultiplyMod(in x, in _right[i], in _moduli[i], out x);
        }
        return x.u0;
    }
}
