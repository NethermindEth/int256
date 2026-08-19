// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using BenchmarkDotNet.Attributes;

namespace Nethermind.Int256.Benchmark;

/// <summary>
/// Platform-neutral benchmark for the 32-byte big-endian read/write paths
/// (AVX2/AVX-512 on x86, AdvSimd on ARM64, scalar otherwise).
/// </summary>
/// <remarks>
/// Unlike <c>ToBigEndianAB</c>, whose setup throws without AVX2, this class runs on every ISA,
/// so it is safe for the ARM benchmark CI suite (<c>--filter '*ByteSwapBench*'</c>).
/// </remarks>
public class ByteSwapBench
{
    private const int N = 16;

    private byte[] _bigEndian = [];
    private readonly byte[] _target = new byte[32];
    private UInt256 _value;

    [GlobalSetup]
    public void Setup()
    {
        _bigEndian = new byte[32];
        for (int i = 0; i < _bigEndian.Length; i++)
        {
            _bigEndian[i] = (byte)(0xC0 + i);
        }
        _value = new UInt256(_bigEndian, isBigEndian: true);
    }

    [Benchmark(OperationsPerInvoke = N)]
    public UInt256 FromBigEndian()
    {
        UInt256 acc = default;
        for (int i = 0; i < N; i++)
        {
            acc ^= new UInt256(_bigEndian, isBigEndian: true);
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void ToBigEndian()
    {
        for (int i = 0; i < N; i++)
        {
            _value.ToBigEndian(_target);
        }
    }
}
