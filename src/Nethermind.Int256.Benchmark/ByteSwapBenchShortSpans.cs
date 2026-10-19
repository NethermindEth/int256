// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using BenchmarkDotNet.Attributes;

namespace Nethermind.Int256.Benchmark;

/// <summary>
/// The span constructor for lengths other than 32, which are read big-endian (minimal encodings such as RLP integers).
/// </summary>
/// <remarks>Named after <see cref="ByteSwapBench"/> so the CI filter <c>'*ByteSwapBench*'</c> runs both.</remarks>
public class ByteSwapBenchShortSpans
{
    private const int N = 16;

    private byte[] _bytes = [];

    [Params(1, 8, 9, 20, 31)]
    public int Length { get; set; }

    [GlobalSetup]
    public void Setup()
    {
        _bytes = new byte[Length];
        for (int i = 0; i < _bytes.Length; i++)
        {
            _bytes[i] = (byte)(0xC0 + i);
        }
    }

    [Benchmark(OperationsPerInvoke = N)]
    public UInt256 FromBigEndian()
    {
        UInt256 acc = default;
        for (int i = 0; i < N; i++)
        {
            acc ^= new UInt256(_bytes, isBigEndian: true);
        }
        return acc;
    }
}
