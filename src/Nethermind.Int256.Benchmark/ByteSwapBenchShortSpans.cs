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
    private byte[] _target = [];
    private UInt256 _value;

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
        _target = new byte[Length];
        _value = new UInt256(0xC0C1C2C3C4C5C6C7, 0xC8C9CACBCCCDCECF, 0xD0D1D2D3D4D5D6D7, 0xD8D9DADBDCDDDEDF);
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

    [Benchmark(OperationsPerInvoke = N)]
    public void WritePaddedBytes()
    {
        for (int i = 0; i < N; i++)
        {
            _value.WritePaddedBytes(_target);
        }
    }
}
