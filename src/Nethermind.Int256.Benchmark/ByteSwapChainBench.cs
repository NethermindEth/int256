// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Buffers.Binary;
using System.Runtime.CompilerServices;
using BenchmarkDotNet.Attributes;

namespace Nethermind.Int256.Benchmark;

/// <summary>
/// The 32-byte conversions in caller shapes: right after a value is computed, reading bytes just written, and
/// with the decoded value consumed at once. <see cref="ByteSwapBench"/> covers idle values.
/// </summary>
public class ByteSwapChainBench
{
    private const int N = 512;

    private UInt256[] _a = [];
    private UInt256[] _b = [];
    private UInt256[] _r = [];
    private byte[] _bytes = [];
    private byte[] _dst = [];

    [GlobalSetup]
    public void Setup()
    {
        Random rnd = new(42);
        _a = new UInt256[N];
        _b = new UInt256[N];
        _r = new UInt256[N];
        _bytes = new byte[N * 32];
        _dst = new byte[N * 32];
        rnd.NextBytes(_bytes);
        for (int i = 0; i < N; i++)
        {
            _a[i] = new UInt256((ulong)rnd.NextInt64(), (ulong)rnd.NextInt64(), (ulong)rnd.NextInt64(), (ulong)rnd.NextInt64());
            _b[i] = new UInt256((ulong)rnd.NextInt64(), (ulong)rnd.NextInt64(), (ulong)rnd.NextInt64(), (ulong)rnd.NextInt64());
        }
    }

    // Writes right after Multiply, which stores 8-byte limbs on ARM64.
    [Benchmark(OperationsPerInvoke = N)]
    public void MulToLE()
    {
        UInt256[] a = _a, b = _b;
        byte[] dst = _dst;
        for (int i = 0; i < N; i++)
        {
            UInt256.Multiply(in a[i], in b[i], out UInt256 t);
            t.ToLittleEndian(dst.AsSpan(i * 32, 32));
        }
    }

    // Add stores 16-byte halves on ARM64.
    [Benchmark(OperationsPerInvoke = N)]
    public void AddToLE()
    {
        UInt256[] a = _a, b = _b;
        byte[] dst = _dst;
        for (int i = 0; i < N; i++)
        {
            UInt256.Add(in a[i], in b[i], out UInt256 t);
            t.ToLittleEndian(dst.AsSpan(i * 32, 32));
        }
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void MulToBE()
    {
        UInt256[] a = _a, b = _b;
        byte[] dst = _dst;
        for (int i = 0; i < N; i++)
        {
            UInt256.Multiply(in a[i], in b[i], out UInt256 t);
            t.ToBigEndian(dst.AsSpan(i * 32, 32));
        }
    }

    // Reads consumed as limbs by a direct caller.
    [Benchmark(OperationsPerInvoke = N)]
    public ulong FromLE()
    {
        byte[] bytes = _bytes;
        ulong x0 = 0, x1 = 0, x2 = 0, x3 = 0;
        for (int i = 0; i < N; i++)
        {
            UInt256 v = new(bytes.AsSpan(i * 32, 32));
            x0 ^= v.u0; x1 ^= v.u1; x2 ^= v.u2; x3 ^= v.u3;
        }
        return x0 ^ x1 ^ x2 ^ x3;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public ulong FromBE()
    {
        byte[] bytes = _bytes;
        ulong x0 = 0, x1 = 0, x2 = 0, x3 = 0;
        for (int i = 0; i < N; i++)
        {
            UInt256 v = new(bytes.AsSpan(i * 32, 32), isBigEndian: true);
            x0 ^= v.u0; x1 ^= v.u1; x2 ^= v.u2; x3 ^= v.u3;
        }
        return x0 ^ x1 ^ x2 ^ x3;
    }

    // Reads of bytes just written by 8-byte stores.
    [Benchmark(OperationsPerInvoke = N)]
    public ulong WriteFromLE()
    {
        UInt256[] a = _a;
        byte[] buf = _dst;
        ulong acc = 0;
        for (int i = 0; i < N; i++)
        {
            Span<byte> slot = buf.AsSpan(i * 32, 32);
            BinaryPrimitives.WriteUInt64LittleEndian(slot, a[i].u0);
            BinaryPrimitives.WriteUInt64LittleEndian(slot[8..], a[i].u1);
            BinaryPrimitives.WriteUInt64LittleEndian(slot[16..], a[i].u2);
            BinaryPrimitives.WriteUInt64LittleEndian(slot[24..], a[i].u3);
            UInt256 v = new(slot);
            acc += v.u0 ^ v.u1 ^ v.u2 ^ v.u3;
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public ulong WriteFromBE()
    {
        UInt256[] a = _a;
        byte[] buf = _dst;
        ulong acc = 0;
        for (int i = 0; i < N; i++)
        {
            Span<byte> slot = buf.AsSpan(i * 32, 32);
            BinaryPrimitives.WriteUInt64BigEndian(slot, a[i].u3);
            BinaryPrimitives.WriteUInt64BigEndian(slot[8..], a[i].u2);
            BinaryPrimitives.WriteUInt64BigEndian(slot[16..], a[i].u1);
            BinaryPrimitives.WriteUInt64BigEndian(slot[24..], a[i].u0);
            UInt256 v = new(slot, isBigEndian: true);
            acc += v.u0 ^ v.u1 ^ v.u2 ^ v.u3;
        }
        return acc;
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static UInt256 DecodeLE(ReadOnlySpan<byte> s) => new(s);

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static UInt256 DecodeBE(ReadOnlySpan<byte> s) => new(s, isBigEndian: true);

    // Non-inlined decode, then Add.
    [Benchmark(OperationsPerInvoke = N)]
    public void DecodeLEAdd()
    {
        UInt256[] b = _b, r = _r;
        byte[] bytes = _bytes;
        for (int i = 0; i < N; i++)
        {
            UInt256 v = DecodeLE(bytes.AsSpan(i * 32, 32));
            UInt256.Add(in v, in b[i], out r[i]);
        }
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void DecodeBEAdd()
    {
        UInt256[] b = _b, r = _r;
        byte[] bytes = _bytes;
        for (int i = 0; i < N; i++)
        {
            UInt256 v = DecodeBE(bytes.AsSpan(i * 32, 32));
            UInt256.Add(in v, in b[i], out r[i]);
        }
    }

    // Non-inlined decode, then limb reads.
    [Benchmark(OperationsPerInvoke = N)]
    public ulong DecodeLELimbs()
    {
        byte[] bytes = _bytes;
        ulong acc = 0;
        for (int i = 0; i < N; i++)
        {
            UInt256 v = DecodeLE(bytes.AsSpan(i * 32, 32));
            acc += (v.u0 | v.u1) ^ (v.u2 | v.u3);
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public ulong DecodeBELimbs()
    {
        byte[] bytes = _bytes;
        ulong acc = 0;
        for (int i = 0; i < N; i++)
        {
            UInt256 v = DecodeBE(bytes.AsSpan(i * 32, 32));
            acc += (v.u0 | v.u1) ^ (v.u2 | v.u3);
        }
        return acc;
    }
}
