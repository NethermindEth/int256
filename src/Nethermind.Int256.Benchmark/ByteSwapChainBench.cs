// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Buffers.Binary;
using System.Runtime.CompilerServices;
using BenchmarkDotNet.Attributes;

namespace Nethermind.Int256.Benchmark;

/// <summary>
/// The 32-byte conversions inside producer/consumer chains, against the scalar code ARM64 ran before its
/// AdvSimd paths. <see cref="ByteSwapBench"/> converts an idle value; here the value has just been computed
/// (or the bytes just written), so a 16-byte access over 8-byte stores has to forward or wait.
/// </summary>
/// <remarks>
/// Production and replica each sit behind one non-inlined wrapper, so both see the value in memory as
/// out-of-line callers do. Runs on every ISA; on x64 "Prod" is the AVX/AVX2 path.
/// </remarks>
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

        Span<byte> prod = stackalloc byte[32];
        Span<byte> replica = stackalloc byte[32];
        for (int i = 0; i < N; i++)
        {
            ReadOnlySpan<byte> src = _bytes.AsSpan(i * 32, 32);
            UInt256 v = ProdFromLE(src);
            if (!v.Equals(ScalarFromLE(src))) throw new InvalidOperationException($"FromLE mismatch at {i}");
            ProdToLE(in v, prod);
            ScalarToLE(in v, replica);
            if (!prod.SequenceEqual(replica) || !prod.SequenceEqual(src)) throw new InvalidOperationException($"ToLE mismatch at {i}");
            ProdToBE(in v, prod);
            ScalarToBE(in v, replica);
            if (!prod.SequenceEqual(replica)) throw new InvalidOperationException($"ToBE mismatch at {i}");
            if (!ProdFromBE(src).Equals(ScalarFromBE(src))) throw new InvalidOperationException($"FromBE mismatch at {i}");
        }
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void ProdToLE(in UInt256 v, Span<byte> dst) => v.ToLittleEndian(dst);

    // The pre-AdvSimd ARM64 body of ToLittleEndian(Span<byte>).
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void ScalarToLE(in UInt256 v, Span<byte> target)
    {
        BinaryPrimitives.WriteUInt64LittleEndian(target.Slice(0, 8), v.u0);
        BinaryPrimitives.WriteUInt64LittleEndian(target.Slice(8, 8), v.u1);
        BinaryPrimitives.WriteUInt64LittleEndian(target.Slice(16, 8), v.u2);
        BinaryPrimitives.WriteUInt64LittleEndian(target.Slice(24, 8), v.u3);
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void ProdToBE(in UInt256 v, Span<byte> dst) => v.ToBigEndian(dst);

    // The pre-AdvSimd ARM64 body of ToBigEndian(Span<byte>) for 32 bytes.
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void ScalarToBE(in UInt256 v, Span<byte> target)
    {
        BinaryPrimitives.WriteUInt64BigEndian(target.Slice(0, 8), v.u3);
        BinaryPrimitives.WriteUInt64BigEndian(target.Slice(8, 8), v.u2);
        BinaryPrimitives.WriteUInt64BigEndian(target.Slice(16, 8), v.u1);
        BinaryPrimitives.WriteUInt64BigEndian(target.Slice(24, 8), v.u0);
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static UInt256 ProdFromLE(ReadOnlySpan<byte> src) => new(src);

    // The pre-AdvSimd ARM64 body of the little-endian UInt256(ReadOnlySpan<byte>) ctor.
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static UInt256 ScalarFromLE(ReadOnlySpan<byte> bytes)
        => new(BinaryPrimitives.ReadUInt64LittleEndian(bytes.Slice(0, 8)),
            BinaryPrimitives.ReadUInt64LittleEndian(bytes.Slice(8, 8)),
            BinaryPrimitives.ReadUInt64LittleEndian(bytes.Slice(16, 8)),
            BinaryPrimitives.ReadUInt64LittleEndian(bytes.Slice(24, 8)));

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static UInt256 ProdFromBE(ReadOnlySpan<byte> src) => new(src, isBigEndian: true);

    // The pre-AdvSimd ARM64 body of the big-endian UInt256(ReadOnlySpan<byte>, true) ctor.
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static UInt256 ScalarFromBE(ReadOnlySpan<byte> bytes)
        => new(BinaryPrimitives.ReadUInt64BigEndian(bytes.Slice(24, 8)),
            BinaryPrimitives.ReadUInt64BigEndian(bytes.Slice(16, 8)),
            BinaryPrimitives.ReadUInt64BigEndian(bytes.Slice(8, 8)),
            BinaryPrimitives.ReadUInt64BigEndian(bytes.Slice(0, 8)));

    // Multiply stores its product as four 8-byte limbs on ARM64: the worst case for a 16-byte reload.
    [Benchmark(Baseline = true, OperationsPerInvoke = N)]
    public void MulToLE_Scalar()
    {
        UInt256[] a = _a, b = _b;
        byte[] dst = _dst;
        for (int i = 0; i < N; i++)
        {
            UInt256.Multiply(in a[i], in b[i], out UInt256 t);
            ScalarToLE(in t, dst.AsSpan(i * 32, 32));
        }
    }

    // A/A control for the baseline above.
    [Benchmark(OperationsPerInvoke = N)]
    public void MulToLE_ScalarAA()
    {
        UInt256[] a = _a, b = _b;
        byte[] dst = _dst;
        for (int i = 0; i < N; i++)
        {
            UInt256.Multiply(in a[i], in b[i], out UInt256 t);
            ScalarToLE(in t, dst.AsSpan(i * 32, 32));
        }
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void MulToLE_Prod()
    {
        UInt256[] a = _a, b = _b;
        byte[] dst = _dst;
        for (int i = 0; i < N; i++)
        {
            UInt256.Multiply(in a[i], in b[i], out UInt256 t);
            ProdToLE(in t, dst.AsSpan(i * 32, 32));
        }
    }

    // ARM64 Add stores wide results as 16-byte halves.
    [Benchmark(OperationsPerInvoke = N)]
    public void AddToLE_Scalar()
    {
        UInt256[] a = _a, b = _b;
        byte[] dst = _dst;
        for (int i = 0; i < N; i++)
        {
            UInt256.Add(in a[i], in b[i], out UInt256 t);
            ScalarToLE(in t, dst.AsSpan(i * 32, 32));
        }
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void AddToLE_Prod()
    {
        UInt256[] a = _a, b = _b;
        byte[] dst = _dst;
        for (int i = 0; i < N; i++)
        {
            UInt256.Add(in a[i], in b[i], out UInt256 t);
            ProdToLE(in t, dst.AsSpan(i * 32, 32));
        }
    }

    // The existing AdvSimd big-endian write (#102) has the same reload pattern.
    [Benchmark(OperationsPerInvoke = N)]
    public void MulToBE_Scalar()
    {
        UInt256[] a = _a, b = _b;
        byte[] dst = _dst;
        for (int i = 0; i < N; i++)
        {
            UInt256.Multiply(in a[i], in b[i], out UInt256 t);
            ScalarToBE(in t, dst.AsSpan(i * 32, 32));
        }
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void MulToBE_Prod()
    {
        UInt256[] a = _a, b = _b;
        byte[] dst = _dst;
        for (int i = 0; i < N; i++)
        {
            UInt256.Multiply(in a[i], in b[i], out UInt256 t);
            ProdToBE(in t, dst.AsSpan(i * 32, 32));
        }
    }

    // Bytes written by 8-byte stores just before the read, as an encoder writes a buffer it then decodes.
    [Benchmark(OperationsPerInvoke = N)]
    public ulong WriteFromLE_Scalar()
    {
        UInt256[] a = _a;
        byte[] buf = _dst;
        ulong acc = 0;
        for (int i = 0; i < N; i++)
        {
            Span<byte> slot = buf.AsSpan(i * 32, 32);
            ScalarToLE(in a[i], slot);
            UInt256 v = ScalarFromLE(slot);
            acc += v.u0 ^ v.u3;
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public ulong WriteFromLE_Prod()
    {
        UInt256[] a = _a;
        byte[] buf = _dst;
        ulong acc = 0;
        for (int i = 0; i < N; i++)
        {
            Span<byte> slot = buf.AsSpan(i * 32, 32);
            ScalarToLE(in a[i], slot);
            UInt256 v = ProdFromLE(slot);
            acc += v.u0 ^ v.u3;
        }
        return acc;
    }

    // The decoded value feeds an arithmetic op straight away (Add reloads it as 16-byte halves on ARM64).
    [Benchmark(OperationsPerInvoke = N)]
    public void FromLEAdd_Scalar()
    {
        UInt256[] b = _b, r = _r;
        byte[] bytes = _bytes;
        for (int i = 0; i < N; i++)
        {
            UInt256 v = ScalarFromLE(bytes.AsSpan(i * 32, 32));
            UInt256.Add(in v, in b[i], out r[i]);
        }
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void FromLEAdd_Prod()
    {
        UInt256[] b = _b, r = _r;
        byte[] bytes = _bytes;
        for (int i = 0; i < N; i++)
        {
            UInt256 v = ProdFromLE(bytes.AsSpan(i * 32, 32));
            UInt256.Add(in v, in b[i], out r[i]);
        }
    }

    // The decoded value is read back as 8-byte limbs.
    [Benchmark(OperationsPerInvoke = N)]
    public ulong FromLELimbs_Scalar()
    {
        byte[] bytes = _bytes;
        ulong acc = 0;
        for (int i = 0; i < N; i++)
        {
            UInt256 v = ScalarFromLE(bytes.AsSpan(i * 32, 32));
            acc += (v.u0 | v.u1) ^ (v.u2 | v.u3);
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public ulong FromLELimbs_Prod()
    {
        byte[] bytes = _bytes;
        ulong acc = 0;
        for (int i = 0; i < N; i++)
        {
            UInt256 v = ProdFromLE(bytes.AsSpan(i * 32, 32));
            acc += (v.u0 | v.u1) ^ (v.u2 | v.u3);
        }
        return acc;
    }

    // ByteSwapBench's shape, without wrappers: the JIT decides inlining as for a direct caller.
    [Benchmark(OperationsPerInvoke = N)]
    public UInt256 FromLEXor_Scalar()
    {
        byte[] bytes = _bytes;
        UInt256 acc = default;
        for (int i = 0; i < N; i++)
        {
            ReadOnlySpan<byte> s = bytes.AsSpan(i * 32, 32);
            acc ^= new UInt256(BinaryPrimitives.ReadUInt64LittleEndian(s.Slice(0, 8)),
                BinaryPrimitives.ReadUInt64LittleEndian(s.Slice(8, 8)),
                BinaryPrimitives.ReadUInt64LittleEndian(s.Slice(16, 8)),
                BinaryPrimitives.ReadUInt64LittleEndian(s.Slice(24, 8)));
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public UInt256 FromLEXor_Prod()
    {
        byte[] bytes = _bytes;
        UInt256 acc = default;
        for (int i = 0; i < N; i++)
        {
            acc ^= new UInt256(bytes.AsSpan(i * 32, 32));
        }
        return acc;
    }

    // The existing AdvSimd big-endian read (#102) stores its result the same way as the LE read.
    [Benchmark(OperationsPerInvoke = N)]
    public ulong WriteFromBE_Scalar()
    {
        UInt256[] a = _a;
        byte[] buf = _dst;
        ulong acc = 0;
        for (int i = 0; i < N; i++)
        {
            Span<byte> slot = buf.AsSpan(i * 32, 32);
            ScalarToBE(in a[i], slot);
            UInt256 v = ScalarFromBE(slot);
            acc += v.u0 ^ v.u3;
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public ulong WriteFromBE_Prod()
    {
        UInt256[] a = _a;
        byte[] buf = _dst;
        ulong acc = 0;
        for (int i = 0; i < N; i++)
        {
            Span<byte> slot = buf.AsSpan(i * 32, 32);
            ScalarToBE(in a[i], slot);
            UInt256 v = ProdFromBE(slot);
            acc += v.u0 ^ v.u3;
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void FromBEAdd_Scalar()
    {
        UInt256[] b = _b, r = _r;
        byte[] bytes = _bytes;
        for (int i = 0; i < N; i++)
        {
            UInt256 v = ScalarFromBE(bytes.AsSpan(i * 32, 32));
            UInt256.Add(in v, in b[i], out r[i]);
        }
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void FromBEAdd_Prod()
    {
        UInt256[] b = _b, r = _r;
        byte[] bytes = _bytes;
        for (int i = 0; i < N; i++)
        {
            UInt256 v = ProdFromBE(bytes.AsSpan(i * 32, 32));
            UInt256.Add(in v, in b[i], out r[i]);
        }
    }

    [Benchmark(OperationsPerInvoke = N)]
    public ulong FromBELimbs_Scalar()
    {
        byte[] bytes = _bytes;
        ulong acc = 0;
        for (int i = 0; i < N; i++)
        {
            UInt256 v = ScalarFromBE(bytes.AsSpan(i * 32, 32));
            acc += (v.u0 | v.u1) ^ (v.u2 | v.u3);
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public ulong FromBELimbs_Prod()
    {
        byte[] bytes = _bytes;
        ulong acc = 0;
        for (int i = 0; i < N; i++)
        {
            UInt256 v = ProdFromBE(bytes.AsSpan(i * 32, 32));
            acc += (v.u0 | v.u1) ^ (v.u2 | v.u3);
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public UInt256 FromBEXor_Scalar()
    {
        byte[] bytes = _bytes;
        UInt256 acc = default;
        for (int i = 0; i < N; i++)
        {
            ReadOnlySpan<byte> s = bytes.AsSpan(i * 32, 32);
            acc ^= new UInt256(BinaryPrimitives.ReadUInt64BigEndian(s.Slice(24, 8)),
                BinaryPrimitives.ReadUInt64BigEndian(s.Slice(16, 8)),
                BinaryPrimitives.ReadUInt64BigEndian(s.Slice(8, 8)),
                BinaryPrimitives.ReadUInt64BigEndian(s.Slice(0, 8)));
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public UInt256 FromBEXor_Prod()
    {
        byte[] bytes = _bytes;
        UInt256 acc = default;
        for (int i = 0; i < N; i++)
        {
            acc ^= new UInt256(bytes.AsSpan(i * 32, 32), isBigEndian: true);
        }
        return acc;
    }
}
