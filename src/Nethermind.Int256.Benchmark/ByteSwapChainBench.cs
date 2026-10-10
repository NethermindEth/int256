// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Runtime.CompilerServices;
using BenchmarkDotNet.Attributes;

namespace Nethermind.Int256.Benchmark;

/// <summary>
/// The 32-byte conversions in the shapes callers use them: right after a value is computed, reading bytes just
/// written, and with the decoded value consumed at once. <see cref="ByteSwapBench"/> only converts idle values.
/// </summary>
/// <remarks>
/// Every shape has three arms. <c>Prod</c> calls <see cref="UInt256"/>. <c>Cur</c> and <c>Old</c> call the
/// verbatim copies in ByteSwapCopies.cs: as shipped, and with the AdvSimd branches removed (what ARM64 ran before).
/// Prod matching Cur within the A/A spread shows the copies are faithful; Cur against Old is the AdvSimd effect.
/// On x64 Cur and Old run the same AVX code and act as a further A/A control.
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

        byte[] p = new byte[32], c = new byte[32], o = new byte[32];
        for (int i = 0; i < N; i++)
        {
            ReadOnlySpan<byte> src = _bytes.AsSpan(i * 32, 32);
            foreach (bool bigEndian in new[] { false, true })
            {
                UInt256 prod = new(src, bigEndian);
                U256Current cur = new(src, bigEndian);
                U256Old old = new(src, bigEndian);
                if (!prod.Equals(Unsafe.As<U256Current, UInt256>(ref cur)) || !prod.Equals(Unsafe.As<U256Old, UInt256>(ref old)))
                    throw new InvalidOperationException($"read mismatch at {i}, bigEndian={bigEndian}");

                if (bigEndian)
                {
                    prod.ToBigEndian(p);
                    cur.ToBigEndian(c);
                    old.ToBigEndian(o);
                }
                else
                {
                    prod.ToLittleEndian(p);
                    cur.ToLittleEndian(c);
                    old.ToLittleEndian(o);
                }
                if (!p.AsSpan().SequenceEqual(c) || !p.AsSpan().SequenceEqual(o) || !p.AsSpan().SequenceEqual(src))
                    throw new InvalidOperationException($"write mismatch at {i}, bigEndian={bigEndian}");
            }
        }
    }

    // ---- Writes of a value just computed. Multiply stores its product as four 8-byte limbs on ARM64.

    [Benchmark(Baseline = true, OperationsPerInvoke = N)]
    public void MulToLE_Prod()
    {
        UInt256[] a = _a, b = _b;
        byte[] dst = _dst;
        for (int i = 0; i < N; i++)
        {
            UInt256.Multiply(in a[i], in b[i], out UInt256 t);
            t.ToLittleEndian(dst.AsSpan(i * 32, 32));
        }
    }

    // A/A control for the baseline above.
    [Benchmark(OperationsPerInvoke = N)]
    public void MulToLE_ProdAA()
    {
        UInt256[] a = _a, b = _b;
        byte[] dst = _dst;
        for (int i = 0; i < N; i++)
        {
            UInt256.Multiply(in a[i], in b[i], out UInt256 t);
            t.ToLittleEndian(dst.AsSpan(i * 32, 32));
        }
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void MulToLE_Cur()
    {
        UInt256[] a = _a, b = _b;
        byte[] dst = _dst;
        for (int i = 0; i < N; i++)
        {
            UInt256.Multiply(in a[i], in b[i], out UInt256 t);
            Unsafe.As<UInt256, U256Current>(ref t).ToLittleEndian(dst.AsSpan(i * 32, 32));
        }
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void MulToLE_Old()
    {
        UInt256[] a = _a, b = _b;
        byte[] dst = _dst;
        for (int i = 0; i < N; i++)
        {
            UInt256.Multiply(in a[i], in b[i], out UInt256 t);
            Unsafe.As<UInt256, U256Old>(ref t).ToLittleEndian(dst.AsSpan(i * 32, 32));
        }
    }

    // ARM64 Add stores wide results as 16-byte halves.
    [Benchmark(OperationsPerInvoke = N)]
    public void AddToLE_Prod()
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
    public void AddToLE_Cur()
    {
        UInt256[] a = _a, b = _b;
        byte[] dst = _dst;
        for (int i = 0; i < N; i++)
        {
            UInt256.Add(in a[i], in b[i], out UInt256 t);
            Unsafe.As<UInt256, U256Current>(ref t).ToLittleEndian(dst.AsSpan(i * 32, 32));
        }
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void AddToLE_Old()
    {
        UInt256[] a = _a, b = _b;
        byte[] dst = _dst;
        for (int i = 0; i < N; i++)
        {
            UInt256.Add(in a[i], in b[i], out UInt256 t);
            Unsafe.As<UInt256, U256Old>(ref t).ToLittleEndian(dst.AsSpan(i * 32, 32));
        }
    }

    // Idle values, for comparison with ByteSwapBench.
    [Benchmark(OperationsPerInvoke = N)]
    public void IdleToLE_Prod()
    {
        UInt256[] a = _a;
        byte[] dst = _dst;
        for (int i = 0; i < N; i++) a[i].ToLittleEndian(dst.AsSpan(i * 32, 32));
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void IdleToLE_Cur()
    {
        UInt256[] a = _a;
        byte[] dst = _dst;
        for (int i = 0; i < N; i++) Unsafe.As<UInt256, U256Current>(ref a[i]).ToLittleEndian(dst.AsSpan(i * 32, 32));
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void IdleToLE_Old()
    {
        UInt256[] a = _a;
        byte[] dst = _dst;
        for (int i = 0; i < N; i++) Unsafe.As<UInt256, U256Old>(ref a[i]).ToLittleEndian(dst.AsSpan(i * 32, 32));
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void MulToBE_Prod()
    {
        UInt256[] a = _a, b = _b;
        byte[] dst = _dst;
        for (int i = 0; i < N; i++)
        {
            UInt256.Multiply(in a[i], in b[i], out UInt256 t);
            t.ToBigEndian(dst.AsSpan(i * 32, 32));
        }
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void MulToBE_Cur()
    {
        UInt256[] a = _a, b = _b;
        byte[] dst = _dst;
        for (int i = 0; i < N; i++)
        {
            UInt256.Multiply(in a[i], in b[i], out UInt256 t);
            Unsafe.As<UInt256, U256Current>(ref t).ToBigEndian(dst.AsSpan(i * 32, 32));
        }
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void MulToBE_Old()
    {
        UInt256[] a = _a, b = _b;
        byte[] dst = _dst;
        for (int i = 0; i < N; i++)
        {
            UInt256.Multiply(in a[i], in b[i], out UInt256 t);
            Unsafe.As<UInt256, U256Old>(ref t).ToBigEndian(dst.AsSpan(i * 32, 32));
        }
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void IdleToBE_Prod()
    {
        UInt256[] a = _a;
        byte[] dst = _dst;
        for (int i = 0; i < N; i++) a[i].ToBigEndian(dst.AsSpan(i * 32, 32));
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void IdleToBE_Cur()
    {
        UInt256[] a = _a;
        byte[] dst = _dst;
        for (int i = 0; i < N; i++) Unsafe.As<UInt256, U256Current>(ref a[i]).ToBigEndian(dst.AsSpan(i * 32, 32));
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void IdleToBE_Old()
    {
        UInt256[] a = _a;
        byte[] dst = _dst;
        for (int i = 0; i < N; i++) Unsafe.As<UInt256, U256Old>(ref a[i]).ToBigEndian(dst.AsSpan(i * 32, 32));
    }

    // ---- Reads consumed as limbs straight away, the ctor inlined (or not) as the JIT decides for a direct caller.

    [Benchmark(OperationsPerInvoke = N)]
    public ulong FromLE_Prod()
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
    public ulong FromLE_Cur()
    {
        byte[] bytes = _bytes;
        ulong x0 = 0, x1 = 0, x2 = 0, x3 = 0;
        for (int i = 0; i < N; i++)
        {
            U256Current v = new(bytes.AsSpan(i * 32, 32));
            x0 ^= v.u0; x1 ^= v.u1; x2 ^= v.u2; x3 ^= v.u3;
        }
        return x0 ^ x1 ^ x2 ^ x3;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public ulong FromLE_Old()
    {
        byte[] bytes = _bytes;
        ulong x0 = 0, x1 = 0, x2 = 0, x3 = 0;
        for (int i = 0; i < N; i++)
        {
            U256Old v = new(bytes.AsSpan(i * 32, 32));
            x0 ^= v.u0; x1 ^= v.u1; x2 ^= v.u2; x3 ^= v.u3;
        }
        return x0 ^ x1 ^ x2 ^ x3;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public ulong FromBE_Prod()
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

    [Benchmark(OperationsPerInvoke = N)]
    public ulong FromBE_Cur()
    {
        byte[] bytes = _bytes;
        ulong x0 = 0, x1 = 0, x2 = 0, x3 = 0;
        for (int i = 0; i < N; i++)
        {
            U256Current v = new(bytes.AsSpan(i * 32, 32), isBigEndian: true);
            x0 ^= v.u0; x1 ^= v.u1; x2 ^= v.u2; x3 ^= v.u3;
        }
        return x0 ^ x1 ^ x2 ^ x3;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public ulong FromBE_Old()
    {
        byte[] bytes = _bytes;
        ulong x0 = 0, x1 = 0, x2 = 0, x3 = 0;
        for (int i = 0; i < N; i++)
        {
            U256Old v = new(bytes.AsSpan(i * 32, 32), isBigEndian: true);
            x0 ^= v.u0; x1 ^= v.u1; x2 ^= v.u2; x3 ^= v.u3;
        }
        return x0 ^ x1 ^ x2 ^ x3;
    }

    // ---- Reads of bytes just written by 8-byte stores (the old scalar writer), as an encoder's buffer is decoded.

    [Benchmark(OperationsPerInvoke = N)]
    public ulong WriteFromLE_Prod()
    {
        UInt256[] a = _a;
        byte[] buf = _dst;
        ulong acc = 0;
        for (int i = 0; i < N; i++)
        {
            Span<byte> slot = buf.AsSpan(i * 32, 32);
            Unsafe.As<UInt256, U256Old>(ref a[i]).ToLittleEndian(slot);
            UInt256 v = new(slot);
            acc += v.u0 ^ v.u1 ^ v.u2 ^ v.u3;
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public ulong WriteFromLE_Cur()
    {
        UInt256[] a = _a;
        byte[] buf = _dst;
        ulong acc = 0;
        for (int i = 0; i < N; i++)
        {
            Span<byte> slot = buf.AsSpan(i * 32, 32);
            Unsafe.As<UInt256, U256Old>(ref a[i]).ToLittleEndian(slot);
            U256Current v = new(slot);
            acc += v.u0 ^ v.u1 ^ v.u2 ^ v.u3;
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public ulong WriteFromLE_Old()
    {
        UInt256[] a = _a;
        byte[] buf = _dst;
        ulong acc = 0;
        for (int i = 0; i < N; i++)
        {
            Span<byte> slot = buf.AsSpan(i * 32, 32);
            Unsafe.As<UInt256, U256Old>(ref a[i]).ToLittleEndian(slot);
            U256Old v = new(slot);
            acc += v.u0 ^ v.u1 ^ v.u2 ^ v.u3;
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
            Unsafe.As<UInt256, U256Old>(ref a[i]).ToBigEndian(slot);
            UInt256 v = new(slot, isBigEndian: true);
            acc += v.u0 ^ v.u1 ^ v.u2 ^ v.u3;
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public ulong WriteFromBE_Cur()
    {
        UInt256[] a = _a;
        byte[] buf = _dst;
        ulong acc = 0;
        for (int i = 0; i < N; i++)
        {
            Span<byte> slot = buf.AsSpan(i * 32, 32);
            Unsafe.As<UInt256, U256Old>(ref a[i]).ToBigEndian(slot);
            U256Current v = new(slot, isBigEndian: true);
            acc += v.u0 ^ v.u1 ^ v.u2 ^ v.u3;
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public ulong WriteFromBE_Old()
    {
        UInt256[] a = _a;
        byte[] buf = _dst;
        ulong acc = 0;
        for (int i = 0; i < N; i++)
        {
            Span<byte> slot = buf.AsSpan(i * 32, 32);
            Unsafe.As<UInt256, U256Old>(ref a[i]).ToBigEndian(slot);
            U256Old v = new(slot, isBigEndian: true);
            acc += v.u0 ^ v.u1 ^ v.u2 ^ v.u3;
        }
        return acc;
    }

    // ---- Reads returned from a non-inlined decoder and fed straight to Add (16-byte reloads on ARM64).

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static UInt256 ProdFromLE(ReadOnlySpan<byte> s) => new(s);

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static U256Current CurFromLE(ReadOnlySpan<byte> s) => new(s);

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static U256Old OldFromLE(ReadOnlySpan<byte> s) => new(s);

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static UInt256 ProdFromBE(ReadOnlySpan<byte> s) => new(s, isBigEndian: true);

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static U256Current CurFromBE(ReadOnlySpan<byte> s) => new(s, isBigEndian: true);

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static U256Old OldFromBE(ReadOnlySpan<byte> s) => new(s, isBigEndian: true);

    [Benchmark(OperationsPerInvoke = N)]
    public void DecodeLEAdd_Prod()
    {
        UInt256[] b = _b, r = _r;
        byte[] bytes = _bytes;
        for (int i = 0; i < N; i++)
        {
            UInt256 v = ProdFromLE(bytes.AsSpan(i * 32, 32));
            UInt256.Add(in v, in b[i], out r[i]);
        }
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void DecodeLEAdd_Cur()
    {
        UInt256[] b = _b, r = _r;
        byte[] bytes = _bytes;
        for (int i = 0; i < N; i++)
        {
            U256Current v = CurFromLE(bytes.AsSpan(i * 32, 32));
            UInt256.Add(in Unsafe.As<U256Current, UInt256>(ref v), in b[i], out r[i]);
        }
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void DecodeLEAdd_Old()
    {
        UInt256[] b = _b, r = _r;
        byte[] bytes = _bytes;
        for (int i = 0; i < N; i++)
        {
            U256Old v = OldFromLE(bytes.AsSpan(i * 32, 32));
            UInt256.Add(in Unsafe.As<U256Old, UInt256>(ref v), in b[i], out r[i]);
        }
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void DecodeBEAdd_Prod()
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
    public void DecodeBEAdd_Cur()
    {
        UInt256[] b = _b, r = _r;
        byte[] bytes = _bytes;
        for (int i = 0; i < N; i++)
        {
            U256Current v = CurFromBE(bytes.AsSpan(i * 32, 32));
            UInt256.Add(in Unsafe.As<U256Current, UInt256>(ref v), in b[i], out r[i]);
        }
    }

    [Benchmark(OperationsPerInvoke = N)]
    public void DecodeBEAdd_Old()
    {
        UInt256[] b = _b, r = _r;
        byte[] bytes = _bytes;
        for (int i = 0; i < N; i++)
        {
            U256Old v = OldFromBE(bytes.AsSpan(i * 32, 32));
            UInt256.Add(in Unsafe.As<U256Old, UInt256>(ref v), in b[i], out r[i]);
        }
    }

    // ---- The same non-inlined decoder, its result read back as 8-byte limbs.

    [Benchmark(OperationsPerInvoke = N)]
    public ulong DecodeLELimbs_Prod()
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

    [Benchmark(OperationsPerInvoke = N)]
    public ulong DecodeLELimbs_Cur()
    {
        byte[] bytes = _bytes;
        ulong acc = 0;
        for (int i = 0; i < N; i++)
        {
            U256Current v = CurFromLE(bytes.AsSpan(i * 32, 32));
            acc += (v.u0 | v.u1) ^ (v.u2 | v.u3);
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public ulong DecodeLELimbs_Old()
    {
        byte[] bytes = _bytes;
        ulong acc = 0;
        for (int i = 0; i < N; i++)
        {
            U256Old v = OldFromLE(bytes.AsSpan(i * 32, 32));
            acc += (v.u0 | v.u1) ^ (v.u2 | v.u3);
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public ulong DecodeBELimbs_Prod()
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
    public ulong DecodeBELimbs_Cur()
    {
        byte[] bytes = _bytes;
        ulong acc = 0;
        for (int i = 0; i < N; i++)
        {
            U256Current v = CurFromBE(bytes.AsSpan(i * 32, 32));
            acc += (v.u0 | v.u1) ^ (v.u2 | v.u3);
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public ulong DecodeBELimbs_Old()
    {
        byte[] bytes = _bytes;
        ulong acc = 0;
        for (int i = 0; i < N; i++)
        {
            U256Old v = OldFromBE(bytes.AsSpan(i * 32, 32));
            acc += (v.u0 | v.u1) ^ (v.u2 | v.u3);
        }
        return acc;
    }
}
