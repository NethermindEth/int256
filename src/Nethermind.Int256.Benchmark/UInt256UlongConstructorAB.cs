// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Jobs;

namespace Nethermind.Int256.Benchmark;

[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 3, warmupCount: 3, iterationCount: 10)]
[NoIntrinsicsJob(RuntimeMoniker.Net10_0, launchCount: 3, warmupCount: 3, iterationCount: 10)]
public class UInt256UlongConstructorAB
{
    private const int N = 4096;

    private readonly ulong[] _u0 = new ulong[N];
    private readonly ulong[] _u1 = new ulong[N];
    private readonly ulong[] _u2 = new ulong[N];
    private readonly ulong[] _u3 = new ulong[N];

    [GlobalSetup]
    public void Setup()
    {
        (ulong U0, ulong U1, ulong U2, ulong U3)[] values =
        [
            (0, 0, 0, 0),
            (ulong.MaxValue, 0, 0, 0),
            (0, ulong.MaxValue, 0, 0),
            (0, 0, ulong.MaxValue, 0),
            (0, 0, 0, ulong.MaxValue),
            (0x0123_4567_89AB_CDEF, 0xFEDC_BA98_7654_3210, 0x8000_0000_0000_0000, 1),
            (ulong.MaxValue, ulong.MaxValue, ulong.MaxValue, ulong.MaxValue),
            (0x8000_0000_0000_0001, 0x7FFF_FFFF_FFFF_FFFE, 0xDEAD_BEEF_CAFE_BABE, 0x1357_9BDF_2468_ACE0),
        ];

        for (int i = 0; i < N; i++)
        {
            (ulong U0, ulong U1, ulong U2, ulong U3) value = values[i % values.Length];
            _u0[i] = value.U0;
            _u1[i] = value.U1;
            _u2[i] = value.U2;
            _u3[i] = value.U3;
        }
    }

    [Benchmark(Baseline = true, OperationsPerInvoke = N)]
    public ulong Constructor()
    {
        ulong accumulator = 0;
        for (int i = 0; i < N; i++)
        {
            UInt256 value = new(_u0[i], _u1[i], _u2[i], _u3[i]);
            accumulator ^= value.u0 ^ value.u1 ^ value.u2 ^ value.u3;
        }

        return accumulator;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public ulong LegacyVectorOrScalar()
    {
        ulong accumulator = 0;
        for (int i = 0; i < N; i++)
        {
            UInt256 value = LegacyConstructor(_u0[i], _u1[i], _u2[i], _u3[i]);
            accumulator ^= value.u0 ^ value.u1 ^ value.u2 ^ value.u3;
        }

        return accumulator;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static UInt256 LegacyConstructor(ulong u0, ulong u1, ulong u2, ulong u3)
    {
        UInt256 result;
        if (Vector256.IsHardwareAccelerated)
        {
            Unsafe.SkipInit(out result);
            Unsafe.As<UInt256, Vector256<ulong>>(ref result) = Vector256.Create(u0, u1, u2, u3);
        }
        else
        {
            Unsafe.SkipInit(out result);
            ref ulong first = ref Unsafe.As<UInt256, ulong>(ref result);
            first = u0;
            Unsafe.Add(ref first, 1) = u1;
            Unsafe.Add(ref first, 2) = u2;
            Unsafe.Add(ref first, 3) = u3;
        }

        return result;
    }
}
