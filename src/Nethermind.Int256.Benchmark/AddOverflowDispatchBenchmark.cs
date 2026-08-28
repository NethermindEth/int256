// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.X86;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Jobs;

namespace Nethermind.Int256.Benchmark;

public enum AddOverflowCase
{
    Distribution,
    Small64,
    Full,
}

[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 3, warmupCount: 3, iterationCount: 10)]
[NoIntrinsicsJob(RuntimeMoniker.Net10_0, launchCount: 3, warmupCount: 3, iterationCount: 10)]
public class AddOverflowDispatchAB
{
    private const int N = 4096;
    private const int DistributionSmallCount = 3604; // 3604/4096 approximates measured 173,674,474/197,390,360 = 87.985%.

    private UInt256[] _a = null!;
    private UInt256[] _b = null!;
    private AddOverflowDelegate _addVector256 = null!;

    [Params(AddOverflowCase.Distribution, AddOverflowCase.Small64, AddOverflowCase.Full)]
    public AddOverflowCase Case;

    private delegate bool AddOverflowDelegate(in UInt256 a, in UInt256 b, out UInt256 result);

    [GlobalSetup]
    public void Setup()
    {
        if (!Avx2.IsSupported && Vector256.IsHardwareAccelerated)
        {
            _addVector256 = (AddOverflowDelegate)typeof(UInt256)
                .GetMethod("AddVector256", BindingFlags.NonPublic | BindingFlags.Static)!
                .CreateDelegate(typeof(AddOverflowDelegate));
        }

        _a = new UInt256[N];
        _b = new UInt256[N];
        Random random = new(0xADD0_497);

        for (int i = 0; i < N; i++)
        {
            (UInt256 a, UInt256 b) = Case switch
            {
                AddOverflowCase.Distribution => DistributionPair(i, random),
                AddOverflowCase.Small64 => Small64Pair(random),
                AddOverflowCase.Full => FullPair(random),
                _ => throw new ArgumentOutOfRangeException(),
            };
            _a[i] = a;
            _b[i] = b;
        }
    }

    [Benchmark(Baseline = true, OperationsPerInvoke = N)]
    public ulong Add_CurrentDispatch()
    {
        UInt256[] a = _a, b = _b;
        ulong accumulator = 0;
        for (int i = 0; i < a.Length; i++)
        {
            bool overflow = AddCurrentDispatch(in a[i], in b[i], out UInt256 result);
            accumulator ^= result.u0 ^ result.u1 ^ result.u2 ^ result.u3;
            accumulator ^= overflow ? 1UL : 0UL;
        }

        return accumulator;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public ulong Add_GatedDispatch()
    {
        UInt256[] a = _a, b = _b;
        ulong accumulator = 0;
        for (int i = 0; i < a.Length; i++)
        {
            bool overflow = UInt256.AddOverflow(in a[i], in b[i], out UInt256 result);
            accumulator ^= result.u0 ^ result.u1 ^ result.u2 ^ result.u3;
            accumulator ^= overflow ? 1UL : 0UL;
        }

        return accumulator;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private bool AddCurrentDispatch(in UInt256 a, in UInt256 b, out UInt256 result)
    {
        if (!Avx2.IsSupported && !Vector256.IsHardwareAccelerated)
        {
            return UInt256.AddScalar(in a, in b, out result);
        }

        if (Avx2.IsSupported)
        {
            return UInt256.AddAvx2(in a, in b, out result);
        }

        return _addVector256(in a, in b, out result);
    }

    private static (UInt256 A, UInt256 B) DistributionPair(int index, Random random)
        => index < DistributionSmallCount
            ? Small64Pair(random)
            : FullPair(random);

    private static (UInt256 A, UInt256 B) Small64Pair(Random random)
        => (new UInt256((ulong)random.NextInt64()), new UInt256((ulong)random.NextInt64()));

    private static (UInt256 A, UInt256 B) FullPair(Random random)
        => (new UInt256((ulong)random.NextInt64(), (ulong)random.NextInt64(), (ulong)random.NextInt64(), (ulong)random.NextInt64() | 1),
            new UInt256((ulong)random.NextInt64(), (ulong)random.NextInt64(), (ulong)random.NextInt64(), (ulong)random.NextInt64() | 1));
}
