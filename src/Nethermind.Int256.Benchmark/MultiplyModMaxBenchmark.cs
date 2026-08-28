// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Reflection;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Jobs;

namespace Nethermind.Int256.Benchmark;

public enum MultiplyModMaxCase
{
    MaxValue,
    FullWidthMiss,
    NarrowModulus,
}

// This end-to-end benchmark is identical on the candidate and base branches, so branch A/B
// compares the optimized public path with the legacy implementation on the same inputs.
[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 3, warmupCount: 3, iterationCount: 10)]
[NoIntrinsicsJob(RuntimeMoniker.Net10_0, launchCount: 3, warmupCount: 3, iterationCount: 10)]
public class MultiplyModMaxTargeted
{
    private const int OperationCount = 1024;
    private UInt256[] _left = null!;
    private UInt256[] _right = null!;
    private UInt256[] _modulus = null!;

    [Params(MultiplyModMaxCase.MaxValue, MultiplyModMaxCase.FullWidthMiss, MultiplyModMaxCase.NarrowModulus)]
    public MultiplyModMaxCase Case { get; set; }

    [GlobalSetup]
    public void Setup()
    {
        _left = new UInt256[OperationCount];
        _right = new UInt256[OperationCount];
        _modulus = new UInt256[OperationCount];
        for (int i = 0; i < _left.Length; i++)
        {
            ulong seed = (ulong)i * 0x9E3779B97F4A7C15UL + 0xD1B54A32D192ED03UL;
            _left[i] = CreateFull(seed);
            _right[i] = CreateFull(seed ^ 0xA0761D6478BD642FUL);
            _modulus[i] = Case switch
            {
                MultiplyModMaxCase.MaxValue => UInt256.MaxValue,
                MultiplyModMaxCase.FullWidthMiss => new UInt256(ulong.MaxValue - 1, ulong.MaxValue, ulong.MaxValue, ulong.MaxValue),
                _ => new UInt256(ulong.MaxValue, ulong.MaxValue, ulong.MaxValue, 0),
            };
        }
    }

    [Benchmark(OperationsPerInvoke = OperationCount)]
    public UInt256 MultiplyMod()
    {
        UInt256 aggregate = default;
        UInt256[] left = _left;
        UInt256[] right = _right;
        UInt256[] modulus = _modulus;
        for (int i = 0; i < left.Length; i++)
        {
            UInt256.MultiplyMod(in left[i], in right[i], in modulus[i], out UInt256 result);
            UInt256.Xor(in aggregate, in result, out aggregate);
        }

        return aggregate;
    }

    private static UInt256 CreateFull(ulong seed) => new(
        seed | 2,
        seed ^ 0xA0761D6478BD642FUL | 1,
        seed ^ 0xE7037ED1A0B428DBUL | 1,
        seed ^ 0x8EBC6AF09C88C6E3UL | 1);

}

// Reduction-only A/B evidence. Both implementations consume the same precomputed product halves;
// the private legacy reducer is bound once during setup, so delegate dispatch is part of this
// algorithm-isolation measurement. The end-to-end benchmark above covers public-path integration.
[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 3, warmupCount: 3, iterationCount: 10)]
[NoIntrinsicsJob(RuntimeMoniker.Net10_0, launchCount: 3, warmupCount: 3, iterationCount: 10)]
public class MultiplyModMaxReductionTargeted
{
    private const int OperationCount = 1024;
    private UInt256[] _lo = null!;
    private UInt256[] _hi = null!;
    private UInt256 _modulus;
    private Reduction _fold = null!;
    private Reduction _legacy = null!;

    private delegate void Reduction(in UInt256 lo, in UInt256 hi, in UInt256 modulus, out UInt256 result);

    [GlobalSetup]
    public void Setup()
    {
        _lo = new UInt256[OperationCount];
        _hi = new UInt256[OperationCount];
        _modulus = UInt256.MaxValue;

        Product product = GetPrivateDelegate<Product>("Multiply256To512Bit");
        _legacy = GetPrivateDelegate<Reduction>("Remainder512By256Bits");
        _fold = FoldMaxModulus;

        for (int i = 0; i < OperationCount; i++)
        {
            ulong seed = (ulong)i * 0x9E3779B97F4A7C15UL + 0xD1B54A32D192ED03UL;
            UInt256 left = CreateFull(seed);
            UInt256 right = CreateFull(seed ^ 0xA0761D6478BD642FUL);
            product(in left, in right, out _lo[i], out _hi[i]);
        }
    }

    [Benchmark(Baseline = true, OperationsPerInvoke = OperationCount)]
    public UInt256 LegacyReduction()
    {
        UInt256 aggregate = default;
        UInt256[] lo = _lo;
        UInt256[] hi = _hi;
        UInt256 modulus = _modulus;
        Reduction legacy = _legacy;
        for (int i = 0; i < lo.Length; i++)
        {
            legacy(in lo[i], in hi[i], in modulus, out UInt256 result);
            UInt256.Xor(in aggregate, in result, out aggregate);
        }

        return aggregate;
    }

    [Benchmark(OperationsPerInvoke = OperationCount)]
    public UInt256 MaxModulusFold()
    {
        UInt256 aggregate = default;
        UInt256[] lo = _lo;
        UInt256[] hi = _hi;
        Reduction fold = _fold;
        for (int i = 0; i < lo.Length; i++)
        {
            fold(in lo[i], in hi[i], in _modulus, out UInt256 result);
            UInt256.Xor(in aggregate, in result, out aggregate);
        }

        return aggregate;
    }

    private static void FoldMaxModulus(in UInt256 lo, in UInt256 hi, in UInt256 modulus, out UInt256 result)
    {
        bool carry = UInt256.AddOverflow(in lo, in hi, out result);
        if (carry)
        {
            UInt256.Add(in result, in UInt256.One, out result);
        }

        if (result.u3 == ulong.MaxValue && (result.u0 & result.u1 & result.u2) == ulong.MaxValue)
        {
            result = default;
        }
    }

    private static TDelegate GetPrivateDelegate<TDelegate>(string name) where TDelegate : Delegate
    {
        MethodInfo method = typeof(UInt256).GetMethod(name, BindingFlags.NonPublic | BindingFlags.Static)
            ?? throw new MissingMethodException(typeof(UInt256).FullName, name);
        return method.CreateDelegate<TDelegate>();
    }

    private static UInt256 CreateFull(ulong seed) => new(
        seed | 2,
        seed ^ 0xA0761D6478BD642FUL | 1,
        seed ^ 0xE7037ED1A0B428DBUL | 1,
        seed ^ 0x8EBC6AF09C88C6E3UL | 1);

    private delegate void Product(in UInt256 x, in UInt256 y, out UInt256 lo, out UInt256 hi);
}
