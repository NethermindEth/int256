// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Jobs;

namespace Nethermind.Int256.Benchmark;

public enum MultiplyModMaxCase
{
    MaxValue,
    FullWidthMiss,
    NarrowModulus,
}

// This benchmark is identical on the candidate and base branches. The branch A/B therefore
// compares the max-modulus fold against the legacy full-width reduction with the same inputs.
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
