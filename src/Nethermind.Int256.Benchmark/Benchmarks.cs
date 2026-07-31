// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Buffers.Binary;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Globalization;
using System.Linq;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.X86;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Configs;
using BenchmarkDotNet.Jobs;
using BenchmarkDotNet.Order;
using BenchmarkDotNet.Reports;
using BenchmarkDotNet.Running;
using Nethermind.Int256.Test;

namespace Nethermind.Int256.Benchmark;

//[DotTraceDiagnoser]
[HideColumns("Job", "RatioSD", "Error")]
[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 1, warmupCount: 3, iterationCount: 3)]
[NoAvx512Job(RuntimeMoniker.Net10_0, launchCount: 1, warmupCount: 3, iterationCount: 3)]
[NoAvx2Job(RuntimeMoniker.Net10_0, launchCount: 1, warmupCount: 3, iterationCount: 3)]
public class UnsignedBenchmarkBase
{
    public static IEnumerable<BigInteger> ValuesMinus3 { get; } = new[] { Numbers.UInt256Max - 3, Numbers.UInt192Max - 3, Numbers.UInt128Max - 3, Numbers.TwoTo64 - 3, BigInteger.One };
    public static IEnumerable<BigInteger> ValuesMinus2 { get; } = ValuesMinus3.Select(x => x + 1).ToArray();
    public static IEnumerable<BigInteger> ValuesMinus1 { get; } = ValuesMinus3.Select(x => x + 2).ToArray();

    public static IEnumerable<(BigInteger, UInt256)> ValuesMinus3Tuple { get; } = ValuesMinus3.Select(x => (x, (UInt256)x)).ToArray();
    public static IEnumerable<(BigInteger, UInt256)> ValuesMinus2Tuple { get; } = ValuesMinus2.Select(x => (x, (UInt256)x)).ToArray();
    public static IEnumerable<(BigInteger, UInt256)> ValuesMinus1Tuple { get; } = ValuesMinus1.Select(x => (x, (UInt256)x)).ToArray();

    public static IEnumerable<int> ValuesInt { get; } = UnaryOps.RandomInt(3);

    public static IEnumerable<UInt256> ValuesIntUint256 { get; } = ValuesInt.Select(x => (UInt256)x).ToArray();

    public static IEnumerable<(int, UInt256)> ValuesIntTuple { get; } = ValuesInt.Select(x => (x, (UInt256)x)).ToArray();
}

public class UnsignedIntTwoParamBenchmarkBase : UnsignedBenchmarkBase
{
    [ParamsSource(nameof(ValuesMinus1Tuple))]
    public (BigInteger, UInt256) A;

    [ParamsSource(nameof(ValuesIntTuple))]
    public (int, UInt256) D;
}

[Config(typeof(Config))]
public class UnsignedTwoParamBenchmarkBase : UnsignedBenchmarkBase
{
    private sealed class Config : ManualConfig
    {
        public Config()
        {
            WithOrderer(new Orderer<DoubleUInt256>(v => ParamIndex.TryGetValue(v, out var i) ? i : int.MaxValue));
        }
    }
    private static IEnumerable<DoubleUInt256> Values
    {
        get
        {
            HashSet<string> used = new();
            foreach (BigInteger x in ValuesMinus1)
            {
                foreach (BigInteger y in ValuesMinus2)
                {
                    var values = new DoubleUInt256((UInt256)x, (UInt256)y);
                    if (used.Add(values.ToString()))
                    {
                        yield return values;
                    }
                }
            }
        }
    }

    public static DoubleUInt256[] ValuesArray { get; } = [.. Values.OrderBy(o => o.B).ThenBy(o => o.A)];

    private static readonly Dictionary<DoubleUInt256, int> ParamIndex =
        ValuesArray.Select((v, i) => (v, i)).ToDictionary(t => t.v, t => t.i);

    [ParamsSource(nameof(ValuesArray))]
    public DoubleUInt256 Param;
}

[Config(typeof(Config))]
public class UnsignedThreeParamBenchmarkBase : UnsignedBenchmarkBase
{
    private sealed class Config : ManualConfig
    {
        public Config()
        {
            WithOrderer(new Orderer<TripleUInt256>(v => ParamIndex.TryGetValue(v, out var i) ? i : int.MaxValue));
        }
    }
    private static IEnumerable<TripleUInt256> Values
    {
        get
        {
            HashSet<string> used = new();
            foreach (BigInteger x in ValuesMinus1)
            {
                foreach (BigInteger y in ValuesMinus2)
                {
                    foreach (BigInteger z in ValuesMinus3)
                    {
                        var values = new TripleUInt256((UInt256)x, (UInt256)z, (UInt256)y);
                        if (used.Add($"{values.A.BitLen + values.B.BitLen},{values.C.BitLen}".ToString()))
                        {
                            yield return values;
                        }
                    }
                }
            }
        }
    }

    public static TripleUInt256[] ValuesArray { get; } = [.. Values.OrderBy(o => o.C).ThenBy(o => o.A).ThenBy(o => o.B)];

    private static readonly Dictionary<TripleUInt256, int> ParamIndex =
        ValuesArray.Select((v, i) => (v, i)).ToDictionary(t => t.v, t => t.i);

    [ParamsSource(nameof(ValuesArray))]
    public TripleUInt256 Param;
}

[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 1, warmupCount: 3, iterationCount: 5)]
[NoIntrinsicsJob(RuntimeMoniker.Net10_0, launchCount: 1, warmupCount: 3, iterationCount: 5)]
public class SignedBenchmarkBase
{
    public IEnumerable<BigInteger> Values => Enumerable.Concat(new[] { Numbers.Int256Max }, UnaryOps.RandomSigned(1));

    public IEnumerable<BigInteger> ValuesPositive => Values.Where(x => x.Sign >= 0);

    public IEnumerable<Int256> ValuesInt256 => Values.Select(x => (Int256)x);

    public IEnumerable<(BigInteger, Int256)> ValuesTuple => Values.Select(x => (x, (Int256)x));

    public IEnumerable<(BigInteger, Int256)> ValuesTuplePositive => ValuesPositive.Select(x => (x, (Int256)x));

    public IEnumerable<int> ValuesInt => UnaryOps.RandomInt(3);

    public IEnumerable<Int256> ValuesIntInt256 => ValuesInt.Select(x => (Int256)x);

    public IEnumerable<(int, Int256)> ValuesIntTuple => ValuesInt.Select(x => (x, (Int256)x));
}

public class SignedTwoParamBenchmarkBase : SignedBenchmarkBase
{
    [ParamsSource(nameof(ValuesTuple))]
    public (BigInteger, Int256) A;

    [ParamsSource(nameof(ValuesTuple))]
    public (BigInteger, Int256) B;
}

public class SignedThreeParamBenchmarkBase : SignedTwoParamBenchmarkBase
{
    [ParamsSource(nameof(ValuesTuple))]
    public (BigInteger, Int256) C;
}

public class SignedIntTwoParamBenchmarkBase : SignedBenchmarkBase
{
    [ParamsSource(nameof(ValuesTuple))]
    public (BigInteger, Int256) A;

    [ParamsSource(nameof(ValuesIntTuple))]
    public (int, Int256) D;
}

public class LessThanUnsigned : UnsignedTwoParamBenchmarkBase
{
    [Benchmark]
    public bool LessThan_UInt256()
    {
        return Param.A < Param.B;
    }
}

public class AddUnsigned : UnsignedTwoParamBenchmarkBase
{
    [Benchmark]
    public UInt256 Add_UInt256()
    {
        UInt256.Add(Param.A, Param.B, out UInt256 res);
        return res;
    }
}

public class AddSigned : SignedTwoParamBenchmarkBase
{
    [Benchmark(Baseline = true)]
    public BigInteger Add_BigInteger()
    {
        return (A.Item1 + B.Item1) % Numbers.TwoTo256;
    }

    [Benchmark]
    public Int256 Add_Int256()
    {
        Int256.Add(A.Item2, B.Item2, out Int256 res);
        return res;
    }
}

public class SubtractUnsigned : UnsignedTwoParamBenchmarkBase
{
    [Benchmark]
    public UInt256 Subtract_UInt256()
    {
        UInt256.Subtract(Param.A, Param.B, out UInt256 res);
        return res;
    }
}

// Same-process A/B of the library's internal scalar vs AVX2 Add paths; sub-nanosecond cross-run
// comparisons are too noisy, the within-run ratio is robust. Full-width operands (u3 != 0) so
// neither path can short-circuit.
[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 6, warmupCount: 3, iterationCount: 10)]
public class ArithmeticPathAB
{
    private const int N = 1024;
    private UInt256[] _a = null!;
    private UInt256[] _b = null!;

    [GlobalSetup]
    public void Setup()
    {
        if (!Avx2.IsSupported)
        {
            throw new PlatformNotSupportedException($"{nameof(ArithmeticPathAB)} requires AVX2.");
        }

        _a = new UInt256[N];
        _b = new UInt256[N];
        Random rnd = new(42);
        for (int i = 0; i < N; i++)
        {
            _a[i] = RandomWide(rnd);
            _b[i] = RandomWide(rnd);
        }
    }

    private static UInt256 RandomWide(Random rnd) => new(
        (ulong)rnd.NextInt64(),
        (ulong)rnd.NextInt64(),
        (ulong)rnd.NextInt64(),
        (ulong)rnd.NextInt64() | 0x8000_0000_0000_0000UL);

    [Benchmark(Baseline = true, OperationsPerInvoke = N)]
    public ulong Add_Avx2()
    {
        UInt256[] a = _a, b = _b;
        ulong acc = 0;
        for (int i = 0; i < a.Length; i++)
        {
            UInt256.AddAvx2(in a[i], in b[i], out UInt256 res);
            acc ^= res.u0;
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public ulong Add_Scalar()
    {
        UInt256[] a = _a, b = _b;
        ulong acc = 0;
        for (int i = 0; i < a.Length; i++)
        {
            UInt256.AddScalar(in a[i], in b[i], out UInt256 res);
            acc ^= res.u0;
        }
        return acc;
    }

}

// LessThan A/B across operand relationships: DifferHigh (scalar exits after one compare),
// DifferLow and Equal (scalar walks all four limbs).
public enum LtCase
{
    DifferHigh,
    DifferLow,
    Equal,
}

[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 6, warmupCount: 3, iterationCount: 10)]
public class LessThanPathAB
{
    private const int N = 1024;
    private UInt256[] _a = null!;
    private UInt256[] _b = null!;

    [Params(LtCase.DifferHigh, LtCase.DifferLow, LtCase.Equal)]
    public LtCase Case;

    [GlobalSetup]
    public void Setup()
    {
        if (!Avx2.IsSupported)
        {
            throw new PlatformNotSupportedException($"{nameof(LessThanPathAB)} requires AVX2.");
        }

        _a = new UInt256[N];
        _b = new UInt256[N];
        Random rnd = new(42);
        for (int i = 0; i < N; i++)
        {
            ulong x0 = (ulong)rnd.NextInt64();
            ulong x1 = (ulong)rnd.NextInt64();
            ulong x2 = (ulong)rnd.NextInt64();
            ulong x3 = (ulong)rnd.NextInt64() | 0x8000_0000_0000_0000UL;
            UInt256 a = new(x0, x1, x2, x3);
            _a[i] = a;
            _b[i] = Case switch
            {
                // Differ in the most-significant limb -> scalar exits after one compare.
                LtCase.DifferHigh => new UInt256(x0, x1, x2, x3 ^ 0x4000_0000_0000_0000UL),
                // Equal in u1..u3, differ only in u0 -> scalar must compare all four limbs.
                LtCase.DifferLow => new UInt256(x0 ^ 1UL, x1, x2, x3),
                // Fully equal -> scalar walks all four limbs, returns false.
                _ => a,
            };
        }
    }

    [Benchmark(Baseline = true, OperationsPerInvoke = N)]
    public int LessThan_Avx2()
    {
        UInt256[] a = _a, b = _b;
        int acc = 0;
        for (int i = 0; i < a.Length; i++)
        {
            if (UInt256.LessThanAvx2(in a[i], in b[i])) acc++;
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public int LessThan_Scalar()
    {
        UInt256[] a = _a, b = _b;
        int acc = 0;
        for (int i = 0; i < a.Length; i++)
        {
            if (UInt256.LessThanScalar(in a[i], in b[i])) acc++;
        }
        return acc;
    }
}

public class SubtractSigned : SignedTwoParamBenchmarkBase
{
    [Benchmark(Baseline = true)]
    public BigInteger Subtract_BigInteger()
    {
        return (A.Item1 - B.Item1) % Numbers.TwoTo256;
    }

    [Benchmark]
    public Int256 Subtract_Int256()
    {
        Int256.Subtract(A.Item2, B.Item2, out Int256 res);
        return res;
    }
}

public class AddModUnsigned : UnsignedThreeParamBenchmarkBase
{
    [Benchmark]
    public UInt256 AddMod_UInt256()
    {
        UInt256.AddMod(Param.A, Param.B, Param.C, out UInt256 res);
        return res;
    }
}

public class AddModSigned : SignedThreeParamBenchmarkBase
{
    [Benchmark(Baseline = true)]
    public BigInteger AddMod_BigInteger()
    {
        return ((A.Item1 + B.Item1) % C.Item1);
    }

    [Benchmark]
    public Int256 AddMod_Int256()
    {
        Int256.AddMod(A.Item2, B.Item2, C.Item2, out Int256 res);
        return res;
    }
}

public class SubtractModUnsigned : UnsignedThreeParamBenchmarkBase
{
    [Benchmark]
    public UInt256 SubtractMod_UInt256()
    {
        UInt256.SubtractMod(Param.A, Param.B, Param.C, out UInt256 res);
        return res;
    }
}

public class SubtractModSigned : SignedThreeParamBenchmarkBase
{
    [Benchmark(Baseline = true)]
    public BigInteger SubtractMod_BigInteger()
    {
        return ((A.Item1 - B.Item1) % C.Item1);
    }

    [Benchmark]
    public Int256 SubtractMod_Int256()
    {
        Int256.SubtractMod(A.Item2, B.Item2, C.Item2, out Int256 res);
        return res;
    }
}

public class MultiplyUnsigned : UnsignedTwoParamBenchmarkBase
{
    [Benchmark]
    public UInt256 Multiply_UInt256()
    {
        UInt256.Multiply(Param.A, Param.B, out UInt256 res);
        return res;
    }
}

[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 1, warmupCount: 5, iterationCount: 10)]
public class MultiplyScalarTargeted
{
    private const int OperationCount = 256;
    private DoubleUInt256[] _values = null!;

    [Params("Full", "OneSmall", "Small", "ProductionMix")]
    public string Shape { get; set; } = null!;

    [GlobalSetup]
    public void Setup()
    {
        _values = new DoubleUInt256[OperationCount];
        for (int i = 0; i < _values.Length; i++)
        {
            ulong seed = (ulong)i * 0x9E3779B97F4A7C15UL + 0xD1B54A32D192ED03UL;
            _values[i] = Shape switch
            {
                "Full" => CreateFull(seed),
                "OneSmall" => CreateOneSmall(seed),
                "Small" => new DoubleUInt256(seed | 2, (seed >> 1) | 2),
                _ => (i % 100) switch
                {
                    < 31 => CreateOneSmall(seed),
                    < 53 => CreateFull(seed),
                    < 63 => Create192(seed),
                    < 91 => Create128(seed),
                    _ => new DoubleUInt256(seed | 2, (seed >> 1) | 2),
                },
            };
        }
    }

    [Benchmark(OperationsPerInvoke = OperationCount)]
    public UInt256 Multiply()
    {
        UInt256 aggregate = default;
        foreach (DoubleUInt256 value in _values)
        {
            UInt256 a = value.A;
            UInt256 b = value.B;
            UInt256.Multiply(in a, in b, out UInt256 result);
            UInt256.Xor(in aggregate, in result, out aggregate);
        }

        return aggregate;
    }

    private static DoubleUInt256 Create128(ulong seed) =>
        new(new UInt256(seed, seed ^ 0xA0761D6478BD642FUL), new UInt256(~seed, seed ^ 0xE7037ED1A0B428DBUL));

    private static DoubleUInt256 Create192(ulong seed) =>
        new(
            new UInt256(seed, seed ^ 0xA0761D6478BD642FUL, seed ^ 0xE7037ED1A0B428DBUL),
            new UInt256(~seed, seed ^ 0x8EBC6AF09C88C6E3UL, seed ^ 0x589965CC75374CC3UL));

    private static DoubleUInt256 CreateFull(ulong seed) =>
        new(
            new UInt256(seed, seed ^ 0xA0761D6478BD642FUL, seed ^ 0xE7037ED1A0B428DBUL, seed ^ 0x8EBC6AF09C88C6E3UL),
            new UInt256(~seed, seed ^ 0x589965CC75374CC3UL, seed ^ 0x1D8E4E27C47D124FUL, seed ^ 0xEB44ACCAB455D165UL));

    private static DoubleUInt256 CreateOneSmall(ulong seed) =>
        new(CreateFull(seed).A, (seed >> 1) | 2);
}

public class MultiplySigned : SignedTwoParamBenchmarkBase
{
    [Benchmark(Baseline = true)]
    public BigInteger Multiply_BigInteger()
    {
        return (A.Item1 * B.Item1) % Numbers.TwoTo256;
    }

    [Benchmark]
    public Int256 Multiply_Int256()
    {
        Int256.Multiply(A.Item2, B.Item2, out Int256 res);
        return res;
    }
}

public class MultiplyModUnsigned : UnsignedThreeParamBenchmarkBase
{
    [Benchmark]
    public UInt256 MultiplyMod_UInt256()
    {
        UInt256.MultiplyMod(Param.A, Param.B, Param.C, out UInt256 res);
        return res;
    }
}

public class MultiplyModSigned : SignedThreeParamBenchmarkBase
{
    [Benchmark(Baseline = true)]
    public BigInteger MultiplyMod_BigInteger()
    {
        return ((A.Item1 * B.Item1) % C.Item1);
    }

    [Benchmark]
    public Int256 MultiplyMod_Int256()
    {
        Int256.MultiplyMod(A.Item2, B.Item2, C.Item2, out Int256 res);
        return res;
    }
}

[Config(typeof(Config))]
public class DivideUnsigned : UnsignedBenchmarkBase
{
    [Benchmark]
    public UInt256 Divide_UInt256()
    {
        UInt256.Divide(Param.A, Param.B, out UInt256 res);
        return res;
    }


    private sealed class Config : ManualConfig
    {
        public Config()
        {
            WithOrderer(new Orderer<DoubleUInt256>(v => ParamIndex.TryGetValue(v, out var i) ? i : int.MaxValue));
        }
    }

    protected static IEnumerable<DoubleUInt256> Values
    {
        get
        {
            foreach (BigInteger x in ValuesMinus1)
            {
                foreach (BigInteger y in ValuesMinus2)
                {
                    if (y > x)
                    {
                        // Skip cases where divisor is greater than dividend
                        continue;
                    }

                    yield return new DoubleUInt256((UInt256)x, (UInt256)y);
                }
            }
        }
    }

    public static DoubleUInt256[] ValuesArray { get; } = [.. Values.OrderBy(o => o.B).ThenBy(o => o.A)];

    private static readonly Dictionary<DoubleUInt256, int> ParamIndex =
        ValuesArray.Select((v, i) => (v, i)).ToDictionary(t => t.v, t => t.i);

    [ParamsSource(nameof(ValuesArray))]
    public DoubleUInt256 Param;
}

public class DivideSigned : SignedTwoParamBenchmarkBase
{
    [Benchmark(Baseline = true)]
    public BigInteger Divide_BigInteger()
    {
        return (A.Item1 / B.Item1);
    }

    [Benchmark]
    public Int256 Divide_Int256()
    {
        Int256.Divide(A.Item2, B.Item2, out Int256 res);
        return res;
    }
}

public class ExpUnsigned : UnsignedTwoParamBenchmarkBase
{
    [Benchmark]
    public UInt256 Exp_UInt256()
    {
        UInt256.Exp(Param.A, Param.B, out UInt256 res);
        return res;
    }
}

public class ExpSigned : SignedIntTwoParamBenchmarkBase
{
    [Benchmark(Baseline = true)]
    public BigInteger Exp_BigInteger()
    {
        return BigInteger.ModPow(A.Item1, D.Item1, Numbers.TwoTo256);
    }

    [Benchmark]
    public Int256 Exp_Int256()
    {
        Int256.Exp(A.Item2, D.Item2, out Int256 res);
        return res;
    }
}

public class ExpModUnsigned : UnsignedThreeParamBenchmarkBase
{
    [Benchmark]
    public UInt256 ExpMod_UInt256()
    {
        UInt256.ExpMod(Param.A, Param.B, Param.C, out UInt256 res);
        return res;
    }
}

public class ExpModSigned : SignedBenchmarkBase
{
    [ParamsSource(nameof(ValuesTuple))]
    public (BigInteger, Int256) A;

    [ParamsSource(nameof(ValuesTuplePositive))]
    public (BigInteger, Int256) B;

    [ParamsSource(nameof(ValuesTuplePositive))]
    public (BigInteger, Int256) C;

    [Benchmark(Baseline = true)]
    public BigInteger ExpMod_BigInteger()
    {
        return BigInteger.ModPow(A.Item1, B.Item1, C.Item1);
    }

    [Benchmark]
    public Int256 ExpMod_Int256()
    {
        Int256.ExpMod(A.Item2, B.Item2, C.Item2, out Int256 res);
        return res;
    }
}

[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 1, warmupCount: 3, iterationCount: 5, invocationCount: 128)]
public class ExpModTargeted
{
    public static TripleUInt256[] Values { get; } =
    [
        new TripleUInt256(5UL, 1UL, 97UL),
        new TripleUInt256(123456789UL, 17UL, 18446744073709551557UL),
        new TripleUInt256(
            new UInt256(ulong.MaxValue, ulong.MaxValue, 0, 0),
            new UInt256(ulong.MaxValue, 0, 0, 0),
            new UInt256(ulong.MaxValue - 58, ulong.MaxValue, 0, 0)),
        new TripleUInt256(
            new UInt256(ulong.MaxValue, ulong.MaxValue, ulong.MaxValue, ulong.MaxValue),
            new UInt256(ulong.MaxValue, ulong.MaxValue, 0, 0),
            new UInt256(ulong.MaxValue - 58, ulong.MaxValue, ulong.MaxValue, 0)),
    ];

    [ParamsSource(nameof(Values))]
    public TripleUInt256 Param;

    [Benchmark(Baseline = true)]
    public UInt256 ExpMod_WithFinalSquare()
    {
        UInt256 intermediate = UInt256.One;
        UInt256 bs = Param.A;
        int len = Param.B.BitLen;
        for (int i = 0; i < len; i++)
        {
            if ((Param.B[i / 64] & (1UL << (i % 64))) != 0)
            {
                UInt256.MultiplyMod(intermediate, bs, Param.C, out intermediate);
            }

            UInt256.MultiplyMod(bs, bs, Param.C, out bs);
        }

        return intermediate;
    }

    [Benchmark]
    public UInt256 ExpMod_UInt256()
    {
        UInt256.ExpMod(Param.A, Param.B, Param.C, out UInt256 res);
        return res;
    }
}

[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 1, warmupCount: 3, iterationCount: 5, invocationCount: 256)]
[NoIntrinsicsJob(RuntimeMoniker.Net10_0, launchCount: 1, warmupCount: 3, iterationCount: 5, invocationCount: 256)]
public class MultiplyMod64Targeted
{
    public static TripleUInt256[] Values { get; } =
    [
        new TripleUInt256(new UInt256(ulong.MaxValue, ulong.MaxValue, 0, 0), 123456789UL, 18446744073709551557UL),
        new TripleUInt256(new UInt256(ulong.MaxValue, ulong.MaxValue, 0, 0), new UInt256(ulong.MaxValue - 1, ulong.MaxValue, 0, 0), 18446744073709551557UL),
        new TripleUInt256(new UInt256(ulong.MaxValue, ulong.MaxValue, ulong.MaxValue, 0), new UInt256(ulong.MaxValue - 1, ulong.MaxValue, ulong.MaxValue, 0), 9223372036854775783UL),
    ];

    [ParamsSource(nameof(Values))]
    public TripleUInt256 Param;

    [Benchmark]
    public UInt256 MultiplyMod_UInt256()
    {
        UInt256.MultiplyMod(Param.A, Param.B, Param.C, out UInt256 res);
        return res;
    }
}

public class LeftShiftUnsigned : UnsignedIntTwoParamBenchmarkBase
{
    [Benchmark(Baseline = true)]
    public BigInteger LeftShift_BigInteger()
    {
        return (A.Item1 << D.Item1) % Numbers.TwoTo256;
    }

    [Benchmark]
    public UInt256 LeftShift_UInt256()
    {
        A.Item2.LeftShift(D.Item1, out UInt256 res);
        return res;
    }
}

public class LeftShiftSigned : SignedIntTwoParamBenchmarkBase
{
    [Benchmark(Baseline = true)]
    public BigInteger LeftShift_BigInteger()
    {
        return (A.Item1 << D.Item1) % Numbers.TwoTo256;
    }

    [Benchmark]
    public Int256 LeftShift_Int256()
    {
        A.Item2.LeftShift(D.Item1, out Int256 res);
        return res;
    }
}

public class RightShiftUnsigned : UnsignedIntTwoParamBenchmarkBase
{
    [Benchmark(Baseline = true)]
    public BigInteger RightShift_BigInteger()
    {
        return (A.Item1 >> D.Item1) % Numbers.TwoTo256;
    }

    [Benchmark]
    public UInt256 RightShift_UInt256()
    {
        A.Item2.RightShift(D.Item1, out UInt256 res);
        return res;
    }
}

public class RightShiftSigned : SignedIntTwoParamBenchmarkBase
{
    [Benchmark(Baseline = true)]
    public BigInteger RightShift_BigInteger()
    {
        return (A.Item1 >> D.Item1) % Numbers.TwoTo256;
    }

    [Benchmark]
    public Int256 RightShift_Int256()
    {
        A.Item2.RightShift(D.Item1, out Int256 res);
        return res;
    }
}

public class IsZeroOne
{
    public UInt256[] Values { get; } = { UInt256.Zero, UInt256.One, UInt256.MaxValue };

    [ParamsSource(nameof(Values))]
    public UInt256 A;

    [Benchmark]
    public bool IsZero()
    {
        return A.IsZero;
    }

    [Benchmark]
    public bool IsOne()
    {
        return A.IsOne;
    }
}

[MemoryDiagnoser]
[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 1, warmupCount: 3, iterationCount: 5)]
public class BigIntegerToUInt256
{
    public static BigInteger[] Values { get; } =
    [
        BigInteger.Zero,
        new BigInteger(ulong.MaxValue),
        new BigInteger(ulong.MaxValue) << 64 | new BigInteger(ulong.MaxValue),
        (BigInteger.One << 192) - 1,
        (BigInteger.One << 256) - 1,
    ];

    [ParamsSource(nameof(Values))]
    public BigInteger Value;

    [Benchmark]
    public UInt256 Cast_UInt256()
    {
        return (UInt256)Value;
    }
}

public abstract class ParseUnsignedBenchmarkBase
{
    public static string[] HexValues { get; } =
    [
        "0x0",
        "0x1",
        "0xffffffffffffffff",
        "0xffffffffffffffffffffffffffffffff",
        "0xffffffffffffffffffffffffffffffffffffffffffffffff",
        "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
    ];

    public static string[] DecimalValues { get; } =
    [
        "0",
        "1",
        "18446744073709551615",
        "340282366920938463463374607431768211455",
        "6277101735386680763835789423207666416102355444464034512895",
        "115792089237316195423570985008687907853269984665640564039457584007913129639935",
    ];

    protected static UInt256 ParseBigIntegerHex(string value)
    {
        ReadOnlySpan<char> digits = value.AsSpan(2);
        Span<char> positiveDigits = stackalloc char[digits.Length + 1];
        positiveDigits[0] = '0';
        digits.CopyTo(positiveDigits[1..]);
        BigInteger parsed = BigInteger.Parse(positiveDigits, NumberStyles.HexNumber, CultureInfo.InvariantCulture);
        return (UInt256)parsed;
    }

    protected static UInt256 ParseBigIntegerDecimal(string value)
    {
        BigInteger parsed = BigInteger.Parse(value, NumberStyles.Integer, CultureInfo.InvariantCulture);
        return (UInt256)parsed;
    }
}

[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 1, warmupCount: 1, iterationCount: 5, invocationCount: 256)]
public class ParseHexUnsigned : ParseUnsignedBenchmarkBase
{
    [ParamsSource(nameof(HexValues))]
    public string Value { get; set; } = null!;

    [Benchmark(Baseline = true)]
    public UInt256 Parse_BigInteger()
    {
        return ParseBigIntegerHex(Value);
    }

    [Benchmark]
    public UInt256 Parse_UInt256()
    {
        return UInt256.Parse(Value);
    }

    [Benchmark]
    public bool TryParse_UInt256()
    {
        return UInt256.TryParse(Value, out _);
    }
}

[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 1, warmupCount: 1, iterationCount: 5, invocationCount: 256)]
public class ParseDecimalUnsigned : ParseUnsignedBenchmarkBase
{
    [ParamsSource(nameof(DecimalValues))]
    public string Value { get; set; } = null!;

    [Benchmark(Baseline = true)]
    public UInt256 Parse_BigInteger()
    {
        return ParseBigIntegerDecimal(Value);
    }

    [Benchmark]
    public UInt256 Parse_UInt256()
    {
        return UInt256.Parse(Value);
    }

    [Benchmark]
    public bool TryParse_UInt256()
    {
        return UInt256.TryParse(Value, out _);
    }
}

// End-to-end AddMod with a 64-bit modulus across sum widths. Under the no-intrinsics job
// X86Base is unavailable, so AddMod takes the portable Remainder257By64Bits path; the default
// job takes the untouched x86 path and serves as a control.
public enum ModSumWidth
{
    Small,    // x, y < m < 2^63 => sum fits one limb
    CarryU1,  // x, y < m with the modulus MSB set => sum has u1 == 1
    Mid128,   // sum is a full 128-bit value
    Full,     // full-width operands, small modulus
}

[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 3, warmupCount: 3, iterationCount: 10)]
[NoIntrinsicsJob(RuntimeMoniker.Net10_0, launchCount: 3, warmupCount: 3, iterationCount: 10)]
public class AddModByUInt64Modulus
{
    private const int N = 1024;
    private UInt256[] _x = null!;
    private UInt256[] _y = null!;
    private UInt256[] _m = null!;

    [Params(ModSumWidth.Small, ModSumWidth.CarryU1, ModSumWidth.Mid128, ModSumWidth.Full)]
    public ModSumWidth Width;

    [GlobalSetup]
    public void Setup()
    {
        _x = new UInt256[N];
        _y = new UInt256[N];
        _m = new UInt256[N];
        Random rnd = new(42);
        for (int i = 0; i < N; i++)
        {
            ulong m = (ulong)rnd.NextInt64(2, long.MaxValue);
            switch (Width)
            {
                case ModSumWidth.Small:
                    _x[i] = (ulong)rnd.NextInt64() % m;
                    _y[i] = (ulong)rnd.NextInt64() % m;
                    break;
                case ModSumWidth.CarryU1:
                    m = 0x8000_0000_0000_0001UL | (ulong)rnd.NextInt64();
                    _x[i] = m - 1;
                    _y[i] = m - 1;
                    break;
                case ModSumWidth.Mid128:
                    _x[i] = new UInt256((ulong)rnd.NextInt64(), (ulong)rnd.NextInt64() >> 1, 0, 0);
                    _y[i] = new UInt256((ulong)rnd.NextInt64(), (ulong)rnd.NextInt64() >> 1, 0, 0);
                    break;
                default:
                    _x[i] = new UInt256((ulong)rnd.NextInt64(), (ulong)rnd.NextInt64(), (ulong)rnd.NextInt64(), (ulong)rnd.NextInt64());
                    _y[i] = new UInt256((ulong)rnd.NextInt64(), (ulong)rnd.NextInt64(), (ulong)rnd.NextInt64(), (ulong)rnd.NextInt64());
                    break;
            }
            _m[i] = m;
        }
    }

    [Benchmark(OperationsPerInvoke = N)]
    public ulong AddMod_UInt64Modulus()
    {
        UInt256[] x = _x, y = _y, m = _m;
        ulong acc = 0;
        for (int i = 0; i < x.Length; i++)
        {
            UInt256.AddMod(in x[i], in y[i], in m[i], out UInt256 res);
            acc ^= (ulong)res;
        }
        return acc;
    }
}

[MemoryDiagnoser]
[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 1, warmupCount: 3, iterationCount: 5)]
[NoIntrinsicsJob(RuntimeMoniker.Net10_0, launchCount: 1, warmupCount: 3, iterationCount: 5)]
public class PaddedBytesUnsigned
{
    public static UInt256 Value { get; } = UInt256.MaxValue;

    // Common pad widths: 20 = address, 32 = EVM word, 33/64 = left-padded wider forms.
    [Params(20, 32, 33, 64)]
    public int N;

    // Mirrors PaddedBytes(int) before this change so the benchmark is a direct in-process A/B.
    [Benchmark(Baseline = true)]
    public byte[] PaddedBytes_Previous()
    {
        byte[] b = new byte[N];
        for (int i = 0; i < 32 && i < N; i++)
        {
            b[N - 1 - i] = (byte)(Value[i / 8] >> (8 * (i % 8)));
        }

        return b;
    }

    [Benchmark]
    public byte[] PaddedBytes_UInt256()
    {
        return Value.PaddedBytes(N);
    }
}

// In-process A/B for the Int256 signed-comparison preamble: master's Sign-based classification
// (replicated below via the public surface) vs operator<'s top-bit test.
public enum SignedCmpCase
{
    DifferSign,          // operands of opposite sign - decided by the preamble alone
    SameSignDifferHigh,  // both negative, differ in the top limb
    Equal,               // fully equal - full limb compare on both paths
}

[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 6, warmupCount: 3, iterationCount: 10)]
public class SignedCompareAB
{
    private const int N = 1024;
    private Int256[] _a = null!;
    private Int256[] _b = null!;

    [Params(SignedCmpCase.DifferSign, SignedCmpCase.SameSignDifferHigh, SignedCmpCase.Equal)]
    public SignedCmpCase Case;

    [GlobalSetup]
    public void Setup()
    {
        _a = new Int256[N];
        _b = new Int256[N];
        Random rnd = new(42);
        for (int i = 0; i < N; i++)
        {
            ulong x0 = (ulong)rnd.NextInt64();
            ulong x1 = (ulong)rnd.NextInt64();
            ulong x2 = (ulong)rnd.NextInt64();
            ulong x3 = (ulong)rnd.NextInt64() | 0x8000_0000_0000_0000UL;
            _a[i] = new Int256(new UInt256(x0, x1, x2, x3));
            _b[i] = Case switch
            {
                SignedCmpCase.DifferSign => new Int256(new UInt256(x0, x1, x2, x3 & ~0x8000_0000_0000_0000UL)),
                SignedCmpCase.SameSignDifferHigh => new Int256(new UInt256(x0, x1, x2, x3 ^ 0x4000_0000_0000_0000UL)),
                _ => _a[i],
            };
        }
    }

    // Master's operator< shape: full Sign for both operands, then the unsigned limb compare.
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool LessThanSignBased(in Int256 z, in Int256 x)
    {
        int zSign = z.Sign;
        int xSign = x.Sign;

        if (zSign >= 0)
        {
            if (xSign < 0)
            {
                return false;
            }
        }
        else if (xSign >= 0)
        {
            return true;
        }

        return Unsafe.As<Int256, UInt256>(ref Unsafe.AsRef(in z)) < Unsafe.As<Int256, UInt256>(ref Unsafe.AsRef(in x));
    }

    [Benchmark(Baseline = true, OperationsPerInvoke = N)]
    public int LessThan_SignBased()
    {
        Int256[] a = _a, b = _b;
        int acc = 0;
        for (int i = 0; i < a.Length; i++)
        {
            if (LessThanSignBased(in a[i], in b[i])) acc++;
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = N)]
    public int LessThan_TopBit()
    {
        Int256[] a = _a, b = _b;
        int acc = 0;
        for (int i = 0; i < a.Length; i++)
        {
            if (a[i] < b[i]) acc++;
        }
        return acc;
    }
}

// In-process A/B for Remainder257By64BitsX86Base's fast path, which skips DivRems on zero high
// limbs. Full is a no-regression guard: both paths take all four DivRems there.
public enum SumWidth
{
    Small,   // sum < 2^65; 1 DivRem on the fast path
    Mid128,  // full 128-bit sum; 2 DivRems on the fast path
    Full,    // full 257-bit sum; 4 DivRems on both paths
}

#pragma warning disable SYSLIB5004 // X86Base.X64.DivRem is [Experimental]; the library already uses it
[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 6, warmupCount: 3, iterationCount: 10)]
public class AddModReduce64AB
{
    private const int N = 1024;
    private ulong[] _u0 = null!;
    private ulong[] _u1 = null!;
    private ulong[] _u2 = null!;
    private ulong[] _u3 = null!;
    private ulong[] _a4 = null!;
    private ulong[] _d = null!;

    [Params(SumWidth.Small, SumWidth.Mid128, SumWidth.Full)]
    public SumWidth Width;

    [GlobalSetup]
    public void Setup()
    {
        if (!X86Base.X64.IsSupported)
        {
            throw new PlatformNotSupportedException($"{nameof(AddModReduce64AB)} requires x86-64 (X86Base.X64.DivRem).");
        }

        _u0 = new ulong[N];
        _u1 = new ulong[N];
        _u2 = new ulong[N];
        _u3 = new ulong[N];
        _a4 = new ulong[N];
        _d = new ulong[N];
        Random rnd = new(42);
        for (int i = 0; i < N; i++)
        {
            _d[i] = (ulong)rnd.NextInt64(2, long.MaxValue); // 64-bit modulus, >= 2
            _u0[i] = (ulong)rnd.NextInt64();
            switch (Width)
            {
                case SumWidth.Small:
                    _u1[i] = (ulong)(rnd.NextInt64() & 1); // 0 or 1 (carry out of u0)
                    _u2[i] = 0; _u3[i] = 0; _a4[i] = 0;
                    break;
                case SumWidth.Mid128:
                    _u1[i] = (ulong)rnd.NextInt64() | 0x8000_0000_0000_0000UL; // large high limb
                    _u2[i] = 0; _u3[i] = 0; _a4[i] = 0;
                    break;
                default: // Full
                    _u1[i] = (ulong)rnd.NextInt64();
                    _u2[i] = (ulong)rnd.NextInt64();
                    _u3[i] = (ulong)rnd.NextInt64();
                    _a4[i] = (ulong)(rnd.NextInt64() & 1);
                    break;
            }
        }
    }

    // Current: four hardware DivRems, one per limb (matches Remainder257By64BitsX86Base).
    [Benchmark(Baseline = true, OperationsPerInvoke = N)]
    public ulong Current()
    {
        ulong[] u0 = _u0, u1 = _u1, u2 = _u2, u3 = _u3, a4 = _a4, d = _d;
        ulong acc = 0;
        for (int i = 0; i < u0.Length; i++)
        {
            ulong dd = d[i];
            ulong r = X86Base.X64.DivRem(u3[i], a4[i], dd).Remainder;
            r = X86Base.X64.DivRem(u2[i], r, dd).Remainder;
            r = X86Base.X64.DivRem(u1[i], r, dd).Remainder;
            r = X86Base.X64.DivRem(u0[i], r, dd).Remainder;
            acc ^= r;
        }
        return acc;
    }

    // Fast path: skip the wasted divides when the sum fits in <=128 bits.
    [Benchmark(OperationsPerInvoke = N)]
    public ulong FastPath()
    {
        ulong[] u0 = _u0, u1 = _u1, u2 = _u2, u3 = _u3, a4 = _a4, d = _d;
        ulong acc = 0;
        for (int i = 0; i < u0.Length; i++)
        {
            ulong dd = d[i];
            ulong hu1 = u1[i], hu0 = u0[i];
            ulong r;
            if ((u2[i] | u3[i] | a4[i]) == 0)
            {
                if (hu1 < dd)
                {
                    r = X86Base.X64.DivRem(hu0, hu1, dd).Remainder; // (hu1:hu0) % d in one DIV
                }
                else
                {
                    ulong rr = X86Base.X64.DivRem(hu1, 0UL, dd).Remainder; // hu1 % d
                    r = X86Base.X64.DivRem(hu0, rr, dd).Remainder;
                }
            }
            else
            {
                r = X86Base.X64.DivRem(u3[i], a4[i], dd).Remainder;
                r = X86Base.X64.DivRem(u2[i], r, dd).Remainder;
                r = X86Base.X64.DivRem(hu1, r, dd).Remainder;
                r = X86Base.X64.DivRem(hu0, r, dd).Remainder;
            }
            acc ^= r;
        }
        return acc;
    }
}
#pragma warning restore SYSLIB5004

// In-process A/B for the 32-byte ToBigEndian write path (MSTORE-style serialization, RLP/RPC/trie).
// The current implementation writes four BSWAPped 64-bit limbs (ScalarWriteBe); the proposed one
// reinterprets the value as a Vector256<byte> and reverses all 32 bytes with a single shuffle/permute
// (mirroring the already-vectorized big-endian READ ctor), storing the result with WriteUnaligned.
// Both strategies are replicated inline here and measured in the SAME process so the A/B ratio is
// robust to cross-run variance. Results escape into the _dst field buffer so the writes are not
// elided; _dst is re-read into the accumulator to anchor the store. Default job = AVX2 on this host.
[SimpleJob(RuntimeMoniker.Net10_0, launchCount: 6, warmupCount: 3, iterationCount: 10)]
public class ToBigEndianAB
{
    private const int N = 1024;
    private UInt256[] _src = null!;
    private byte[] _dst = null!;

    [GlobalSetup]
    public void Setup()
    {
        if (!Avx2.IsSupported)
        {
            throw new PlatformNotSupportedException($"{nameof(ToBigEndianAB)} requires AVX2.");
        }

        _src = new UInt256[N];
        _dst = new byte[32];
        Random rnd = new(42);
        for (int i = 0; i < N; i++)
        {
            _src[i] = new UInt256(
                (ulong)rnd.NextInt64(),
                (ulong)rnd.NextInt64(),
                (ulong)rnd.NextInt64(),
                (ulong)rnd.NextInt64());
        }
    }

    // Current implementation: four big-endian 64-bit stores (BSWAP + mov).
    [Benchmark(Baseline = true, OperationsPerInvoke = N)]
    public byte ScalarWriteBe()
    {
        UInt256[] src = _src;
        Span<byte> dst = _dst;
        byte acc = 0;
        for (int i = 0; i < src.Length; i++)
        {
            ref readonly UInt256 v = ref src[i];
            BinaryPrimitives.WriteUInt64BigEndian(dst.Slice(0, 8), v.u3);
            BinaryPrimitives.WriteUInt64BigEndian(dst.Slice(8, 8), v.u2);
            BinaryPrimitives.WriteUInt64BigEndian(dst.Slice(16, 8), v.u1);
            BinaryPrimitives.WriteUInt64BigEndian(dst.Slice(24, 8), v.u0);
            acc ^= dst[0];
        }
        return acc;
    }

    // Proposed implementation: full 32-byte reverse via one shuffle (AVX2) or permute (AVX-512 VBMI),
    // then an unaligned 256-bit store. The byte-reverse permutation is an involution, so the same
    // shuffle constant the big-endian read ctor uses also performs the big-endian write.
    [Benchmark(OperationsPerInvoke = N)]
    public byte VectorWriteBe()
    {
        UInt256[] src = _src;
        Span<byte> dst = _dst;
        ref byte dst0 = ref MemoryMarshal.GetReference(dst);
        Vector256<byte> shuffle = Vector256.Create(
            0x18191a1b1c1d1e1ful,
            0x1011121314151617ul,
            0x08090a0b0c0d0e0ful,
            0x0001020304050607ul).AsByte();
        byte acc = 0;
        for (int i = 0; i < src.Length; i++)
        {
            Vector256<byte> data = Unsafe.As<UInt256, Vector256<byte>>(ref Unsafe.AsRef(in src[i]));
            if (Avx512Vbmi.VL.IsSupported)
            {
                Unsafe.WriteUnaligned(ref dst0, Avx512Vbmi.VL.PermuteVar32x8(data, shuffle));
            }
            else
            {
                Vector256<byte> convert = Avx2.Shuffle(data, shuffle);
                Vector256<ulong> permute = Avx2.Permute4x64(convert.AsUInt64(), 0b_01_00_11_10);
                Unsafe.WriteUnaligned(ref dst0, permute);
            }
            acc ^= dst[0];
        }
        return acc;
    }
}

public readonly record struct DoubleUInt256(UInt256 A, UInt256 B)
{
    public override readonly string ToString() => $"{A.BitLen} bits / {B.BitLen} bits";
}

public readonly record struct TripleUInt256(UInt256 A, UInt256 B, UInt256 C)
{
    public override readonly string ToString() => $"{A.BitLen},{B.BitLen},{C.BitLen} bits";
}

public sealed class Orderer<T> : IOrderer
{
    private readonly Func<T, int> _indexOf;

    public Orderer(Func<T, int> indexOf) => _indexOf = indexOf;

    public IEnumerable<BenchmarkCase> GetSummaryOrder(ImmutableArray<BenchmarkCase> benchmarks, Summary summary)
        => benchmarks
            .OrderBy(b => _indexOf(GetParam(b)))
            .ThenBy(EnvVarsTotalLength)
            .ThenBy(b => b.Job.DisplayInfo);

    public IEnumerable<BenchmarkCase> GetExecutionOrder(ImmutableArray<BenchmarkCase> benchmarksCase, IEnumerable<BenchmarkLogicalGroupRule>? order = null)
        => benchmarksCase
            .OrderBy(b => _indexOf(GetParam(b)))
            .ThenBy(b => b.Job.DisplayInfo);

    private static T GetParam(BenchmarkCase b)
        => (T)b.Parameters.Items.First(p => p.Name == "Param").Value!;

    public string? GetHighlightGroupKey(BenchmarkCase benchmarkCase) => null;
    public string? GetLogicalGroupKey(ImmutableArray<BenchmarkCase> allBenchmarksCases, BenchmarkCase benchmarkCase)
        => GetParam(benchmarkCase)?.ToString();

    public IEnumerable<IGrouping<string, BenchmarkCase>> GetLogicalGroupOrder(IEnumerable<IGrouping<string, BenchmarkCase>> logicalGroups, IEnumerable<BenchmarkLogicalGroupRule>? order = null)
        => logicalGroups;

    public bool SeparateLogicalGroups => true;
    public bool SeparateHighlightGroups => false;
    public bool SeparateReporters => false;

    private static int EnvVarsTotalLength(BenchmarkCase b)
    {
        var vars = b.Job?.Environment?.EnvironmentVariables;
        if (vars is null) return 0;

        int sum = 0;
        foreach (var e in vars)
        {
            // length of "KEY=VALUE" without allocating it
            sum += (e.Key?.Length ?? 0) + 1 + (e.Value?.Length ?? 0);
        }
        return sum;
    }
}
