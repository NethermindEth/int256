// SPDX-FileCopyrightText: 2025 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Numerics;
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
//[NoAvx512Job(RuntimeMoniker.Net10_0, launchCount: 1, warmupCount: 3, iterationCount: 3)]
//[NoAvx2Job(RuntimeMoniker.Net10_0, launchCount: 1, warmupCount: 3, iterationCount: 3, baseline: true)]
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
