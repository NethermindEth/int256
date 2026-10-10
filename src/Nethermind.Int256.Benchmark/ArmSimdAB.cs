// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System;
using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.Arm;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Configs;
using BenchmarkDotNet.Jobs;

namespace Nethermind.Int256.Benchmark;

/// <summary>NEON candidates for paths that are scalar on ARM64; kept to re-measure on newer cores and runtimes.</summary>
internal static class NeonCandidates
{
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ref Vector128<ulong> Halves(in UInt256 value)
        => ref Unsafe.As<UInt256, Vector128<ulong>>(ref Unsafe.AsRef(in value));

    // Lane masks packed to 16 bits, limb 3 highest: a < b iff packed lt > packed gt.
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool LessThan(in UInt256 a, in UInt256 b)
    {
        ref Vector128<ulong> ar = ref Halves(in a);
        ref Vector128<ulong> br = ref Halves(in b);
        Vector128<ulong> aLo = ar, aHi = Unsafe.Add(ref ar, 1);
        Vector128<ulong> bLo = br, bHi = Unsafe.Add(ref br, 1);

        Vector128<uint> lt = AdvSimd.Arm64.UnzipEven(
            AdvSimd.Arm64.CompareGreaterThan(bLo, aLo).AsUInt32(), AdvSimd.Arm64.CompareGreaterThan(bHi, aHi).AsUInt32());
        Vector128<uint> gt = AdvSimd.Arm64.UnzipEven(
            AdvSimd.Arm64.CompareGreaterThan(aLo, bLo).AsUInt32(), AdvSimd.Arm64.CompareGreaterThan(aHi, bHi).AsUInt32());
        Vector128<ulong> packed = AdvSimd.Arm64.UnzipEven(lt.AsUInt16(), gt.AsUInt16()).AsUInt64();
        return packed.GetElement(0) > packed.GetElement(1);
    }

    // Same packing for x and y; one uminv reduces both verdicts.
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool LessThanBoth(in UInt256 x, in UInt256 y, in UInt256 m)
    {
        ref Vector128<ulong> mr = ref Halves(in m);
        ref Vector128<ulong> xr = ref Halves(in x);
        ref Vector128<ulong> yr = ref Halves(in y);
        Vector128<ulong> mLo = mr, mHi = Unsafe.Add(ref mr, 1);
        Vector128<ulong> xLo = xr, xHi = Unsafe.Add(ref xr, 1);
        Vector128<ulong> yLo = yr, yHi = Unsafe.Add(ref yr, 1);

        Vector128<uint> ltX = AdvSimd.Arm64.UnzipEven(
            AdvSimd.Arm64.CompareGreaterThan(mLo, xLo).AsUInt32(), AdvSimd.Arm64.CompareGreaterThan(mHi, xHi).AsUInt32());
        Vector128<uint> gtX = AdvSimd.Arm64.UnzipEven(
            AdvSimd.Arm64.CompareGreaterThan(xLo, mLo).AsUInt32(), AdvSimd.Arm64.CompareGreaterThan(xHi, mHi).AsUInt32());
        Vector128<uint> ltY = AdvSimd.Arm64.UnzipEven(
            AdvSimd.Arm64.CompareGreaterThan(mLo, yLo).AsUInt32(), AdvSimd.Arm64.CompareGreaterThan(mHi, yHi).AsUInt32());
        Vector128<uint> gtY = AdvSimd.Arm64.UnzipEven(
            AdvSimd.Arm64.CompareGreaterThan(yLo, mLo).AsUInt32(), AdvSimd.Arm64.CompareGreaterThan(yHi, mHi).AsUInt32());

        Vector128<ulong> lt = AdvSimd.Arm64.UnzipEven(ltX.AsUInt16(), ltY.AsUInt16()).AsUInt64(); // [Lx, Ly]
        Vector128<ulong> gt = AdvSimd.Arm64.UnzipEven(gtX.AsUInt16(), gtY.AsUInt16()).AsUInt64(); // [Gx, Gy]
        Vector128<ulong> both = AdvSimd.Arm64.CompareGreaterThan(lt, gt);
        return AdvSimd.Arm64.MinAcross(both.AsUInt32()).ToScalar() != 0;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void And(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        ref Vector128<ulong> ar = ref Halves(in a);
        ref Vector128<ulong> br = ref Halves(in b);
        Vector128<ulong> lo = ar & br;
        Vector128<ulong> hi = Unsafe.Add(ref ar, 1) & Unsafe.Add(ref br, 1);
        Unsafe.SkipInit(out res);
        ref Vector128<ulong> rr = ref Unsafe.As<UInt256, Vector128<ulong>>(ref res);
        rr = lo;
        Unsafe.Add(ref rr, 1) = hi;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void Xor(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        ref Vector128<ulong> ar = ref Halves(in a);
        ref Vector128<ulong> br = ref Halves(in b);
        Vector128<ulong> lo = ar ^ br;
        Vector128<ulong> hi = Unsafe.Add(ref ar, 1) ^ Unsafe.Add(ref br, 1);
        Unsafe.SkipInit(out res);
        ref Vector128<ulong> rr = ref Unsafe.As<UInt256, Vector128<ulong>>(ref res);
        rr = lo;
        Unsafe.Add(ref rr, 1) = hi;
    }
}

internal sealed class ArmAbConfig : ManualConfig
{
    public ArmAbConfig()
    {
        AddJob(Job.ShortRun.WithLaunchCount(2).WithId("PGO"));
        // EVM opcode handlers compile without PGO; see InlineCallerBench.
        AddJob(Job.ShortRun.WithLaunchCount(2).WithEnvironmentVariables(new EnvironmentVariable("DOTNET_TieredPGO", "0")).WithId("NoPGO"));
    }
}

internal static class ArmAbData
{
    public const int N = 512;

    public static void RequireArm(string name)
    {
        if (!AdvSimd.Arm64.IsSupported) throw new PlatformNotSupportedException($"{name} requires AdvSimd.Arm64.");
    }

    public static UInt256 Wide(Random rnd)
        => new((ulong)rnd.NextInt64(), (ulong)rnd.NextInt64(), (ulong)rnd.NextInt64(), (ulong)rnd.NextInt64());

    public static UInt256[] Edges { get; } =
    [
        UInt256.Zero, UInt256.One, UInt256.MaxValue, UInt256.UInt128MaxValue,
        new(0, 0, 0, 1), new(1, 0, 0, 1), new(0, 0, 1, 0), new(0, 1, 0, 0),
        new(ulong.MaxValue, 0, 0, 0), new(0, 0, 0, ulong.MaxValue), new(ulong.MaxValue, ulong.MaxValue, ulong.MaxValue, 0),
        new(0x8000_0000_0000_0000UL, 0x8000_0000_0000_0000UL, 0x8000_0000_0000_0000UL, 0x8000_0000_0000_0000UL),
        new(0x7FFF_FFFF_FFFF_FFFFUL, 0, 0x7FFF_FFFF_FFFF_FFFFUL, 0x8000_0000_0000_0000UL),
    ];

    public static void Check(bool expected, bool actual, string what)
    {
        if (expected != actual) throw new InvalidOperationException($"NEON candidate mismatch: {what}");
    }

    public static void Check(in UInt256 expected, in UInt256 actual, string what)
    {
        if (!expected.Equals(actual)) throw new InvalidOperationException($"NEON candidate mismatch: {what}");
    }
}

public enum ArmCmpCase
{
    DifferHigh,
    DifferLow,
    Equal,
    Evm,
    Mixed,
}

/// <summary>Production <c>&lt;</c> versus NEON, standalone and in a dependent select chain.</summary>
[Config(typeof(ArmAbConfig))]
public class ArmCompareAB
{
    private UInt256[] _a = [];
    private UInt256[] _b = [];

    [Params(ArmCmpCase.DifferHigh, ArmCmpCase.DifferLow, ArmCmpCase.Equal, ArmCmpCase.Evm, ArmCmpCase.Mixed)]
    public ArmCmpCase Case;

    [GlobalSetup]
    public void Setup()
    {
        ArmAbData.RequireArm(nameof(ArmCompareAB));
        Random rnd = new(42);
        _a = new UInt256[ArmAbData.N];
        _b = new UInt256[ArmAbData.N];
        for (int i = 0; i < _a.Length; i++)
        {
            ArmCmpCase c = Case == ArmCmpCase.Mixed ? (ArmCmpCase)rnd.Next(4) : Case;
            UInt256 a = ArmAbData.Wide(rnd);
            UInt256 b = c switch
            {
                ArmCmpCase.DifferHigh => new UInt256(a.u0, a.u1, a.u2, (ulong)rnd.NextInt64()),
                ArmCmpCase.DifferLow => new UInt256((ulong)rnd.NextInt64(), a.u1, a.u2, a.u3),
                ArmCmpCase.Equal => a,
                _ => default,
            };
            if (c == ArmCmpCase.Evm)
            {
                a = (ulong)rnd.NextInt64();
                b = (ulong)rnd.NextInt64();
            }
            _a[i] = a;
            _b[i] = b;
        }

        foreach (UInt256[] set in new[] { _a, _b, ArmAbData.Edges })
        foreach (UInt256 x in set)
        foreach (UInt256 y in set)
        {
            ArmAbData.Check(x < y, NeonCandidates.LessThan(in x, in y), $"{x} < {y}");
        }
    }

    [Benchmark(Baseline = true, OperationsPerInvoke = ArmAbData.N)]
    public int Lt_Scalar()
    {
        UInt256[] a = _a, b = _b;
        int acc = 0;
        for (int i = 0; i < a.Length; i++)
        {
            acc += a[i] < b[i] ? 1 : 0;
        }
        return acc;
    }

    // A/A control.
    [Benchmark(OperationsPerInvoke = ArmAbData.N)]
    public int Lt_ScalarAA()
    {
        UInt256[] a = _a, b = _b;
        int acc = 0;
        for (int i = 0; i < a.Length; i++)
        {
            acc += a[i] < b[i] ? 1 : 0;
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = ArmAbData.N)]
    public int Lt_Neon()
    {
        UInt256[] a = _a, b = _b;
        int acc = 0;
        for (int i = 0; i < a.Length; i++)
        {
            acc += NeonCandidates.LessThan(in a[i], in b[i]) ? 1 : 0;
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = ArmAbData.N)]
    public UInt256 Chain_Scalar()
    {
        UInt256[] a = _a, b = _b;
        UInt256 acc = a[0];
        for (int i = 0; i < a.Length; i++)
        {
            acc = acc < a[i] ? b[i] : a[i];
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = ArmAbData.N)]
    public UInt256 Chain_Neon()
    {
        UInt256[] a = _a, b = _b;
        UInt256 acc = a[0];
        for (int i = 0; i < a.Length; i++)
        {
            acc = NeonCandidates.LessThan(in acc, in a[i]) ? b[i] : a[i];
        }
        return acc;
    }
}

public enum ArmBothCase
{
    InRange,
    InRangeEvm,
    OutOfRange,
    Mixed,
}

/// <summary>The AddMod gate <c>x &lt; m &amp;&amp; y &lt; m</c>: production versus NEON.</summary>
[Config(typeof(ArmAbConfig))]
public class ArmLessThanBothAB
{
    private UInt256[] _x = [];
    private UInt256[] _y = [];
    private UInt256[] _m = [];

    [Params(ArmBothCase.InRange, ArmBothCase.InRangeEvm, ArmBothCase.OutOfRange, ArmBothCase.Mixed)]
    public ArmBothCase Case;

    [GlobalSetup]
    public void Setup()
    {
        ArmAbData.RequireArm(nameof(ArmLessThanBothAB));
        Random rnd = new(42);
        _x = new UInt256[ArmAbData.N];
        _y = new UInt256[ArmAbData.N];
        _m = new UInt256[ArmAbData.N];
        for (int i = 0; i < _x.Length; i++)
        {
            ArmBothCase c = Case == ArmBothCase.Mixed ? (ArmBothCase)rnd.Next(3) : Case;
            UInt256 m = ArmAbData.Wide(rnd);
            UInt256 x, y;
            switch (c)
            {
                case ArmBothCase.InRange:
                    // Equal top limb: the compare must look past limb 3.
                    x = new UInt256((ulong)rnd.NextInt64(), (ulong)rnd.NextInt64(), m.u2 >> 1, m.u3);
                    y = new UInt256((ulong)rnd.NextInt64(), (ulong)rnd.NextInt64(), (ulong)rnd.NextInt64(), m.u3 >> 1);
                    break;
                case ArmBothCase.InRangeEvm:
                    ulong small = (ulong)rnd.NextInt64() | 1;
                    m = small;
                    x = (ulong)rnd.NextInt64() % small;
                    y = (ulong)rnd.NextInt64() % small;
                    break;
                default:
                    x = ArmAbData.Wide(rnd);
                    y = new UInt256(m.u0, m.u1, m.u2, m.u3 | 1);
                    break;
            }
            if (rnd.Next(2) == 0) (x, y) = (y, x);
            _x[i] = x;
            _y[i] = y;
            _m[i] = m;
        }

        for (int i = 0; i < _x.Length; i++)
        {
            ArmAbData.Check(Production(in _x[i], in _y[i], in _m[i]), NeonCandidates.LessThanBoth(in _x[i], in _y[i], in _m[i]), $"both #{i}");
        }
        foreach (UInt256 x in ArmAbData.Edges)
        foreach (UInt256 y in ArmAbData.Edges)
        foreach (UInt256 m in ArmAbData.Edges)
        {
            ArmAbData.Check(Production(in x, in y, in m), NeonCandidates.LessThanBoth(in x, in y, in m), $"both {x} {y} {m}");
        }
    }

    // What UInt256.LessThanBoth runs on ARM64.
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static bool Production(in UInt256 x, in UInt256 y, in UInt256 m)
        => UInt256.LessThanScalar(in x, in m) && UInt256.LessThanScalar(in y, in m);

    [Benchmark(Baseline = true, OperationsPerInvoke = ArmAbData.N)]
    public int Both_Scalar()
    {
        UInt256[] x = _x, y = _y, m = _m;
        int acc = 0;
        for (int i = 0; i < x.Length; i++)
        {
            acc += Production(in x[i], in y[i], in m[i]) ? 1 : 0;
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = ArmAbData.N)]
    public int Both_ScalarAA()
    {
        UInt256[] x = _x, y = _y, m = _m;
        int acc = 0;
        for (int i = 0; i < x.Length; i++)
        {
            acc += Production(in x[i], in y[i], in m[i]) ? 1 : 0;
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = ArmAbData.N)]
    public int Both_Neon()
    {
        UInt256[] x = _x, y = _y, m = _m;
        int acc = 0;
        for (int i = 0; i < x.Length; i++)
        {
            acc += NeonCandidates.LessThanBoth(in x[i], in y[i], in m[i]) ? 1 : 0;
        }
        return acc;
    }
}

/// <summary>Production bitwise ops versus NEON, standalone and in producer/consumer chains.</summary>
[Config(typeof(ArmAbConfig))]
public class ArmBitwiseAB
{
    private UInt256[] _a = [];
    private UInt256[] _b = [];
    private UInt256[] _c = [];
    private UInt256[] _r = [];

    [GlobalSetup]
    public void Setup()
    {
        ArmAbData.RequireArm(nameof(ArmBitwiseAB));
        Random rnd = new(42);
        _a = new UInt256[ArmAbData.N];
        _b = new UInt256[ArmAbData.N];
        _c = new UInt256[ArmAbData.N];
        _r = new UInt256[ArmAbData.N];
        for (int i = 0; i < _a.Length; i++)
        {
            _a[i] = ArmAbData.Wide(rnd);
            _b[i] = ArmAbData.Wide(rnd);
            // Every fourth mask is disjoint from a, so IsZero sees both outcomes.
            _c[i] = (i & 3) == 0 ? new UInt256(~_a[i].u0, ~_a[i].u1, ~_a[i].u2, ~_a[i].u3) : ArmAbData.Wide(rnd);
        }

        foreach (UInt256[] set in new[] { _a, _c, ArmAbData.Edges })
        foreach (UInt256 x in set)
        foreach (UInt256 y in ArmAbData.Edges)
        {
            UInt256.And(in x, in y, out UInt256 andExpected);
            NeonCandidates.And(in x, in y, out UInt256 andActual);
            ArmAbData.Check(in andExpected, in andActual, $"{x} & {y}");
            UInt256.Xor(in x, in y, out UInt256 xorExpected);
            NeonCandidates.Xor(in x, in y, out UInt256 xorActual);
            ArmAbData.Check(in xorExpected, in xorActual, $"{x} ^ {y}");
        }
        // res aliasing an input.
        UInt256 alias = _a[1];
        NeonCandidates.Xor(in alias, in _b[1], out alias);
        UInt256.Xor(in _a[1], in _b[1], out UInt256 aliasExpected);
        ArmAbData.Check(in aliasExpected, in alias, "aliased xor");
    }

    [Benchmark(Baseline = true, OperationsPerInvoke = ArmAbData.N)]
    public void And_Scalar()
    {
        UInt256[] a = _a, b = _b, r = _r;
        for (int i = 0; i < a.Length; i++) UInt256.And(in a[i], in b[i], out r[i]);
    }

    [Benchmark(OperationsPerInvoke = ArmAbData.N)]
    public void And_ScalarAA()
    {
        UInt256[] a = _a, b = _b, r = _r;
        for (int i = 0; i < a.Length; i++) UInt256.And(in a[i], in b[i], out r[i]);
    }

    [Benchmark(OperationsPerInvoke = ArmAbData.N)]
    public void And_Neon()
    {
        UInt256[] a = _a, b = _b, r = _r;
        for (int i = 0; i < a.Length; i++) NeonCandidates.And(in a[i], in b[i], out r[i]);
    }

    // Worst case for NEON: Multiply's limb stores feed 16-byte loads.
    [Benchmark(OperationsPerInvoke = ArmAbData.N)]
    public void MulAnd_Scalar()
    {
        UInt256[] a = _a, b = _b, c = _c, r = _r;
        for (int i = 0; i < a.Length; i++)
        {
            UInt256.Multiply(in a[i], in b[i], out UInt256 t);
            UInt256.And(in t, in c[i], out r[i]);
        }
    }

    [Benchmark(OperationsPerInvoke = ArmAbData.N)]
    public void MulAnd_Neon()
    {
        UInt256[] a = _a, b = _b, c = _c, r = _r;
        for (int i = 0; i < a.Length; i++)
        {
            UInt256.Multiply(in a[i], in b[i], out UInt256 t);
            NeonCandidates.And(in t, in c[i], out r[i]);
        }
    }

    // Best case for NEON: 16-byte stores feed Add's 16-byte loads.
    [Benchmark(OperationsPerInvoke = ArmAbData.N)]
    public void AndAdd_Scalar()
    {
        UInt256[] a = _a, b = _b, c = _c, r = _r;
        for (int i = 0; i < a.Length; i++)
        {
            UInt256.And(in a[i], in b[i], out UInt256 t);
            UInt256.Add(in t, in c[i], out r[i]);
        }
    }

    [Benchmark(OperationsPerInvoke = ArmAbData.N)]
    public void AndAdd_Neon()
    {
        UInt256[] a = _a, b = _b, c = _c, r = _r;
        for (int i = 0; i < a.Length; i++)
        {
            NeonCandidates.And(in a[i], in b[i], out UInt256 t);
            UInt256.Add(in t, in c[i], out r[i]);
        }
    }

    // 16-byte stores read back as 8-byte limbs.
    [Benchmark(OperationsPerInvoke = ArmAbData.N)]
    public int AndIsZero_Scalar()
    {
        UInt256[] a = _a, c = _c;
        int acc = 0;
        for (int i = 0; i < a.Length; i++)
        {
            UInt256.And(in a[i], in c[i], out UInt256 t);
            acc += t.IsZero ? 1 : 0;
        }
        return acc;
    }

    [Benchmark(OperationsPerInvoke = ArmAbData.N)]
    public int AndIsZero_Neon()
    {
        UInt256[] a = _a, c = _c;
        int acc = 0;
        for (int i = 0; i < a.Length; i++)
        {
            NeonCandidates.And(in a[i], in c[i], out UInt256 t);
            acc += t.IsZero ? 1 : 0;
        }
        return acc;
    }

    // Each result feeds the next iteration through memory.
    [Benchmark(OperationsPerInvoke = ArmAbData.N - 1)]
    public void XorChain_Scalar()
    {
        UInt256[] a = _a, r = _r;
        r[0] = a[0];
        for (int i = 1; i < a.Length; i++) UInt256.Xor(in r[i - 1], in a[i], out r[i]);
    }

    [Benchmark(OperationsPerInvoke = ArmAbData.N - 1)]
    public void XorChain_Neon()
    {
        UInt256[] a = _a, r = _r;
        r[0] = a[0];
        for (int i = 1; i < a.Length; i++) NeonCandidates.Xor(in r[i - 1], in a[i], out r[i]);
    }
}
