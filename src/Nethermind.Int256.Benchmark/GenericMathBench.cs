// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System;
using System.Numerics;
using System.Runtime.CompilerServices;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Configs;

namespace Nethermind.Int256.Benchmark;

/// <summary>
/// The <see cref="INumber{TSelf}"/> path against the public operators. The interface members take 32-byte
/// operands by value and forward to the <c>in</c> operators; once inlined, each generic method should cost
/// what its direct twin does. Portable, so it is safe for the ARM benchmark CI suite
/// (<c>--filter '*GenericMath*'</c>).
/// </summary>
[WarmupCount(3)]
[IterationCount(10)]
[MemoryDiagnoser]
[GroupBenchmarksBy(BenchmarkLogicalGroupRule.ByCategory)]
[CategoriesColumn]
public class GenericMathBench
{
    private const int OperationCount = 256;

    private readonly UInt256[] _ua = new UInt256[OperationCount];
    private readonly UInt256[] _ub = new UInt256[OperationCount];
    private readonly UInt256[] _ur = new UInt256[OperationCount];
    private readonly Int256[] _sa = new Int256[OperationCount];
    private readonly Int256[] _sb = new Int256[OperationCount];
    private readonly Int256[] _sr = new Int256[OperationCount];
    private readonly bool[] _flags = new bool[OperationCount];

    [GlobalSetup]
    public void Setup()
    {
        Random random = new(0x6E_4D_42);
        Span<byte> bytes = stackalloc byte[32];
        for (int i = 0; i < OperationCount; i++)
        {
            random.NextBytes(bytes);
            UInt256 a = new(bytes);
            random.NextBytes(bytes);
            // Narrow operands half the time, as the EVM sees them; the larger first so subtraction cannot underflow.
            UInt256 b = (i & 1) == 0 ? new UInt256(bytes) : new UInt256((ulong)random.NextInt64());
            (_ua[i], _ub[i]) = a < b ? (b, a) : (a, b);
            _sa[i] = new Int256(_ua[i]);
            _sb[i] = new Int256(_ub[i]);
        }
    }

    [Benchmark(Baseline = true, OperationsPerInvoke = OperationCount), BenchmarkCategory("UInt256 +")]
    public void UInt256AddDirect() => AddDirect(_ua, _ub, _ur);

    [Benchmark(OperationsPerInvoke = OperationCount), BenchmarkCategory("UInt256 +")]
    public void UInt256AddGeneric() => Add(_ua, _ub, _ur);

    [Benchmark(Baseline = true, OperationsPerInvoke = OperationCount), BenchmarkCategory("UInt256 -")]
    public void UInt256SubtractDirect() => SubtractDirect(_ua, _ub, _ur);

    [Benchmark(OperationsPerInvoke = OperationCount), BenchmarkCategory("UInt256 -")]
    public void UInt256SubtractGeneric() => Subtract(_ua, _ub, _ur);

    [Benchmark(Baseline = true, OperationsPerInvoke = OperationCount), BenchmarkCategory("UInt256 *")]
    public void UInt256MultiplyDirect() => MultiplyDirect(_ua, _ub, _ur);

    [Benchmark(OperationsPerInvoke = OperationCount), BenchmarkCategory("UInt256 *")]
    public void UInt256MultiplyGeneric() => Multiply(_ua, _ub, _ur);

    [Benchmark(Baseline = true, OperationsPerInvoke = OperationCount), BenchmarkCategory("UInt256 /")]
    public void UInt256DivideDirect() => DivideDirect(_ua, _ub, _ur);

    [Benchmark(OperationsPerInvoke = OperationCount), BenchmarkCategory("UInt256 /")]
    public void UInt256DivideGeneric() => Divide(_ua, _ub, _ur);

    [Benchmark(Baseline = true, OperationsPerInvoke = OperationCount), BenchmarkCategory("UInt256 <")]
    public void UInt256LessThanDirect() => LessThanDirect(_ub, _ua, _flags);

    [Benchmark(OperationsPerInvoke = OperationCount), BenchmarkCategory("UInt256 <")]
    public void UInt256LessThanGeneric() => LessThan(_ub, _ua, _flags);

    [Benchmark(Baseline = true, OperationsPerInvoke = OperationCount), BenchmarkCategory("Int256 +")]
    public void Int256AddDirect() => AddDirect(_sa, _sb, _sr);

    [Benchmark(OperationsPerInvoke = OperationCount), BenchmarkCategory("Int256 +")]
    public void Int256AddGeneric() => Add(_sa, _sb, _sr);

    [Benchmark(Baseline = true, OperationsPerInvoke = OperationCount), BenchmarkCategory("Int256 *")]
    public void Int256MultiplyDirect() => MultiplyDirect(_sa, _sb, _sr);

    [Benchmark(OperationsPerInvoke = OperationCount), BenchmarkCategory("Int256 *")]
    public void Int256MultiplyGeneric() => Multiply(_sa, _sb, _sr);

    [Benchmark(Baseline = true, OperationsPerInvoke = OperationCount), BenchmarkCategory("Int256 <")]
    public void Int256LessThanDirect() => LessThanDirect(_sb, _sa, _flags);

    [Benchmark(OperationsPerInvoke = OperationCount), BenchmarkCategory("Int256 <")]
    public void Int256LessThanGeneric() => LessThan(_sb, _sa, _flags);

    // Direct twins of the generic loops below: same shape, binding to the public `in` operators.

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void AddDirect(UInt256[] a, UInt256[] b, UInt256[] r)
    {
        for (int i = 0; i < OperationCount; i++) r[i] = a[i] + b[i];
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void AddDirect(Int256[] a, Int256[] b, Int256[] r)
    {
        for (int i = 0; i < OperationCount; i++) r[i] = a[i] + b[i];
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void SubtractDirect(UInt256[] a, UInt256[] b, UInt256[] r)
    {
        for (int i = 0; i < OperationCount; i++) r[i] = a[i] - b[i];
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void MultiplyDirect(UInt256[] a, UInt256[] b, UInt256[] r)
    {
        for (int i = 0; i < OperationCount; i++) r[i] = a[i] * b[i];
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void MultiplyDirect(Int256[] a, Int256[] b, Int256[] r)
    {
        for (int i = 0; i < OperationCount; i++) r[i] = a[i] * b[i];
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void DivideDirect(UInt256[] a, UInt256[] b, UInt256[] r)
    {
        for (int i = 0; i < OperationCount; i++) r[i] = a[i] / b[i];
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void LessThanDirect(UInt256[] a, UInt256[] b, bool[] r)
    {
        for (int i = 0; i < OperationCount; i++) r[i] = a[i] < b[i];
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void LessThanDirect(Int256[] a, Int256[] b, bool[] r)
    {
        for (int i = 0; i < OperationCount; i++) r[i] = a[i] < b[i];
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void Add<T>(T[] a, T[] b, T[] r) where T : INumber<T>
    {
        for (int i = 0; i < OperationCount; i++) r[i] = a[i] + b[i];
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void Subtract<T>(T[] a, T[] b, T[] r) where T : INumber<T>
    {
        for (int i = 0; i < OperationCount; i++) r[i] = a[i] - b[i];
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void Multiply<T>(T[] a, T[] b, T[] r) where T : INumber<T>
    {
        for (int i = 0; i < OperationCount; i++) r[i] = a[i] * b[i];
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void Divide<T>(T[] a, T[] b, T[] r) where T : INumber<T>
    {
        for (int i = 0; i < OperationCount; i++) r[i] = a[i] / b[i];
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static void LessThan<T>(T[] a, T[] b, bool[] r) where T : INumber<T>
    {
        for (int i = 0; i < OperationCount; i++) r[i] = a[i] < b[i];
    }
}
