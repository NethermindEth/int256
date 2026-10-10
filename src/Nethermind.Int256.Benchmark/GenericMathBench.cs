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
    public void UInt256AddDirect()
    {
        for (int i = 0; i < OperationCount; i++) _ur[i] = _ua[i] + _ub[i];
    }

    [Benchmark(OperationsPerInvoke = OperationCount), BenchmarkCategory("UInt256 +")]
    public void UInt256AddGeneric() => Add(_ua, _ub, _ur);

    [Benchmark(Baseline = true, OperationsPerInvoke = OperationCount), BenchmarkCategory("UInt256 -")]
    public void UInt256SubtractDirect()
    {
        for (int i = 0; i < OperationCount; i++) _ur[i] = _ua[i] - _ub[i];
    }

    [Benchmark(OperationsPerInvoke = OperationCount), BenchmarkCategory("UInt256 -")]
    public void UInt256SubtractGeneric() => Subtract(_ua, _ub, _ur);

    [Benchmark(Baseline = true, OperationsPerInvoke = OperationCount), BenchmarkCategory("UInt256 *")]
    public void UInt256MultiplyDirect()
    {
        for (int i = 0; i < OperationCount; i++) _ur[i] = _ua[i] * _ub[i];
    }

    [Benchmark(OperationsPerInvoke = OperationCount), BenchmarkCategory("UInt256 *")]
    public void UInt256MultiplyGeneric() => Multiply(_ua, _ub, _ur);

    [Benchmark(Baseline = true, OperationsPerInvoke = OperationCount), BenchmarkCategory("UInt256 /")]
    public void UInt256DivideDirect()
    {
        for (int i = 0; i < OperationCount; i++) _ur[i] = _ua[i] / _ub[i];
    }

    [Benchmark(OperationsPerInvoke = OperationCount), BenchmarkCategory("UInt256 /")]
    public void UInt256DivideGeneric() => Divide(_ua, _ub, _ur);

    [Benchmark(Baseline = true, OperationsPerInvoke = OperationCount), BenchmarkCategory("UInt256 <")]
    public void UInt256LessThanDirect()
    {
        for (int i = 0; i < OperationCount; i++) _flags[i] = _ub[i] < _ua[i];
    }

    [Benchmark(OperationsPerInvoke = OperationCount), BenchmarkCategory("UInt256 <")]
    public void UInt256LessThanGeneric() => LessThan(_ub, _ua, _flags);

    [Benchmark(Baseline = true, OperationsPerInvoke = OperationCount), BenchmarkCategory("Int256 +")]
    public void Int256AddDirect()
    {
        for (int i = 0; i < OperationCount; i++) _sr[i] = _sa[i] + _sb[i];
    }

    [Benchmark(OperationsPerInvoke = OperationCount), BenchmarkCategory("Int256 +")]
    public void Int256AddGeneric() => Add(_sa, _sb, _sr);

    [Benchmark(Baseline = true, OperationsPerInvoke = OperationCount), BenchmarkCategory("Int256 *")]
    public void Int256MultiplyDirect()
    {
        for (int i = 0; i < OperationCount; i++) _sr[i] = _sa[i] * _sb[i];
    }

    [Benchmark(OperationsPerInvoke = OperationCount), BenchmarkCategory("Int256 *")]
    public void Int256MultiplyGeneric() => Multiply(_sa, _sb, _sr);

    [Benchmark(Baseline = true, OperationsPerInvoke = OperationCount), BenchmarkCategory("Int256 <")]
    public void Int256LessThanDirect()
    {
        for (int i = 0; i < OperationCount; i++) _flags[i] = _sb[i] < _sa[i];
    }

    [Benchmark(OperationsPerInvoke = OperationCount), BenchmarkCategory("Int256 <")]
    public void Int256LessThanGeneric() => LessThan(_sb, _sa, _flags);

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
